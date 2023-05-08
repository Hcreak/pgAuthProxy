package proxy

import (
	"encoding/binary"
	"errors"
	"github.com/KnifeMaster007/pgAuthProxy/auth"
	"github.com/KnifeMaster007/pgAuthProxy/utils"
	"github.com/jackc/pgproto3/v2"
	log "github.com/sirupsen/logrus"
	"io"
	"net"
	"strings"
	"time"
	// "encoding/json"
	"fmt"
	"bytes"
	"crypto/hmac"
	"crypto/rand"
	"crypto/sha256"
	"encoding/base64"
	"strconv"
	"golang.org/x/crypto/pbkdf2"
	"golang.org/x/text/secure/precis"
)

type ProxyBack struct {
	TargetProps map[string]string
	TargetHost  string

	originProps      map[string]string
	backendConn      net.Conn
	proto            *pgproto3.Frontend
	protoChunkReader pgproto3.ChunkReader
}

const MaxTcpPayload = 65535

var (
	MissingRequiredTargetFields = errors.New("required target fields missing in target props")
	BackendAuthenticationError  = errors.New("backend authentication failed")
	BackendInvalidMessage       = errors.New("unexpected message received from backend")
)

func NewProxyBackend(targetProps map[string]string, originProps map[string]string) (*ProxyBack, error) {
	b := &ProxyBack{
		originProps: originProps,
		TargetProps: make(map[string]string),
	}
	if host, ok := targetProps[utils.TargetHostParameter]; ok {
		b.TargetHost = host
	} else {
		return nil, MissingRequiredTargetFields
	}
	for k, v := range targetProps {
		if !strings.HasPrefix(k, utils.MetaPrefix) {
			b.TargetProps[k] = v
		}
	}
	err := b.initiateBackendConnection(targetProps[utils.TargetCredentialParameter])
	if err != nil {
		return nil, err
	}
	return b, nil
}

func (b *ProxyBack) initiateBackendConnection(credential string) error {
	conn, err := net.Dial("tcp", b.TargetHost)
	if err != nil {
		return err
	}
	b.backendConn = conn
	b.protoChunkReader = pgproto3.NewChunkReader(conn)
	b.proto = pgproto3.NewFrontend(b.protoChunkReader, conn)
	err = b.proto.Send(&pgproto3.StartupMessage{
		ProtocolVersion: pgproto3.ProtocolVersionNumber,
		Parameters:      b.TargetProps,
	})
	if err != nil {
		conn.Close()
		return err
	}
	sc := &scramClient{}
	for {
		msg, err := b.proto.Receive()
		if err != nil {
			conn.Close()
			return err
		}
		switch msg.(type) {
		case *pgproto3.AuthenticationMD5Password:
			salt := msg.(*pgproto3.AuthenticationMD5Password).Salt
			err = b.proto.Send(&pgproto3.PasswordMessage{Password: auth.SaltedMd5Credential(credential, salt)})
			if err != nil {
				conn.Close()
				return err
			}
			continue
		case *pgproto3.AuthenticationOk:
			return nil
		case *pgproto3.ErrorResponse:
			return BackendAuthenticationError
		case *pgproto3.AuthenticationSASL:
			sc, err = newScramClient(msg.(*pgproto3.AuthenticationSASL).AuthMechanisms, credential)
			if err != nil {
				conn.Close()
				return err
			}
			// Send client-first-message in a SASLInitialResponse
			err = b.proto.Send(&pgproto3.SASLInitialResponse{AuthMechanism: "SCRAM-SHA-256", Data: sc.clientFirstMessage()})
			if err != nil {
				conn.Close()
				return err
			}
			continue
		case *pgproto3.AuthenticationSASLContinue:
			// Receive server-first-message payload in a AuthenticationSASLContinue.
			err = sc.recvServerFirstMessage(msg.(*pgproto3.AuthenticationSASLContinue).Data)
			if err != nil {
				conn.Close()
				return err
			}
			// Send client-final-message in a SASLResponse
			err = b.proto.Send(&pgproto3.SASLResponse{Data: []byte(sc.clientFinalMessage())})
			if err != nil {
				conn.Close()
				return err
			}
			continue
		case *pgproto3.AuthenticationSASLFinal:
			continue
		default:
			conn.Close()
			return BackendInvalidMessage
		}
	}
}

type scramClient struct {
	serverAuthMechanisms []string
	password             []byte
	clientNonce          []byte

	clientFirstMessageBare []byte

	serverFirstMessage   []byte
	clientAndServerNonce []byte
	salt                 []byte
	iterations           int

	saltedPassword []byte
	authMessage    []byte
}

const clientNonceLen = 18

func newScramClient(serverAuthMechanisms []string, password string) (*scramClient, error) {
	sc := &scramClient{
		serverAuthMechanisms: serverAuthMechanisms,
	}

	// Ensure server supports SCRAM-SHA-256
	hasScramSHA256 := false
	for _, mech := range sc.serverAuthMechanisms {
		if mech == "SCRAM-SHA-256" {
			hasScramSHA256 = true
			break
		}
	}
	if !hasScramSHA256 {
		return nil, errors.New("server does not support SCRAM-SHA-256")
	}

	// precis.OpaqueString is equivalent to SASLprep for password.
	var err error
	sc.password, err = precis.OpaqueString.Bytes([]byte(password))
	if err != nil {
		// PostgreSQL allows passwords invalid according to SCRAM / SASLprep.
		sc.password = []byte(password)
	}

	buf := make([]byte, clientNonceLen)
	_, err = rand.Read(buf)
	if err != nil {
		return nil, err
	}
	sc.clientNonce = make([]byte, base64.RawStdEncoding.EncodedLen(len(buf)))
	base64.RawStdEncoding.Encode(sc.clientNonce, buf)

	return sc, nil
}

func (sc *scramClient) clientFirstMessage() []byte {
	sc.clientFirstMessageBare = []byte(fmt.Sprintf("n=,r=%s", sc.clientNonce))
	return []byte(fmt.Sprintf("n,,%s", sc.clientFirstMessageBare))
}

func (sc *scramClient) recvServerFirstMessage(serverFirstMessage []byte) error {
	sc.serverFirstMessage = serverFirstMessage
	buf := serverFirstMessage
	if !bytes.HasPrefix(buf, []byte("r=")) {
		return errors.New("invalid SCRAM server-first-message received from server: did not include r=")
	}
	buf = buf[2:]

	idx := bytes.IndexByte(buf, ',')
	if idx == -1 {
		return errors.New("invalid SCRAM server-first-message received from server: did not include s=")
	}
	sc.clientAndServerNonce = buf[:idx]
	buf = buf[idx+1:]

	if !bytes.HasPrefix(buf, []byte("s=")) {
		return errors.New("invalid SCRAM server-first-message received from server: did not include s=")
	}
	buf = buf[2:]

	idx = bytes.IndexByte(buf, ',')
	if idx == -1 {
		return errors.New("invalid SCRAM server-first-message received from server: did not include i=")
	}
	saltStr := buf[:idx]
	buf = buf[idx+1:]

	if !bytes.HasPrefix(buf, []byte("i=")) {
		return errors.New("invalid SCRAM server-first-message received from server: did not include i=")
	}
	buf = buf[2:]
	iterationsStr := buf

	var err error
	sc.salt, err = base64.StdEncoding.DecodeString(string(saltStr))
	if err != nil {
		return fmt.Errorf("invalid SCRAM salt received from server: %w", err)
	}

	sc.iterations, err = strconv.Atoi(string(iterationsStr))
	if err != nil || sc.iterations <= 0 {
		return fmt.Errorf("invalid SCRAM iteration count received from server: %w", err)
	}

	if !bytes.HasPrefix(sc.clientAndServerNonce, sc.clientNonce) {
		return errors.New("invalid SCRAM nonce: did not start with client nonce")
	}

	if len(sc.clientAndServerNonce) <= len(sc.clientNonce) {
		return errors.New("invalid SCRAM nonce: did not include server nonce")
	}

	return nil
}

func (sc *scramClient) clientFinalMessage() string {
	clientFinalMessageWithoutProof := []byte(fmt.Sprintf("c=biws,r=%s", sc.clientAndServerNonce))

	sc.saltedPassword = pbkdf2.Key([]byte(sc.password), sc.salt, sc.iterations, 32, sha256.New)
	sc.authMessage = bytes.Join([][]byte{sc.clientFirstMessageBare, sc.serverFirstMessage, clientFinalMessageWithoutProof}, []byte(","))

	clientProof := computeClientProof(sc.saltedPassword, sc.authMessage)

	return fmt.Sprintf("%s,p=%s", clientFinalMessageWithoutProof, clientProof)
}

func computeHMAC(key, msg []byte) []byte {
	mac := hmac.New(sha256.New, key)
	mac.Write(msg)
	return mac.Sum(nil)
}

func computeClientProof(saltedPassword, authMessage []byte) []byte {
	clientKey := computeHMAC(saltedPassword, []byte("Client Key"))
	storedKey := sha256.Sum256(clientKey)
	clientSignature := computeHMAC(storedKey[:], authMessage)

	clientProof := make([]byte, len(clientSignature))
	for i := 0; i < len(clientSignature); i++ {
		clientProof[i] = clientKey[i] ^ clientSignature[i]
	}

	buf := make([]byte, base64.StdEncoding.EncodedLen(len(clientProof)))
	base64.StdEncoding.Encode(buf, clientProof)
	return buf
}


func pipeBackendPgMessages(source pgproto3.ChunkReader, dest io.Writer) error {
	bw := utils.NewBufferedWriter(MaxTcpPayload, dest, 300*time.Millisecond)
	defer bw.Close()
	startupComplete := false

	for {
		header, err := source.Next(5)
		if err != nil {
			return err
		}
		l := int(binary.BigEndian.Uint32(header[1:])) - 4
		body, _ := source.Next(l)
		_, err = bw.Write(append(header, body...))
		if err != nil {
			return err
		}
		switch header[0] {
		case 'S':
			if !startupComplete {
				break
			}
			fallthrough
		case 'A', 'N', 'Z':
			if header[0] == 'Z' {
				startupComplete = true
			}
			_, err = bw.Flush()
			if err != nil {
				return err
			}
		}
	}
}

func pipePgMessages(source pgproto3.ChunkReader, dest io.Writer) error {
	for {
		header, err := source.Next(5)
		if err != nil {
			return err
		}
		l := int(binary.BigEndian.Uint32(header[1:])) - 4
		body, _ := source.Next(l)
		_, err = dest.Write(append(header, body...))
		if err != nil {
			return err
		}
	}
}

func (b *ProxyBack) Run(frontConn net.Conn, frontChunkReader pgproto3.ChunkReader) error {
	defer b.Close()
	err := make(chan error)
	go func() {
		log.Debug("bootstrapped backend -> frontend message pipe")
		err <- pipeBackendPgMessages(b.protoChunkReader, frontConn)
	}()
	go func() {
		log.Debug("bootstrapped backend <- frontend message pipe")
		err <- pipePgMessages(frontChunkReader, b.backendConn)
	}()
	select {
	case e := <-err:
		return e
	}
}

func (b *ProxyBack) Close() {
	if b.backendConn != nil {
		b.backendConn.Close()
	}
}
