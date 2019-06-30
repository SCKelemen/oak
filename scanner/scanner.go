package scanner

import (
	"github.com/SCKelemen/oak/token"

	"github.com/SCKelemen/oak/util"
)

// Scanner is the lexer
type Scanner struct {
	input   string
	head    int
	read    int
	current rune
}

func New(input string) *Scanner {
	s := &Scanner{input: input}

	s.readChar()
	return s
}

// readChar 's only responsibility is to progress
// the read-ahead head, check for EOF, and then
// update head to read-ahead head
func (s *Scanner) readChar() {
	// if the look-ahead pointer reaches
	// the end of the input stream,
	// set the current character to NUL/0
	// indicating EOF
	if s.read >= len(s.input) {
		s.current = 0
	} else {
		// else, set the current character
		// under inspection to be the char
		// at the look-ahead position
		s.current = rune(s.input[s.read])
	}

	// then we can set the head to the
	// read-ahead head
	s.head = s.read
	// and then increment the read-ahead head
	s.read++
}

// NextToken emits the next token. Handles single
//char tokens internally, directly
func (s *Scanner) NextToken() token.Token {
	var tok token.Token
	s.skipWhitespace()

	switch s.current {
	/*
		LBRACK // [
		RBRACK // ]
		LBRACE // {
		RBRACE // }
		LPAREN // (
		RPAREN // )
		LCHEV  // <
		RCHEV  // >

		COMMA // ,
		DOT   // .
		COLON // :
		SEMI  // ;

		EQL // =
	*/

	// handle brackety things
	case '[':
		tok = newToken(token.LBRACK, s.current)
	case ']':
		tok = newToken(token.RBRACK, s.current)
	case '{':
		tok = newToken(token.LBRACE, s.current)
	case '}':
		tok = newToken(token.RBRACE, s.current)
	case '(':
		tok = newToken(token.LPAREN, s.current)
	case ')':
		tok = newToken(token.RPAREN, s.current)
	case '<':
		tok = newToken(token.LCHEV, s.current)
	case '>':
		tok = newToken(token.RCHEV, s.current)

	// handle punctionationy things
	case ',':
		tok = newToken(token.COMMA, s.current)
	case '.':
		tok = newToken(token.DOT, s.current)
	case ':':
		tok = newToken(token.COLON, s.current)
	case ';':
		tok = newToken(token.SEMI, s.current)

	// handle arithmeticy things
	case '=':
		tok = newToken(token.EQL, s.current)

	// handle the nul/eof char
	case 0:
		tok.Literal = ""
		tok.TokenKind = token.EOF

	default:
		tok = newToken(token.ILLEGAL, s.current)
	}
	s.readChar()
	return tok
}

// skipWhitespace 's only responsibility is to
// read while the current token under inspection
// remains a whitespace character. These don't have
// syntactic or semantic meaning to the language.
func (s *Scanner) skipWhitespace() {
	for util.IsWhitespace(s.current) {
		s.readChar()
	}
}

func newToken(kind token.TokenKind, ch rune) token.Token {
	return token.Token{TokenKind: kind, Literal: string(ch)}
}
