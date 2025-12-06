package scanner

import (
	"bytes"

	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/util"
)

// Scanner is the lexer
type Scanner struct {
	input   string
	head    int // Current byte position (start of current token)
	read    int // Look-ahead byte position
	current rune
	line    int // Current line number (1-based)
	column  int // Current column number (1-based)
}

func New(input string) *Scanner {
	s := &Scanner{
		input:  input,
		line:   1,
		column: 1,
	}

	s.readChar()
	return s
}

// readChar 's only responsibility is to progress
// the read-ahead head, check for EOF, and then
// update head to read-ahead head
func (s *Scanner) readChar() {
	// Track line/column before advancing
	if s.read < len(s.input) {
		if s.input[s.read] == '\n' {
			s.line++
			s.column = 0 // Will be incremented to 1 below
		}
	}

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

	// Increment column after reading (1-based)
	if s.current != '\n' && s.current != 0 {
		s.column++
	} else if s.current == '\n' {
		s.column = 1
	}
}

// NextToken emits the next token. Handles single
// char tokens internally, directly
// Returns TRIVIA tokens for whitespace and other non-syntactic content
func (s *Scanner) NextToken() token.Token {
	var tok token.Token

	// Check for whitespace/trivia before the next token
	if util.IsWhitespace(s.current) {
		return s.readTrivia()
	}

	// Save current position (this is where the token starts)
	line := s.line
	column := s.column
	byteStart := s.head // Byte offset where token starts

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
		tok = newTokenWithPos(token.LBRACK, s.current, line, column)
	case ']':
		tok = newTokenWithPos(token.RBRACK, s.current, line, column)
	case '{':
		tok = newTokenWithPos(token.LBRACE, s.current, line, column)
	case '}':
		tok = newTokenWithPos(token.RBRACE, s.current, line, column)
	case '(':
		tok = newTokenWithPos(token.LPAREN, s.current, line, column)
		// Don't call readChar() here - it will be called at line 218
	case ')':
		tok = newTokenWithPos(token.RPAREN, s.current, line, column)
		// Don't call readChar() here - it will be called at line 218
	case '<':
		tok = newTokenWithPos(token.LCHEV, s.current, line, column)
	case '>':
		tok = newTokenWithPos(token.RCHEV, s.current, line, column)

	// handle punctionationy things
	case ',':
		tok = newTokenWithPos(token.COMMA, s.current, line, column)
	case '.':
		tok = newTokenWithPos(token.DOT, s.current, line, column)
	case ':':
		if s.peekChar() == '=' {
			ch := s.current
			s.readChar()
			literal := string(ch) + string(s.current)
			tok = token.Token{TokenKind: token.COLON_ASSIGN, Literal: literal, Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.COLON, s.current, line, column)
		}
	case ';':
		tok = newTokenWithPos(token.SEMI, s.current, line, column)

	// handle arithmeticy things
	case '=':
		if s.peekChar() == '=' {
			ch := s.current
			s.readChar()
			literal := string(ch) + string(s.current)
			tok = token.Token{TokenKind: token.EQL, Literal: literal, Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.ASSIGN, s.current, line, column)
		}
	// handle bitwise/type like things
	case '|':
		tok = newTokenWithPos(token.PIPE, s.current, line, column)
	case '&':
		tok = newTokenWithPos(token.AMP, s.current, line, column)

	case '!':
		if s.peekChar() == '=' {
			ch := s.current
			s.readChar()
			literal := string(ch) + string(s.current)
			tok = token.Token{TokenKind: token.NEQL, Literal: literal, Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.BANG, s.current, line, column)
		}
	case '-':
		if s.peekChar() == '>' {
			ch := s.current
			s.readChar()
			literal := string(ch) + string(s.current)
			tok = token.Token{TokenKind: token.ARROW, Literal: literal, Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.NEG, s.current, line, column)
		}
	case '+':
		tok = newTokenWithPos(token.SUM, s.current, line, column)
	case '*':
		tok = newTokenWithPos(token.MUL, s.current, line, column)
	case '/':
		// Check for line comment: //
		if s.peekChar() == '/' {
			return s.readLineComment()
		}
		// Check for block comment: /*
		if s.peekChar() == '*' {
			return s.readBlockComment()
		}
		// Regular division operator
		tok = newTokenWithPos(token.QUO, s.current, line, column)
	case '?':
		tok = newTokenWithPos(token.QMARK, s.current, line, column)
	case '"':
		// String literal - readString advances head, so we need to capture before
		tok.Literal = s.readString()
		tok.TokenKind = token.STRING
		tok.Line = line
		tok.Column = column
		tok.ByteStart = byteStart
		tok.ByteEnd = s.head // readString already advanced head
		return tok

	// handle the nul/eof char
	case 0:
		tok.Literal = ""
		tok.TokenKind = token.EOF
		tok.Line = line
		tok.Column = column
		tok.ByteStart = byteStart
		tok.ByteEnd = s.head
		return tok

	default:
		if util.IsLetter(s.current) {
			// Word - readWord advances head, so we need to capture before
			tok.Literal = s.readWord()
			tok.TokenKind = token.Lookup(tok.Literal)
			tok.Line = line
			tok.Column = column
			tok.ByteStart = byteStart
			tok.ByteEnd = s.head // readWord already advanced head
			return tok
		} else if util.IsDigit(s.current) {
			// Number - readNumber advances head, so we need to capture before
			tok.Literal = s.readNumber()
			tok.TokenKind = token.INT
			tok.Line = line
			tok.Column = column
			tok.ByteStart = byteStart
			tok.ByteEnd = s.head // readNumber already advanced head
			return tok
		} else {
			tok = newTokenWithPos(token.ILLEGAL, s.current, line, column)
		}
	}
	s.readChar()

	// Set end position (current head is where token ends)
	tok.ByteStart = byteStart
	tok.ByteEnd = s.head

	return tok
}

// readTrivia reads whitespace and other non-syntactic content
// and returns it as a TRIVIA token. This allows exact source reconstruction.
func (s *Scanner) readTrivia() token.Token {
	line := s.line
	column := s.column
	byteStart := s.head

	var trivia bytes.Buffer
	for util.IsWhitespace(s.current) {
		trivia.WriteRune(s.current)
		s.readChar()
	}

	return token.Token{
		TokenKind: token.TRIVIA,
		Literal:   trivia.String(),
		Line:      line,
		Column:    column,
		ByteStart: byteStart,
		ByteEnd:   s.head,
	}
}

func newToken(kind token.TokenKind, ch rune) token.Token {
	return token.Token{TokenKind: kind, Literal: string(ch)}
}

func newTokenWithPos(kind token.TokenKind, ch rune, line, column int) token.Token {
	// Note: ByteStart and ByteEnd will be set in NextToken after reading
	return token.Token{TokenKind: kind, Literal: string(ch), Line: line, Column: column}
}

// read until the next space
func (s *Scanner) readWord() string {
	position := s.head
	for util.IsIdentifierChar(s.current) {
		s.readChar()
	}
	// After the loop, s.current is the first non-identifier character
	// s.read points to the character after that
	// We DON'T back up s.read - we leave s.current pointing to the next character to process
	// This allows NextToken() to process that character in the next call
	return s.input[position:s.head]
}

func (s *Scanner) readNumber() string {
	position := s.head
	for util.IsDigit(s.current) {
		s.readChar()
	}
	// After the loop, s.current is the first non-digit character
	// s.read points to the character after that
	// We DON'T back up s.read - we leave s.current pointing to the next character to process
	// This allows NextToken() to process that character in the next call
	return s.input[position:s.head]
}

func (s *Scanner) readString() string {
	position := s.head + 1 // skip opening quote
	for {
		s.readChar()
		if s.current == '"' || s.current == 0 {
			break
		}
	}
	if s.current == '"' {
		// consume closing quote
		s.readChar()
	}
	return s.input[position : s.head-1] // exclude quotes
}

func (s *Scanner) peekChar() byte {
	if s.read >= len(s.input) {
		return 0
	} else {
		return s.input[s.read]
	}
}

// readLineComment reads a line comment (// ...) and returns it as a COMMENT token
func (s *Scanner) readLineComment() token.Token {
	line := s.line
	column := s.column
	byteStart := s.head

	// Consume both slashes
	s.readChar() // consume first /
	s.readChar() // consume second /

	// Read until end of line or EOF
	var comment bytes.Buffer
	for s.current != '\n' && s.current != 0 {
		comment.WriteRune(s.current)
		s.readChar()
	}

	return token.Token{
		TokenKind: token.COMMENT,
		Literal:   comment.String(),
		Line:      line,
		Column:    column,
		ByteStart: byteStart,
		ByteEnd:   s.head,
	}
}

// readBlockComment reads a block comment (/* ... */) and returns it as a COMMENT token
// Returns ILLEGAL token if the comment is unterminated (EOF before */)
func (s *Scanner) readBlockComment() token.Token {
	line := s.line
	column := s.column
	byteStart := s.head

	// Consume /*
	s.readChar() // consume /
	s.readChar() // consume *

	// Read until */
	var comment bytes.Buffer
	for {
		if s.current == 0 {
			// EOF reached before closing */ - this is an error
			return token.Token{
				TokenKind: token.ILLEGAL,
				Literal:   "unterminated block comment",
				Line:      line,
				Column:    column,
				ByteStart: byteStart,
				ByteEnd:   s.head,
			}
		}
		if s.current == '*' && s.peekChar() == '/' {
			// Found closing */
			s.readChar() // consume *
			s.readChar() // consume /
			break
		}
		comment.WriteRune(s.current)
		s.readChar()
	}

	return token.Token{
		TokenKind: token.COMMENT,
		Literal:   comment.String(),
		Line:      line,
		Column:    column,
		ByteStart: byteStart,
		ByteEnd:   s.head,
	}
}
