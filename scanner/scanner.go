package scanner

import (
	"bytes"
	"strconv"
	"unicode/utf16"
	"unicode/utf8"

	"github.com/SCKelemen/oak/source"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/util"
)

// Scanner is the Oak lexer.
type Scanner struct {
	file    *source.File
	input   string
	head    int // Current byte position (start of current token)
	read    int // Look-ahead byte position
	current rune
	width   int
	line    int // Current line number (1-based)
	column  int // Current UTF-16 column number (1-based)
	nextLn  int
	nextCol int
}

func New(input string) *Scanner {
	return NewFile(source.NewFile(0, "", input))
}

// NewFile constructs a scanner that preserves source identity for diagnostics,
// editor links, and later compiler projections.
func NewFile(file *source.File) *Scanner {
	if file == nil {
		file = source.NewFile(0, "", "")
	}
	s := &Scanner{
		file:    file,
		input:   file.Text,
		nextLn:  1,
		nextCol: 1,
	}

	s.readChar()
	return s
}

// SourceFile implements token.LocatedSource.
func (s *Scanner) SourceFile() *source.File { return s.file }

// readChar advances by one UTF-8 rune and updates token position fields.
// Columns use UTF-16 code units so scanner positions map exactly to LSP/VS Code.
func (s *Scanner) readChar() {
	if s.read >= len(s.input) {
		s.head = s.read
		s.current = 0
		s.width = 0
		s.line = s.nextLn
		s.column = s.nextCol
		return
	}

	s.head = s.read
	s.line = s.nextLn
	s.column = s.nextCol

	// Invalid UTF-8 decodes to U+FFFD and the scanner keeps progressing.
	// This is tolerated only because ingestion is the authoritative gate:
	// Compilation.Parse rejects any source that fails source.ValidateUTF8
	// before the scanner runs (docs/spec/70-strings.md section 8), so
	// invalid bytes here can occur only for partial buffers (e.g. editors).
	r, w := utf8.DecodeRuneInString(s.input[s.read:])
	s.current = r
	s.width = w
	s.read += w

	if r == '\n' {
		s.nextLn++
		s.nextCol = 1
	} else {
		units := utf16.RuneLen(r)
		if units < 1 {
			units = 1
		}
		s.nextCol += units
	}
}

// NextToken emits the next token from the rune stream.
// Returns TRIVIA tokens for whitespace and other non-syntactic content.
func (s *Scanner) NextToken() token.Token {
	var tok token.Token

	// Check for whitespace/trivia before the next token
	if util.IsWhitespace(s.current) {
		return s.readTrivia()
	}

	// Save current position (this is where the token starts)
	line := s.line
	column := s.column
	byteStart := s.head

	switch s.current {
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
	case ')':
		tok = newTokenWithPos(token.RPAREN, s.current, line, column)
	case '<':
		if s.peekRune() == '=' {
			ch := s.current
			s.readChar()
			tok = token.Token{TokenKind: token.LEQ, Literal: string(ch) + string(s.current), Line: line, Column: column}
		} else if s.peekRune() == '<' {
			ch := s.current
			s.readChar()
			tok = token.Token{TokenKind: token.SHL, Literal: string(ch) + string(s.current), Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.LCHEV, s.current, line, column)
		}
	case '>':
		if s.peekRune() == '=' {
			ch := s.current
			s.readChar()
			tok = token.Token{TokenKind: token.GEQ, Literal: string(ch) + string(s.current), Line: line, Column: column}
		} else if s.peekRune() == '>' {
			ch := s.current
			s.readChar()
			tok = token.Token{TokenKind: token.SHR, Literal: string(ch) + string(s.current), Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.RCHEV, s.current, line, column)
		}

	case ',':
		tok = newTokenWithPos(token.COMMA, s.current, line, column)
	case '.':
		if s.peekRune() == '.' {
			s.readChar() // second dot
			if s.peekRune() == '.' {
				s.readChar() // third dot
				tok = token.Token{TokenKind: token.ELLIPSIS, Literal: "...", Line: line, Column: column}
			} else {
				// Two dots have no meaning; fail closed rather than split.
				tok = token.Token{TokenKind: token.ILLEGAL, Literal: "..", Line: line, Column: column}
			}
		} else {
			tok = newTokenWithPos(token.DOT, s.current, line, column)
		}
	case ':':
		if s.peekRune() == '=' {
			ch := s.current
			s.readChar()
			literal := string(ch) + string(s.current)
			tok = token.Token{TokenKind: token.COLON_ASSIGN, Literal: literal, Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.COLON, s.current, line, column)
		}
	case ';':
		tok = newTokenWithPos(token.SEMI, s.current, line, column)

	case '=':
		peek := s.peekRune()
		if peek == '>' {
			ch := s.current
			s.readChar()
			literal := string(ch) + string(s.current)
			tok = token.Token{TokenKind: token.FAT_ARROW, Literal: literal, Line: line, Column: column}
		} else if peek == '=' {
			ch := s.current
			s.readChar()
			literal := string(ch) + string(s.current)
			tok = token.Token{TokenKind: token.EQL, Literal: literal, Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.ASSIGN, s.current, line, column)
		}
	case '|':
		if s.peekRune() == '>' {
			ch := s.current
			s.readChar()
			tok = token.Token{TokenKind: token.PIPE_FORWARD, Literal: string(ch) + string(s.current), Line: line, Column: column}
		} else if s.peekRune() == '|' {
			ch := s.current
			s.readChar()
			tok = token.Token{TokenKind: token.LOR, Literal: string(ch) + string(s.current), Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.PIPE, s.current, line, column)
		}
	case '%':
		tok = newTokenWithPos(token.REM, s.current, line, column)
	case '^':
		tok = newTokenWithPos(token.CARET, s.current, line, column)
	case '&':
		if s.peekRune() == '&' {
			ch := s.current
			s.readChar()
			tok = token.Token{TokenKind: token.LAND, Literal: string(ch) + string(s.current), Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.AMP, s.current, line, column)
		}
	case '!':
		if s.peekRune() == '=' {
			ch := s.current
			s.readChar()
			literal := string(ch) + string(s.current)
			tok = token.Token{TokenKind: token.NEQL, Literal: literal, Line: line, Column: column}
		} else {
			tok = newTokenWithPos(token.BANG, s.current, line, column)
		}
	case '-':
		if s.peekRune() == '>' {
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
		if s.peekRune() == '/' {
			return s.readLineComment()
		}
		if s.peekRune() == '*' {
			return s.readBlockComment()
		}
		tok = newTokenWithPos(token.QUO, s.current, line, column)
	case '?':
		tok = newTokenWithPos(token.QMARK, s.current, line, column)
	case '"':
		literal, valid := s.readString()
		tok.Literal = literal
		tok.TokenKind = token.STRING
		if !valid {
			tok.TokenKind = token.ILLEGAL
			tok.Literal = "invalid escape sequence in string literal (docs/spec/10-syntax.md section 2a: \\n \\t \\r \\0 \\\\ \\\" \\xHH)"
		}
		tok.Line = line
		tok.Column = column
		return s.finishToken(tok, byteStart)

	case 0:
		tok.Literal = ""
		tok.TokenKind = token.EOF
		tok.Line = line
		tok.Column = column
		return s.finishToken(tok, byteStart)

	default:
		if util.IsLetter(s.current) {
			tok.Literal = s.readWord()
			tok.TokenKind = token.Lookup(tok.Literal)
			tok.Line = line
			tok.Column = column
			return s.finishToken(tok, byteStart)
		} else if util.IsDigit(s.current) {
			tok.Literal = s.readNumber()
			tok.TokenKind = token.INT
			tok.Line = line
			tok.Column = column
			return s.finishToken(tok, byteStart)
		} else {
			tok = newTokenWithPos(token.ILLEGAL, s.current, line, column)
		}
	}
	s.readChar()
	return s.finishToken(tok, byteStart)
}

func (s *Scanner) finishToken(tok token.Token, byteStart int) token.Token {
	tok.ByteStart = byteStart
	tok.ByteEnd = s.head
	tok.EndLine = s.line
	tok.EndColumn = s.column
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

	return s.finishToken(token.Token{
		TokenKind: token.TRIVIA,
		Literal:   trivia.String(),
		Line:      line,
		Column:    column,
	}, byteStart)
}

func newToken(kind token.TokenKind, ch rune) token.Token {
	return token.Token{TokenKind: kind, Literal: string(ch)}
}

func newTokenWithPos(kind token.TokenKind, ch rune, line, column int) token.Token {
	return token.Token{TokenKind: kind, Literal: string(ch), Line: line, Column: column}
}

func (s *Scanner) readWord() string {
	position := s.head
	for util.IsIdentifierChar(s.current) {
		s.readChar()
	}
	return s.input[position:s.head]
}

func (s *Scanner) readNumber() string {
	position := s.head

	// 0x/0b sugar for the radix form: 0xFF reads as 16rFF, 0b1010 as
	// 2r1010 (docs/spec/10-syntax.md). The canonical radix spelling stays.
	if s.current == '0' && (s.peekRune() == 'x' || s.peekRune() == 'X' || s.peekRune() == 'b' || s.peekRune() == 'B') {
		radix := "16"
		if s.peekRune() == 'b' || s.peekRune() == 'B' {
			radix = "2"
		}
		s.readChar() // past 0
		s.readChar() // past x/b
		digitsStart := s.head
		for s.isRadixTailChar(s.current) {
			s.readChar()
		}
		digits := stripUnderscores(s.input[digitsStart:s.head])
		if len(digits) == 0 {
			return s.input[position:s.head]
		}
		return radix + "r" + digits
	}

	for util.IsDigit(s.current) {
		s.readChar()
	}

	if s.current == 'r' || s.current == 'R' {
		radixStr := util.NormalizeDigits(s.input[position:s.head])
		radix, err := strconv.Atoi(radixStr)
		if err == nil && radix >= 2 && radix <= 16 {
			s.readChar()
			for s.isRadixTailChar(s.current) {
				s.readChar()
			}
			return util.NormalizeDigits(s.input[position:s.head])
		}
		return stripUnderscores(s.input[position:s.head])
	}

	for util.IsNumericChar(s.current) {
		s.readChar()
	}
	return stripUnderscores(s.input[position:s.head])
}

func stripUnderscores(s string) string {
	result := make([]rune, 0, len(s))
	for _, ch := range s {
		if ch != '_' {
			if d, ok := util.DigitValue(ch); ok {
				result = append(result, rune('0'+d))
			} else {
				result = append(result, ch)
			}
		}
	}
	return string(result)
}

func (s *Scanner) isRadixTailChar(ch rune) bool {
	if ch == '_' || util.IsDigit(ch) {
		return true
	}
	return ('A' <= ch && ch <= 'Z') || ('a' <= ch && ch <= 'z')
}

// readString scans the body of a string literal and returns its decoded
// bytes. The escape sequences of docs/spec/10-syntax.md section 2a are
// processed here, once, so every later phase (the evaluator, `text_literal`,
// the C backend's own re-escaping) sees the bytes the program means:
//
//	\n \t \r \0 \\ \"    the usual C set
//	\xHH                 one byte, two hex digits
//
// Any other character after a backslash is an invalid escape: the literal is
// still consumed to its closing quote so the token span stays right, and
// ok is false so the caller reports the token as ILLEGAL.
func (s *Scanner) readString() (literal string, ok bool) {
	var out bytes.Buffer
	ok = true
scan:
	for {
		s.readChar()
		switch s.current {
		case '"', 0:
			break scan
		case '\\':
			s.readChar()
			switch s.current {
			case 'n':
				out.WriteByte('\n')
			case 't':
				out.WriteByte('\t')
			case 'r':
				out.WriteByte('\r')
			case '0':
				out.WriteByte(0)
			case '\\':
				out.WriteByte('\\')
			case '"':
				out.WriteByte('"')
			case 'x':
				value := 0
				for digits := 0; digits < 2; digits++ {
					s.readChar()
					d, isHex := hexDigitValue(s.current)
					if !isHex {
						ok = false
						if s.current == '"' || s.current == 0 {
							break scan
						}
						continue scan
					}
					value = value*16 + d
				}
				out.WriteByte(byte(value))
			case 0:
				// A backslash at end of input: unterminated literal.
				ok = false
				break scan
			default:
				ok = false
			}
		default:
			out.WriteRune(s.current)
		}
	}
	if s.current == '"' {
		s.readChar()
	}
	return out.String(), ok
}

// hexDigitValue decodes one hexadecimal digit.
func hexDigitValue(ch rune) (int, bool) {
	switch {
	case '0' <= ch && ch <= '9':
		return int(ch - '0'), true
	case 'a' <= ch && ch <= 'f':
		return int(ch-'a') + 10, true
	case 'A' <= ch && ch <= 'F':
		return int(ch-'A') + 10, true
	}
	return 0, false
}

func (s *Scanner) peekRune() rune {
	if s.read >= len(s.input) {
		return 0
	}
	r, _ := utf8.DecodeRuneInString(s.input[s.read:])
	return r
}

func (s *Scanner) readLineComment() token.Token {
	line := s.line
	column := s.column
	byteStart := s.head

	s.readChar()
	s.readChar()

	var comment bytes.Buffer
	for s.current != '\n' && s.current != 0 {
		comment.WriteRune(s.current)
		s.readChar()
	}

	return s.finishToken(token.Token{
		TokenKind: token.COMMENT,
		Literal:   comment.String(),
		Line:      line,
		Column:    column,
	}, byteStart)
}

func (s *Scanner) readBlockComment() token.Token {
	line := s.line
	column := s.column
	byteStart := s.head

	s.readChar()
	s.readChar()

	var comment bytes.Buffer
	for {
		if s.current == 0 {
			return s.finishToken(token.Token{
				TokenKind: token.ILLEGAL,
				Literal:   "unterminated block comment",
				Line:      line,
				Column:    column,
			}, byteStart)
		}
		if s.current == '*' && s.peekRune() == '/' {
			s.readChar()
			s.readChar()
			break
		}
		comment.WriteRune(s.current)
		s.readChar()
	}

	return s.finishToken(token.Token{
		TokenKind: token.COMMENT,
		Literal:   comment.String(),
		Line:      line,
		Column:    column,
	}, byteStart)
}
