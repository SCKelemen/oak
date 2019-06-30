package token

import "strconv"

type TokenKind int

type Token struct {
	TokenKind TokenKind
	Literal   string
}

const (
	ILLEGAL TokenKind = iota
	EOF
	TRIVIA
	COMMENT

	IDENT

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

	PIPE // |
	AMP  // &

	_keywords_beg
	TYPE
	SWITCH
	_keywords_end
)

var tokens = [...]string{
	ILLEGAL: "ILLEGAL",
	EOF:     "EOF",
	TRIVIA:  "TRIVIA",
	COMMENT: "COMMENT",

	IDENT: "IDENTITY",

	LBRACK: "[",
	RBRACK: "]",
	LBRACE: "{",
	RBRACE: "}",
	LPAREN: "(",
	RPAREN: ")",
	LCHEV:  "<",
	RCHEV:  ">",

	COMMA: ",",
	DOT:   ".",
	COLON: ":",
	SEMI:  ";",

	EQL: "=",

	PIPE: "|",
	AMP:  "&",

	TYPE:   "type",
	SWITCH: "switch",
}

func (token TokenKind) String() string {
	s := ""
	if 0 <= token && token < TokenKind(len(tokens)) {
		s = tokens[token]
	}
	if s == "" {
		s = "token(" + strconv.Itoa(int(token)) + ")"
	}
	return s
}

var keywords map[string]TokenKind

func init() {
	keywords = make(map[string]TokenKind)
	for i := _keywords_beg + 1; i < _keywords_end; i++ {
		keywords[tokens[i]] = i
	}
}

func Lookup(candidate string) TokenKind {
	if tok, isKeyword := keywords[candidate]; isKeyword {
		return tok
	}
	return IDENT
}
