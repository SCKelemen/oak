package token

type TokenKind int

type Token struct {
	TokenKind
	Literal string
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

	TYPE:   "type",
	SWITCH: "switch",
}

var keywords map[string]TokenKind

func init() {
	keywords = make(map[string]TokenKind)
	for i := _keywords_beg + 1; i < _keywords_end; i++ {
		keywords[tokens[i]] = i
	}
}
