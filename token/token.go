package token

import "strconv"

type TokenKind int

type Token struct {
	TokenKind TokenKind
	Literal   string
	Line      int  // 1-based line number
	Column    int  // 1-based UTF-16 column (VS Code/LSP compatible + 1)
	EndLine   int  // 1-based line immediately after the token
	EndColumn int  // 1-based UTF-16 column immediately after the token
	ByteStart int  // UTF-8 byte offset where token starts
	ByteEnd   int  // UTF-8 byte offset where token ends (exclusive)
	Synthetic bool // true when introduced by normalization rather than source text
}

const (
	ILLEGAL TokenKind = iota
	EOF
	TRIVIA
	COMMENT

	IDENT
	INT    // for natural numbers
	STRING // string literals

	LBRACK // [
	RBRACK // ]
	LBRACE // {
	RBRACE // }
	LPAREN // (
	RPAREN // )
	LCHEV  // <
	LEQ    // <=
	GEQ    // >=
	RCHEV  // >

	COMMA // ,
	DOT      // .
	ELLIPSIS // ...
	COLON // :
	SEMI  // ;

	ASSIGN       // =
	COLON_ASSIGN // :=
	ARROW        // ->
	FAT_ARROW    // =>

	PIPE  // |
	AMP   // &
	BANG  // !
	QMARK // ?

	// arithmeticy bits
	NEG // -
	SUM // +
	MUL // *
	QUO // /

	EQL  // ==
	NEQL // !=

	LAND // && (short-circuit logical and)
	LOR  // || (short-circuit logical or)

	_keywords_beg
	TYPE
	INTERFACE
	STRUCT
	TRUE
	FALSE
	PACKAGE
	IMPORT
	WHILE
	UNSAFE
	FN
	IF
	ELSE
	_keywords_end
)

var tokens = [...]string{
	ILLEGAL: "ILLEGAL",
	EOF:     "EOF",
	TRIVIA:  "TRIVIA",
	COMMENT: "COMMENT",

	IDENT:  "IDENTITY",
	INT:    "INT",
	STRING: "STRING",

	LBRACK: "[",
	RBRACK: "]",
	LBRACE: "{",
	RBRACE: "}",
	LPAREN: "(",
	RPAREN: ")",
	LCHEV:  "<",
	LEQ:    "<=",
	GEQ:    ">=",
	RCHEV:  ">",

	COMMA: ",",
	DOT:      ".",
	ELLIPSIS: "...",
	COLON: ":",
	SEMI:  ";",

	ASSIGN:       "=",
	COLON_ASSIGN: ":=",
	ARROW:        "->",
	FAT_ARROW:    "=>",

	PIPE:  "|",
	AMP:   "&",
	BANG:  "!",
	QMARK: "?",

	NEG: "-",
	SUM: "+",
	MUL: "*",
	QUO: "/",

	EQL:  "==",
	NEQL: "!=",

	LAND: "&&",
	LOR:  "||",

	TYPE:      "type",
	INTERFACE: "interface",
	STRUCT:    "struct",
	TRUE:      "true",
	FALSE:     "false",
	PACKAGE:   "package",
	IMPORT:    "import",
	WHILE:     "while",
	UNSAFE:    "unsafe",
	FN:        "fn",
	IF:        "if",
	ELSE:      "else",
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
