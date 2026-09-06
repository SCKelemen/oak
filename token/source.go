package token

import "github.com/SCKelemen/oak/source"

// Source is the minimal streaming contract between lexical and syntactic
// compiler stages. Scanner and layout normalization both implement Source.
//
// Keeping this contract in token avoids coupling the parser to a concrete
// scanner implementation and lets token transforms compose without knowing
// about one another.
type Source interface {
	NextToken() Token
}

// LocatedSource is implemented by token streams that preserve the source file
// they originated from. Parser code may use this optional contract for
// diagnostics/editor links without coupling syntax to scanner implementation.
type LocatedSource interface {
	Source
	SourceFile() *source.File
}
