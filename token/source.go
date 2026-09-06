package token

// Source is the minimal streaming contract between lexical and syntactic
// compiler stages. Scanner and layout normalization both implement Source.
//
// Keeping this contract in token avoids coupling the parser to a concrete
// scanner implementation and lets token transforms compose without knowing
// about one another.
type Source interface {
	NextToken() Token
}
