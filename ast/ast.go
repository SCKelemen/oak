package ast

import "github.com/SCKelemen/oak/token"

type Node interface {
	TokenLiteral() string
}

type Statement interface {
	Node
	statementNode()
}

type Expression interface {
	Node
	expressionNode()
}

type Program struct {
	Statements []Statement
}

func (p *Program) TokenLiteral() string {
	if len(p.Statements) > 0 {
		return p.Statements[0].TokenLiteral()
	} else {
		return ""
	}
}

type TypeDeclarationStatement struct {
	Token token.Token // 'type' token
	Name  *Identifier
	Value Expression
}

func (tds *TypeDeclarationStatement) statementNode()       {}
func (tds *TypeDeclarationStatement) TokenLiteral() string { return tds.Token.Literal }

type Identifier struct {
	Token token.Token // 'ident' token
	Value string
}

func (i *Identifier) expressionNode()      {}
func (i *Identifier) TokenLiteral() string { return i.Token.Literal }
