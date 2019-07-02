package ast

import (
	"bytes"
	"strings"

	"github.com/SCKelemen/oak/token"
)

type Node interface {
	TokenLiteral() string
	String() string
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

func (p *Program) String() string {
	var out bytes.Buffer

	for _, s := range p.Statements {
		out.WriteString(s.String())
	}
	return out.String()
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
func (tds *TypeDeclarationStatement) String() string {
	var out bytes.Buffer

	out.WriteString(tds.TokenLiteral())
	out.WriteRune(' ')
	out.WriteString(tds.Name.String())
	out.WriteString(" = ")

	if tds.Value != nil {
		out.WriteString(tds.Value.String())
	}
	out.WriteRune(';')

	return out.String()
}

type Identifier struct {
	Token token.Token // 'ident' token
	Value string
}

func (i *Identifier) expressionNode()      {}
func (i *Identifier) TokenLiteral() string { return i.Token.Literal }
func (i *Identifier) String() string       { return i.Value }

type ReturnStatement struct {
	Token       token.Token // 'return' token
	ReturnValue Expression
}

func (rs *ReturnStatement) statementNode()       {}
func (rs *ReturnStatement) TokenLiteral() string { return rs.Token.Literal }
func (rs *ReturnStatement) String() string {
	var out bytes.Buffer

	out.WriteString(rs.TokenLiteral())
	out.WriteRune(' ')

	if rs.ReturnValue != nil {
		out.WriteString(rs.ReturnValue.String())
	}

	out.WriteRune(';')

	return out.String()
}

// ExpressionStatement is required for
// side-effecting code such as
// counter++;
type ExpressionStatement struct {
	Token      token.Token // the first token of the expression
	Expression Expression
}

func (es *ExpressionStatement) statementNode()       {}
func (es *ExpressionStatement) TokenLiteral() string { return es.Token.Literal }
func (es *ExpressionStatement) String() string {
	if es.Expression != nil {
		return es.Expression.String()
	}
	return ""
}

type IntegerLiteral struct {
	Token token.Token
	Value int64
}

func (lit *IntegerLiteral) expressionNode()      {}
func (lit *IntegerLiteral) TokenLiteral() string { return lit.Token.Literal }
func (lit *IntegerLiteral) String() string       { return lit.Token.Literal }

type PrefixExpression struct {
	Token    token.Token // prefix tokens: !, -, *
	Operator string
	Right    Expression
}

func (pe *PrefixExpression) expressionNode()      {}
func (pe *PrefixExpression) TokenLiteral() string { return pe.Token.Literal }
func (pe *PrefixExpression) String() string {
	var out bytes.Buffer

	out.WriteRune('(')
	out.WriteString(pe.Operator)
	out.WriteString(pe.Right.String())
	out.WriteRune(')')

	return out.String()
}

type InfixExpression struct {
	Token    token.Token // the operator token: +, -, *, /, etc...
	Left     Expression
	Operator string
	Right    Expression
}

func (ie InfixExpression) expressionNode()      {}
func (ie InfixExpression) TokenLiteral() string { return ie.Token.Literal }
func (ie InfixExpression) String() string {
	var out bytes.Buffer

	out.WriteRune('(')
	out.WriteString(ie.Left.String())
	out.WriteRune(' ')
	out.WriteString(ie.Operator)
	out.WriteRune(' ')
	out.WriteString(ie.Right.String())
	out.WriteRune(')')

	return out.String()
}

type Boolean struct {
	Token token.Token // true | false                   or maybe ;)
	Value bool
}

func (b *Boolean) expressionNode()      {}
func (b *Boolean) TokenLiteral() string { return b.Token.Literal }
func (b *Boolean) String() string       { return b.Token.Literal }

type IfExpression struct {
	Token       token.Token // if token
	Condition   Expression
	Consequence *BlockStatement
	Alternative *BlockStatement
}

func (ie *IfExpression) expressionNode()      {}
func (ie *IfExpression) TokenLiteral() string { return ie.Token.Literal }
func (ie *IfExpression) String() string {
	var out bytes.Buffer

	out.WriteString("if")
	out.WriteString(ie.Condition.String())
	out.WriteRune(' ')
	out.WriteString(ie.Consequence.String())

	if ie.Alternative != nil {
		out.WriteString("else ")
		out.WriteString(ie.Alternative.String())
	}

	return out.String()
}

type BlockStatement struct {
	Token      token.Token // { token
	Statements []Statement
}

func (bs *BlockStatement) statementNode()       {}
func (bs *BlockStatement) TokenLiteral() string { return bs.Token.Literal }
func (bs *BlockStatement) String() string {
	var out bytes.Buffer

	for _, s := range bs.Statements {
		out.WriteString(s.String())
	}

	return out.String()
}

type FunctionLiteral struct {
	Token     token.Token // func
	Arguments []*Identifier
	Body      *BlockStatement
}

func (fl *FunctionLiteral) expressionNode()      {}
func (fl *FunctionLiteral) TokenLiteral() string { return fl.Token.Literal }
func (fl *FunctionLiteral) String() string {
	var out bytes.Buffer

	args := []string{}
	for _, arg := range fl.Arguments {
		args = append(args, arg.String())
	}

	out.WriteString(fl.TokenLiteral())
	out.WriteRune('(')
	out.WriteString(strings.Join(args, ", "))
	out.WriteRune(')')
	out.WriteString(fl.Body.String())

	return out.String()
}

type InvocationExpression struct {
	Token     token.Token // ( token
	Function  Expression  // Identifier || FunctionLiteral
	Arguments []Expression
}

func (ie InvocationExpression) expressionNode()      {}
func (ie InvocationExpression) TokenLiteral() string { return ie.Token.Literal }
func (ie InvocationExpression) String() string {
	var out bytes.Buffer

	args := []string{}
	for _, arg := range ie.Arguments {
		args = append(args, arg.String())
	}

	out.WriteString(ie.Function.String())
	out.WriteRune('(')
	out.WriteString(strings.Join(args, ", "))
	out.WriteRune(')')

	return out.String()

}
