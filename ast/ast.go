package ast

import (
	"bytes"
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/token"
)

// BaseNode provides default implementations for trivia methods
// AST nodes can embed this to get default behavior
type BaseNode struct {
	leadingTrivia_  []token.Token
	trailingTrivia_ []token.Token
}

func (b *BaseNode) LeadingTrivia() []token.Token           { return b.leadingTrivia_ }
func (b *BaseNode) TrailingTrivia() []token.Token          { return b.trailingTrivia_ }
func (b *BaseNode) SetLeadingTrivia(trivia []token.Token)  { b.leadingTrivia_ = trivia }
func (b *BaseNode) SetTrailingTrivia(trivia []token.Token) { b.trailingTrivia_ = trivia }

type Node interface {
	TokenLiteral() string
	String() string
	// LeadingTrivia returns trivia tokens that appear before this node
	LeadingTrivia() []token.Token
	// TrailingTrivia returns trivia tokens that appear after this node
	TrailingTrivia() []token.Token
	// SetLeadingTrivia sets the leading trivia tokens
	SetLeadingTrivia([]token.Token)
	// SetTrailingTrivia sets the trailing trivia tokens
	SetTrailingTrivia([]token.Token)
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
	// Trivia tokens that appear before the first statement (e.g., leading whitespace)
	LeadingTriviaTokens []token.Token
	// Trivia tokens that appear after the last statement (e.g., trailing whitespace)
	TrailingTriviaTokens []token.Token
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

func (p *Program) LeadingTrivia() []token.Token {
	return p.LeadingTriviaTokens
}

func (p *Program) TrailingTrivia() []token.Token {
	return p.TrailingTriviaTokens
}

func (p *Program) SetLeadingTrivia(trivia []token.Token) {
	p.LeadingTriviaTokens = trivia
}

func (p *Program) SetTrailingTrivia(trivia []token.Token) {
	p.TrailingTriviaTokens = trivia
}

type Identifier struct {
	BaseNode
	Token token.Token // 'ident' token
	Value string
}

func (i *Identifier) expressionNode()      {}
func (i *Identifier) TokenLiteral() string { return i.Token.Literal }
func (i *Identifier) String() string       { return i.Value }

// ExpressionStatement is required for
// side-effecting code such as
// counter++;
type ExpressionStatement struct {
	BaseNode
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
	BaseNode
	Token token.Token
	Value int64
}

func (lit *IntegerLiteral) expressionNode()      {}
func (lit *IntegerLiteral) TokenLiteral() string { return lit.Token.Literal }
func (lit *IntegerLiteral) String() string       { return lit.Token.Literal }

type StringLiteral struct {
	BaseNode
	Token token.Token
	Value string
}

func (lit *StringLiteral) expressionNode()      {}
func (lit *StringLiteral) TokenLiteral() string { return lit.Token.Literal }
func (lit *StringLiteral) String() string       { return lit.Token.Literal }

// RecordLiteral: { field1: value1, field2: value2, ... }
type RecordLiteral struct {
	BaseNode
	Token    token.Token // { token or struct token
	EndToken token.Token // } token (for end position)
	Fields   map[string]Expression
	TypeName *Identifier // optional type name for type-qualified literals: TypeName{ ... }
}

func (rl *RecordLiteral) expressionNode()      {}
func (rl *RecordLiteral) TokenLiteral() string { return rl.Token.Literal }
func (rl *RecordLiteral) String() string {
	var out bytes.Buffer
	out.WriteRune('{')

	first := true
	for field, expr := range rl.Fields {
		if !first {
			out.WriteString(", ")
		}
		out.WriteString(field)
		out.WriteString(": ")
		out.WriteString(expr.String())
		first = false
	}

	out.WriteRune('}')
	return out.String()
}

type PrefixExpression struct {
	BaseNode
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
	BaseNode
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

// IndexExpression: record.field or array[index]
type IndexExpression struct {
	BaseNode
	Token token.Token // The . token or [ token
	Left  Expression
	Index Expression // For records, this is an identifier. For arrays, this is an integer expression.
}

func (ie *IndexExpression) expressionNode()      {}
func (ie *IndexExpression) TokenLiteral() string { return ie.Token.Literal }
func (ie *IndexExpression) String() string {
	var out bytes.Buffer
	out.WriteRune('(')
	out.WriteString(ie.Left.String())
	if ident, ok := ie.Index.(*Identifier); ok {
		// Record field access
		out.WriteRune('.')
		out.WriteString(ident.Value)
	} else {
		// Array indexing
		out.WriteRune('[')
		out.WriteString(ie.Index.String())
		out.WriteRune(']')
	}
	out.WriteRune(')')
	return out.String()
}

// SliceExpression: array[low:high] or array[low:] or array[:high] or array[:]
// Supports Python-style negative indices
// Step field reserved for future [low:high:step] syntax
type SliceExpression struct {
	BaseNode
	Token token.Token // The [ token
	Seq   Expression  // The array/view/span being sliced
	Low   Expression  // Low bound (nil means 0, i.e., expr[:high])
	High  Expression  // High bound (nil means len, i.e., expr[low:] or expr[:])
	// Step Expression // Reserved for future [i:j:k] syntax
}

func (se *SliceExpression) expressionNode()      {}
func (se *SliceExpression) TokenLiteral() string { return se.Token.Literal }
func (se *SliceExpression) String() string {
	var out bytes.Buffer
	out.WriteRune('(')
	out.WriteString(se.Seq.String())
	out.WriteRune('[')
	if se.Low != nil {
		out.WriteString(se.Low.String())
	}
	out.WriteRune(':')
	if se.High != nil {
		out.WriteString(se.High.String())
	}
	out.WriteRune(']')
	out.WriteRune(')')
	return out.String()
}

// ArrayLiteral: [expr1, expr2, ...] or [N]Type{ expr1, expr2, ... }
type ArrayLiteral struct {
	BaseNode
	Token    token.Token // The [ token
	Elements []Expression
	Type     Expression // Optional: array type for typed literals like [4]u8{ ... }
}

func (al *ArrayLiteral) expressionNode()      {}
func (al *ArrayLiteral) TokenLiteral() string { return al.Token.Literal }
func (al *ArrayLiteral) String() string {
	var out bytes.Buffer
	out.WriteRune('[')
	for i, elem := range al.Elements {
		if i > 0 {
			out.WriteString(", ")
		}
		out.WriteString(elem.String())
	}
	out.WriteRune(']')
	return out.String()
}

type Boolean struct {
	BaseNode
	Token token.Token // true | false                   or maybe ;)
	Value bool
}

func (b *Boolean) expressionNode()      {}
func (b *Boolean) TokenLiteral() string { return b.Token.Literal }
func (b *Boolean) String() string       { return b.Token.Literal }

type BlockStatement struct {
	BaseNode
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
	BaseNode
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
	BaseNode
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

// Variable declaration: a: type = value or a: type
type VariableDeclaration struct {
	BaseNode
	Token token.Token
	Name  *Identifier
	Type  Expression // optional type annotation
	Value Expression // optional initial value
}

func (vd *VariableDeclaration) statementNode()       {}
func (vd *VariableDeclaration) TokenLiteral() string { return vd.Token.Literal }
func (vd *VariableDeclaration) String() string {
	var out bytes.Buffer
	out.WriteString(vd.Name.String())
	if vd.Type != nil {
		out.WriteString(": ")
		out.WriteString(vd.Type.String())
	}
	if vd.Value != nil {
		out.WriteString(" = ")
		out.WriteString(vd.Value.String())
	}
	return out.String()
}

// Assignment statement: a = b
type AssignmentStatement struct {
	BaseNode
	Token token.Token
	Name  *Identifier
	Value Expression
}

func (as *AssignmentStatement) statementNode()       {}
func (as *AssignmentStatement) TokenLiteral() string { return as.Token.Literal }
func (as *AssignmentStatement) String() string {
	var out bytes.Buffer
	out.WriteString(as.Name.String())
	out.WriteString(" = ")
	out.WriteString(as.Value.String())
	return out.String()
}

// Pattern matching expression
type MatchExpression struct {
	BaseNode
	Token     token.Token // '?' token
	Scrutinee Expression
	Arms      []*MatchArm
}

// Variant expression: .Ok or Status::Ok
type VariantExpression struct {
	BaseNode
	Token    token.Token
	TypeName *Identifier // optional, for Status::Ok
	Variant  *Identifier // .Ok or Ok
	Payload  Expression  // optional, for .Some(value)
}

func (ve *VariantExpression) expressionNode()      {}
func (ve *VariantExpression) TokenLiteral() string { return ve.Token.Literal }
func (ve *VariantExpression) String() string {
	var out bytes.Buffer
	if ve.TypeName != nil {
		out.WriteString(ve.TypeName.String())
		out.WriteString("::")
	}
	out.WriteString(".")
	out.WriteString(ve.Variant.String())
	if ve.Payload != nil {
		out.WriteRune('(')
		out.WriteString(ve.Payload.String())
		out.WriteRune(')')
	}
	return out.String()
}

func (me *MatchExpression) expressionNode()      {}
func (me *MatchExpression) TokenLiteral() string { return me.Token.Literal }
func (me *MatchExpression) String() string {
	var out bytes.Buffer

	out.WriteString(me.Scrutinee.String())
	out.WriteString(" ? ")
	for i, arm := range me.Arms {
		if i > 0 {
			out.WriteString(" | ")
		}
		out.WriteString(arm.String())
	}

	return out.String()
}

// Pattern matching arm
type MatchArm struct {
	Token   token.Token // '|' or first token
	Pattern Pattern
	Body    Expression
}

func (ma *MatchArm) String() string {
	var out bytes.Buffer
	out.WriteString(ma.Pattern.String())
	out.WriteString(" -> ")
	out.WriteString(ma.Body.String())
	return out.String()
}

// Pattern interface
type Pattern interface {
	Node
	patternNode()
}

// Wildcard pattern
type WildcardPattern struct {
	BaseNode
	Token token.Token // '_'
}

func (wp *WildcardPattern) patternNode()         {}
func (wp *WildcardPattern) TokenLiteral() string { return wp.Token.Literal }
func (wp *WildcardPattern) String() string       { return "_" }

// Binding pattern
type BindingPattern struct {
	BaseNode
	Token token.Token
	Name  *Identifier
}

func (bp *BindingPattern) patternNode()         {}
func (bp *BindingPattern) TokenLiteral() string { return bp.Token.Literal }
func (bp *BindingPattern) String() string       { return bp.Name.String() }

// Literal pattern
type LiteralPattern struct {
	BaseNode
	Token token.Token
	Value Expression // IntegerLiteral, StringLiteral, etc.
}

func (lp *LiteralPattern) patternNode()         {}
func (lp *LiteralPattern) TokenLiteral() string { return lp.Token.Literal }
func (lp *LiteralPattern) String() string       { return lp.Value.String() }

// Variant pattern
type VariantPattern struct {
	BaseNode
	Token   token.Token
	Variant *Identifier // .Ok, .Some, etc.
	Payload Pattern     // optional, for .Some(x)
}

func (vp *VariantPattern) patternNode()         {}
func (vp *VariantPattern) TokenLiteral() string { return vp.Token.Literal }
func (vp *VariantPattern) String() string {
	var out bytes.Buffer
	out.WriteString(".")
	out.WriteString(vp.Variant.String())
	if vp.Payload != nil {
		out.WriteRune('(')
		out.WriteString(vp.Payload.String())
		out.WriteRune(')')
	}
	return out.String()
}

// Interface type definition
// Example: Reader: interface = fn (self) read(...) -> ...
type InterfaceType struct {
	BaseNode
	Token      token.Token // 'interface' token
	EndToken   token.Token // Last token of the interface definition
	Name       *Identifier
	TypeParams []*TypeParameter   // Optional type parameters: [T, Tag]
	Methods    []*InterfaceMethod // Method signatures
}

// InterfaceMethod represents a method signature in an interface
type InterfaceMethod struct {
	BaseNode
	Token        token.Token
	Name         *Identifier
	ReceiverType Expression // Optional receiver type: (self: *T) or (self)
	Parameters   []*FunctionParameter
	ReturnType   Expression
}

func (im *InterfaceMethod) statementNode()       {}
func (im *InterfaceMethod) TokenLiteral() string { return im.Token.Literal }
func (im *InterfaceMethod) String() string {
	var out bytes.Buffer
	out.WriteString("fn(")
	if im.ReceiverType != nil {
		out.WriteString(im.ReceiverType.String())
	}
	out.WriteString(") ")
	out.WriteString(im.Name.String())
	out.WriteString("(")
	for i, param := range im.Parameters {
		if i > 0 {
			out.WriteString(", ")
		}
		out.WriteString(param.String())
	}
	out.WriteString(") -> ")
	out.WriteString(im.ReturnType.String())
	return out.String()
}

func (it *InterfaceType) statementNode()       {}
func (it *InterfaceType) TokenLiteral() string { return it.Token.Literal }
func (it *InterfaceType) String() string {
	var out bytes.Buffer
	out.WriteString(it.Name.String())
	if len(it.TypeParams) > 0 {
		out.WriteString("[")
		for i, tp := range it.TypeParams {
			if i > 0 {
				out.WriteString(", ")
			}
			out.WriteString(tp.String())
		}
		out.WriteString("]")
	}
	out.WriteString(": interface =")
	if len(it.Methods) > 0 {
		for i, method := range it.Methods {
			if i > 0 {
				out.WriteString("\n  ")
			} else {
				out.WriteString(" ")
			}
			out.WriteString(method.String())
		}
	}
	return out.String()
}

// ADT type definition
type ADTType struct {
	BaseNode
	Token      token.Token // 'type' token
	EndToken   token.Token // Last token of the ADT definition (for end position)
	Name       *Identifier
	TypeParams []*TypeParameter // Optional type parameters: [T: Ordered]
	Variants   []*ADTVariant
}

func (adt *ADTType) statementNode()       {}
func (adt *ADTType) TokenLiteral() string { return adt.Token.Literal }
func (adt *ADTType) String() string {
	var out bytes.Buffer
	out.WriteString(adt.Name.String())
	out.WriteString(": type")
	for i, v := range adt.Variants {
		if i == 0 {
			out.WriteString(" = ")
		} else {
			out.WriteString(" | ")
		}
		out.WriteString(v.String())
	}
	return out.String()
}

// ADT variant
type ADTVariant struct {
	Token   token.Token
	Name    *Identifier
	Payload Expression // optional type parameter, e.g. Some(T)
	Literal Expression // optional literal tag, e.g. Ok: 200
}

func (v *ADTVariant) String() string {
	var out bytes.Buffer
	out.WriteString(v.Name.String())
	if v.Payload != nil {
		out.WriteRune('(')
		out.WriteString(v.Payload.String())
		out.WriteRune(')')
	}
	if v.Literal != nil {
		out.WriteString(": ")
		out.WriteString(v.Literal.String())
	}
	return out.String()
}

// Package declaration
type PackageStatement struct {
	BaseNode
	Token token.Token // 'package' token
	Name  *Identifier
}

func (ps *PackageStatement) statementNode()       {}
func (ps *PackageStatement) TokenLiteral() string { return ps.Token.Literal }
func (ps *PackageStatement) String() string {
	return "package " + ps.Name.String()
}

// Import statement
type ImportStatement struct {
	BaseNode
	Token token.Token // 'import' token
	Path  *Identifier // package path
	Alias *Identifier // optional alias
}

func (is *ImportStatement) statementNode()       {}
func (is *ImportStatement) TokenLiteral() string { return is.Token.Literal }
func (is *ImportStatement) String() string {
	var out bytes.Buffer
	out.WriteString("import(")
	out.WriteString(is.Path.String())
	out.WriteRune(')')
	if is.Alias != nil {
		out.WriteString(" as ")
		out.WriteString(is.Alias.String())
	}
	return out.String()
}

// TypeParameter represents a type parameter with optional constraint
// Examples: T, T: Reader, T: Reader & Writer
type TypeParameter struct {
	BaseNode
	Token      token.Token // IDENT token for the type parameter name
	Name       *Identifier // Type parameter name (e.g., "T", "U")
	Constraint Expression  // Optional constraint expression (interface or intersection)
}

func (tp *TypeParameter) statementNode()       {}
func (tp *TypeParameter) TokenLiteral() string { return tp.Token.Literal }
func (tp *TypeParameter) String() string {
	if tp.Constraint != nil {
		return fmt.Sprintf("%s: %s", tp.Name.Value, tp.Constraint.String())
	}
	return tp.Name.Value
}

// Function declaration (top-level)
type FunctionStatement struct {
	BaseNode
	Token      token.Token        // 'fn' token
	EndToken   token.Token        // Last token of the function (for end position)
	TypeParams []*TypeParameter   // Optional type parameters: [T: Reader, U: Writer]
	Receiver   *FunctionParameter // optional receiver for methods: fn (recv: Type) method(...)
	Name       *Identifier
	Parameters []*FunctionParameter
	ReturnType Expression // type expression
	Body       Expression
}

func (fs *FunctionStatement) statementNode()       {}
func (fs *FunctionStatement) TokenLiteral() string { return fs.Token.Literal }
func (fs *FunctionStatement) String() string {
	var out bytes.Buffer
	out.WriteString("fn ")
	if fs.Receiver != nil {
		out.WriteRune('(')
		out.WriteString(fs.Receiver.String())
		out.WriteRune(')')
		out.WriteRune(' ')
	}
	out.WriteString(fs.Name.String())
	out.WriteRune('(')
	for i, param := range fs.Parameters {
		if i > 0 {
			out.WriteString(", ")
		}
		out.WriteString(param.String())
	}
	out.WriteRune(')')
	if fs.ReturnType != nil {
		out.WriteString(" -> ")
		out.WriteString(fs.ReturnType.String())
	}
	out.WriteRune(' ')
	out.WriteString(fs.Body.String())
	return out.String()
}

// Function parameter
type FunctionParameter struct {
	Token token.Token
	Name  *Identifier
	Type  Expression // type expression
}

func (fp *FunctionParameter) String() string {
	return fp.Name.String() + ": " + fp.Type.String()
}

// While loop
type WhileStatement struct {
	BaseNode
	Token     token.Token // 'while' token
	Condition Expression
	Body      *BlockStatement
}

func (ws *WhileStatement) statementNode()       {}
func (ws *WhileStatement) TokenLiteral() string { return ws.Token.Literal }
func (ws *WhileStatement) String() string {
	var out bytes.Buffer
	out.WriteString("while ")
	out.WriteString(ws.Condition.String())
	out.WriteRune(' ')
	out.WriteString(ws.Body.String())
	return out.String()
}

// Unsafe block
type UnsafeBlock struct {
	BaseNode
	Token token.Token // 'unsafe' token
	Body  *BlockStatement
}

func (ub *UnsafeBlock) statementNode()       {}
func (ub *UnsafeBlock) TokenLiteral() string { return ub.Token.Literal }
func (ub *UnsafeBlock) String() string {
	var out bytes.Buffer
	out.WriteString("unsafe ")
	out.WriteString(ub.Body.String())
	return out.String()
}

// REPLCommand represents a REPL directive like :exit, :quit, :help
// These are part of the language syntax and are type-checked
type REPLCommand struct {
	BaseNode
	Token token.Token  // ':' token
	Name  string       // command name: "exit", "quit", "help", "typeof"
	Args  []Expression // optional arguments to the command (e.g., expression for typeof)
}

func (rc *REPLCommand) statementNode()       {}
func (rc *REPLCommand) TokenLiteral() string { return rc.Token.Literal }
func (rc *REPLCommand) String() string {
	return ":" + rc.Name
}
