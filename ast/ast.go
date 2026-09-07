package ast

import (
	"bytes"
	"fmt"
	"sort"
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

// RecordField is one record member in source order. Value is either a value
// expression or a type expression depending on the record's syntactic context.
type RecordField struct {
	Token token.Token
	Name  string
	Value Expression
}

// RecordLiteral represents both record value and record type syntax. Fields is
// retained for O(1) compatibility lookup; FieldOrder is authoritative source order.
type RecordLiteral struct {
	BaseNode
	Token      token.Token // { token or struct token
	EndToken   token.Token // } token (for end position)
	Fields     map[string]Expression
	FieldOrder []RecordField
	TypeName   *Identifier // optional type name for type-qualified literals: TypeName{ ... }
}

// AddField appends a uniquely named field in declaration order, rejecting
// duplicates. Maintained as the transliteration of
// Oak.SemanticRecord.addField (spec/lean/Oak/SemanticRecord.lean), which
// proves construction preserves uniqueness and declaration order and that
// lookup returns exactly the member associated with a name.
func (rl *RecordLiteral) AddField(tok token.Token, name string, value Expression) bool {
	if rl.Fields == nil {
		rl.Fields = make(map[string]Expression)
	}
	if _, exists := rl.Fields[name]; exists {
		return false
	}
	rl.Fields[name] = value
	rl.FieldOrder = append(rl.FieldOrder, RecordField{Token: tok, Name: name, Value: value})
	return true
}

// OrderedFields returns source order when it is known. It deliberately returns
// nil for legacy/manually-built map-only records rather than fabricating order.
func (rl *RecordLiteral) OrderedFields() []RecordField {
	if len(rl.FieldOrder) == 0 {
		return nil
	}
	return rl.FieldOrder
}

func (rl *RecordLiteral) expressionNode()      {}
func (rl *RecordLiteral) TokenLiteral() string { return rl.Token.Literal }
func (rl *RecordLiteral) String() string {
	var out bytes.Buffer
	out.WriteRune('{')

	if len(rl.FieldOrder) > 0 {
		for i, field := range rl.FieldOrder {
			if i > 0 {
				out.WriteString(", ")
			}
			out.WriteString(field.Name)
			out.WriteString(": ")
			out.WriteString(field.Value.String())
		}
	} else {
		// Legacy/manual ASTs have no source order. Sort only for deterministic
		// rendering; semantic/layout code must not treat this as source order.
		names := make([]string, 0, len(rl.Fields))
		for name := range rl.Fields {
			names = append(names, name)
		}
		sort.Strings(names)
		for i, name := range names {
			if i > 0 {
				out.WriteString(", ")
			}
			out.WriteString(name)
			out.WriteString(": ")
			out.WriteString(rl.Fields[name].String())
		}
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
	// Dot marks member access spelled with '.', so field access (p.x) is
	// never confused with element indexing (a[i]) downstream: lowering
	// rewrites only bracket indexing to bounds-checked core_index.
	Dot bool
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

// BlockExpression is a braced statement sequence used in expression position,
// most importantly as a function block body. Every statement is retained; the
// block's value is the trailing expression statement's expression, or unit
// when the block is empty or ends with a non-expression statement.
type BlockExpression struct {
	BaseNode
	Token token.Token // { token
	Block *BlockStatement
}

func (be *BlockExpression) expressionNode()      {}
func (be *BlockExpression) TokenLiteral() string { return be.Token.Literal }
func (be *BlockExpression) String() string {
	if be.Block == nil {
		return "{}"
	}
	return "{ " + be.Block.String() + " }"
}

// Result returns the trailing expression statement's expression, or nil when
// the block's value is unit.
func (be *BlockExpression) Result() Expression {
	if be.Block == nil || len(be.Block.Statements) == 0 {
		return nil
	}
	if exprStmt, ok := be.Block.Statements[len(be.Block.Statements)-1].(*ExpressionStatement); ok {
		return exprStmt.Expression
	}
	return nil
}

// FunctionTypeExpression is a function interface type: (T1, T2) -> R.
type FunctionTypeExpression struct {
	BaseNode
	Token      token.Token // ( token
	Parameters []Expression
	Return     Expression
}

func (ft *FunctionTypeExpression) expressionNode()      {}
func (ft *FunctionTypeExpression) TokenLiteral() string { return ft.Token.Literal }
func (ft *FunctionTypeExpression) String() string {
	var out bytes.Buffer
	out.WriteRune('(')
	for i, param := range ft.Parameters {
		if i > 0 {
			out.WriteString(", ")
		}
		out.WriteString(param.String())
	}
	out.WriteString(") -> ")
	if ft.Return != nil {
		out.WriteString(ft.Return.String())
	} else {
		out.WriteString("()")
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
	Token    token.Token
	TypeName *Identifier // optional type name for Type.Variant patterns
	Variant  *Identifier // .Ok, .Some, etc.
	Payload  Pattern     // optional, for .Some(x)
}

func (vp *VariantPattern) patternNode()         {}
func (vp *VariantPattern) TokenLiteral() string { return vp.Token.Literal }
func (vp *VariantPattern) String() string {
	var out bytes.Buffer
	if vp.TypeName != nil {
		// Type.Variant form
		out.WriteString(vp.TypeName.String())
		out.WriteString(".")
		out.WriteString(vp.Variant.String())
	} else {
		// .Variant or bare variant form
		out.WriteString(".")
		out.WriteString(vp.Variant.String())
	}
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
	Payload Expression // optional payload type, e.g. Some: T
	Literal Expression // optional literal tag/default, e.g. Ok: 200
	Result  Expression // optional indexed result type, e.g. Expr[i64]
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
	if v.Result != nil {
		out.WriteString(" => ")
		out.WriteString(v.Result.String())
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
	// ExternSymbol, when non-empty, marks an extern C binding
	// (docs/spec/92-ffi.md section 2.3): the definition was
	// `c.extern("symbol")`, the function has no Oak body, and calls
	// lower to the foreign symbol.
	ExternSymbol string
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
	Type  Expression // type expression (the element type when Variadic)
	// Variadic marks a Go-style trailing parameter (rest: ...T); legal only
	// in last position. The body sees it as []T.
	Variadic bool
}

func (fp *FunctionParameter) String() string {
	if fp.Variadic {
		return fp.Name.String() + ": ..." + fp.Type.String()
	}
	return fp.Name.String() + ": " + fp.Type.String()
}

// While loop
// IfStatement is the INTERNAL branch statement: Oak has no if/else
// keywords — the surface form is the `?` condition sugar over Bool
// (docs/spec/10-syntax.md §3a), and lowering converts statement-position
// Bool matches into this node so side-effecting branches emit as C
// if/else.
type IfStatement struct {
	BaseNode
	Token       token.Token // 'if' token
	Condition   Expression
	Consequence *BlockStatement
	// Alternative is nil, an *IfStatement (else if ...), or a
	// *BlockStatement (final else).
	Alternative Statement
}

func (is *IfStatement) statementNode()       {}
func (is *IfStatement) TokenLiteral() string { return is.Token.Literal }
func (is *IfStatement) String() string {
	var out bytes.Buffer
	out.WriteString("if ")
	out.WriteString(is.Condition.String())
	out.WriteString(" { ")
	if is.Consequence != nil {
		out.WriteString(is.Consequence.String())
	}
	out.WriteString(" }")
	if is.Alternative != nil {
		out.WriteString(" else ")
		out.WriteString(is.Alternative.String())
	}
	return out.String()
}

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

// IndexAssignmentStatement writes an element through an index: s[i] = value.
// The target must be a writable span or an owned array; views are read-only.
type IndexAssignmentStatement struct {
	BaseNode
	Token  token.Token // the '=' token
	Target *IndexExpression
	Value  Expression
}

func (ia *IndexAssignmentStatement) statementNode()       {}
func (ia *IndexAssignmentStatement) TokenLiteral() string { return ia.Token.Literal }
func (ia *IndexAssignmentStatement) String() string {
	return ia.Target.String() + " = " + ia.Value.String()
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

func (rc *REPLCommand) statementNode() {}
func (rc *REPLCommand) TokenLiteral() string {
	if rc == nil {
		return ""
	}
	return rc.Token.Literal
}
func (rc *REPLCommand) String() string {
	if rc == nil {
		return "<nil REPLCommand>"
	}
	return ":" + rc.Name
}
