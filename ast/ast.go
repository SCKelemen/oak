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
	// Discard marks the explicit discard form `_ = expr`
	// (docs/spec/85-discipline.md section 6): the expression is evaluated
	// for its effects and its non-unit result is deliberately dropped.
	Discard bool
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
	// Wide marks a literal above the signed 64-bit range (2^63 .. 2^64-1):
	// Value then holds the unsigned magnitude's two's-complement bit
	// pattern, and only u64/uint/uptr contexts admit the literal.
	Wide bool
}

// Magnitude returns the literal's unsigned value (the full u64 range).
func (lit *IntegerLiteral) Magnitude() uint64 { return uint64(lit.Value) }

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
	// Manifest is the shared definition of a signature type member
	// (`Key: type = u64`, docs/spec/83-modules.md section 6.3); nil for an
	// abstract member or an ordinary field.
	Manifest Expression
	// Align is the field's declared alignment (head(align: 64): Atomic[u32]),
	// 0 for natural. A representation detail, never shape identity
	// (docs/spec/40-records.md §6a).
	Align uint32
	// Tags are the field's typed metadata (id(json: "user_id"): u64) —
	// each names a declared tag schema and carries a checked value
	// (docs/spec/40-records.md §12). Metadata axis only: never layout,
	// never the runtime value.
	Tags []FieldTag
}

// FieldTag is one typed metadata entry on a record field: the namespace
// (a declared tag schema) and its value — a bare literal (bound to the
// schema's first declared field) or a record literal over schema fields.
type FieldTag struct {
	Token token.Token
	Name  string
	Value Expression
}

// TagDeclaration declares a tag schema: json: tag = { name: string }.
// The schema body is ordinary record-type syntax; fields give the typed
// vocabulary a projection may read from tagged record fields.
type TagDeclaration struct {
	BaseNode
	Token    token.Token // the schema name token
	EndToken token.Token // closing brace of the schema
	Name     *Identifier
	Schema   *RecordLiteral
	// Exported marks a `pub` declaration (docs/spec/83-modules.md section
	// 6); visibility is never inferred from spelling. Opaque marks
	// `pub(opaque)`: the name is exported, the definition is not.
	Exported bool
	Opaque   bool
}

func (td *TagDeclaration) statementNode()       {}
func (td *TagDeclaration) TokenLiteral() string { return td.Token.Literal }
func (td *TagDeclaration) String() string {
	if td.Name != nil && td.Schema != nil {
		return td.Name.Value + ": tag = " + td.Schema.String()
	}
	return "tag declaration"
}

// RecordLiteral represents both record value and record type syntax. Fields is
// retained for O(1) compatibility lookup; FieldOrder is authoritative source order.
type RecordLiteral struct {
	BaseNode
	Token      token.Token // { token or struct token
	EndToken   token.Token // } token (for end position)
	Fields     map[string]Expression
	FieldOrder []RecordField
	// Extension is the row variable in { r | name: string }.
	// It is type-level metadata and has no runtime representation.
	Extension *Identifier
	TypeName  *Identifier       // optional type name for type-qualified literals: TypeName{ ... }
	Layout    *RecordLayoutSpec // optional declared layout: struct(packed), struct(align: 64)
}

// RecordLayoutSpec is the source-declared layout discipline of a struct type
// (docs/spec/40-records.md): Packed forbids padding between fields, Align
// raises the record's alignment (0 means natural), NoPadding claims the
// natural placement is already dense — every byte a field byte — which the
// compiler checks rather than arranges. Semantics and arithmetic live in
// semir.RecordLayoutWithSpec; this node only carries the declaration.
type RecordLayoutSpec struct {
	Packed    bool
	Align     uint32
	NoPadding bool
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
	if rl.Extension != nil {
		out.WriteString(rl.Extension.String())
		out.WriteString(" | ")
	}

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
	// Order is the reduction order the block declares once for the
	// `reduce.reduce` calls inside it (docs/spec/55-parallelism.md section
	// 4): "tree", "left", or "any" for `order tree { ... }`; "" for an
	// ordinary block.
	Order string
	// DeferredFrom, when positive, is the index of the first statement the
	// parser moved here from a `defer` (docs/spec/10-syntax.md section 4b):
	// Statements[DeferredFrom-1] is the block's original tail and
	// Statements[DeferredFrom:] run after it. The typechecker, which knows
	// the tail's type, binds a valued tail to a temporary before them and
	// resets this to zero.
	DeferredFrom int
}

func (bs *BlockStatement) statementNode()       {}
func (bs *BlockStatement) TokenLiteral() string { return bs.Token.Literal }
func (bs *BlockStatement) String() string {
	var out bytes.Buffer

	for _, s := range bs.Statements {
		out.WriteString(s.String())
	}
	if bs.Order != "" {
		// An order block prints as declared (docs/spec/55-parallelism.md
		// section 4): the order once, then its statements.
		return "order " + bs.Order + " { " + out.String() + " }"
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
	if be.Block.Order != "" {
		return be.Block.String()
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
	// Effects is the effect row of the type (`(T) -> R effects { A.B }`,
	// docs/spec/60-effects-allocation.md section 2a): a value of the type
	// performs at most these effects, so a call through it is known to the
	// effect analysis. EffectsDeclared distinguishes `effects { }` (none)
	// from no row (unknown, as before).
	Effects         []*EffectName
	EffectsDeclared bool
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
	if ft.EffectsDeclared {
		out.WriteString(" effects {")
		for i, e := range ft.Effects {
			if i > 0 {
				out.WriteString(",")
			}
			out.WriteString(" " + e.String())
		}
		out.WriteString(" }")
	}
	return out.String()
}

// FunctionLiteral is a function value written in expression position
// (docs/spec/10-syntax.md section 3c). Arguments always holds the parameter
// names. Parameters and ReturnType are set for the typed shape
// `fn(a: T): R { ... }`; ExpressionBody marks `fn(a: T): R = expr`, whose
// expression is held as the single statement of Body so every consumer
// sees one body shape.
type FunctionLiteral struct {
	BaseNode
	Token          token.Token // fn
	Arguments      []*Identifier
	Parameters     []*FunctionParameter // typed shape only; same order as Arguments
	ReturnType     Expression           // typed shape only; nil when unannotated
	ExpressionBody bool
	Body           *BlockStatement
}

func (fl *FunctionLiteral) expressionNode()      {}
func (fl *FunctionLiteral) TokenLiteral() string { return fl.Token.Literal }
func (fl *FunctionLiteral) String() string {
	var out bytes.Buffer

	out.WriteString(fl.TokenLiteral())
	out.WriteRune('(')
	if len(fl.Parameters) > 0 {
		params := []string{}
		for _, param := range fl.Parameters {
			params = append(params, param.String())
		}
		out.WriteString(strings.Join(params, ", "))
	} else {
		args := []string{}
		for _, arg := range fl.Arguments {
			args = append(args, arg.String())
		}
		out.WriteString(strings.Join(args, ", "))
	}
	out.WriteRune(')')
	if fl.ReturnType != nil {
		out.WriteString(": ")
		out.WriteString(fl.ReturnType.String())
	}
	if fl.ExpressionBody && fl.Body != nil && len(fl.Body.Statements) == 1 {
		if stmt, ok := fl.Body.Statements[0].(*ExpressionStatement); ok && stmt.Expression != nil {
			out.WriteString(" = ")
			out.WriteString(stmt.Expression.String())
			return out.String()
		}
	}
	if fl.Body != nil {
		out.WriteString(fl.Body.String())
	}

	return out.String()
}

type InvocationExpression struct {
	BaseNode
	Token     token.Token // ( token
	Function  Expression  // Identifier || FunctionLiteral
	Arguments []Expression
	// ResolvedMethod is set by the type checker when Function is the dotted
	// form `recv.method` and recv is an ADT declaring the method: the
	// checker's `Type::method` identity. The receiver stays in Function
	// (it is not an argument, so explicit argument indices never shift);
	// the backend lowers the call to the method's C function with the
	// receiver as its first parameter (docs/spec/90-backend.md).
	ResolvedMethod string `json:",omitempty"`
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
	// Exported marks a `pub` declaration (docs/spec/83-modules.md section
	// 6); visibility is never inferred from spelling. Opaque marks
	// `pub(opaque)`: the name is exported, the definition is not.
	Exported bool
	Opaque   bool
	// Section is the declared linker section of a static
	// (ring: [8]u64 (section: "shared")); empty for the default
	// (docs/spec/65-machine-memory.md). Fixed addresses stay with the
	// linker script; only the section is language surface.
	Section string
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

// FieldAccessorExpression is Elm-style .field sugar. It is a contextual,
// structurally polymorphic function: .name(value) is value.name.
type FieldAccessorExpression struct {
	BaseNode
	Token token.Token
	Field *Identifier
	// ResolvedRecord is filled by contextual type checking when the
	// accessor is used as a first-class (Record) -> Field function. It is
	// deliberately absent for direct .field(value) sugar.
	ResolvedRecord string
}

func (fa *FieldAccessorExpression) expressionNode()      {}
func (fa *FieldAccessorExpression) TokenLiteral() string { return fa.Token.Literal }
func (fa *FieldAccessorExpression) String() string       { return "." + fa.Field.String() }

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
	// Exported marks a `pub` declaration (docs/spec/83-modules.md section
	// 6); visibility is never inferred from spelling. Opaque marks
	// `pub(opaque)`: the name is exported, the definition is not.
	Exported bool
	Opaque   bool
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
	// Refinement is the predicate of `Name: type = Base where <expr>`
	// (docs/spec/20-types.md section 12): a Bool expression over `value`,
	// the candidate of the base type. The single variant's Payload is the
	// base. Nil for every other declaration.
	Refinement Expression
	// Exported marks a `pub` declaration (docs/spec/83-modules.md section
	// 6); visibility is never inferred from spelling. Opaque marks
	// `pub(opaque)`: the name is exported, the definition is not.
	Exported bool
	Opaque   bool
	// TagValues, when set, fixes each variant's tag value in the C
	// representation (one per variant, in order) instead of the
	// declaration index — a representation choice the protocol projection
	// makes for shift-DFA state types (tags are the offsets 6*i). Matching
	// compares tags by name, so nothing else observes the values.
	TagValues []int `json:",omitempty"`
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

// Package declaration. TypeParams make the package generic
// (`package ring[T, N: u32]`, docs/spec/83-modules.md section 6.7); each
// import instantiates it with arguments.
type PackageStatement struct {
	BaseNode
	Token      token.Token // 'package' token
	Name       *Identifier
	TypeParams []*TypeParameter
}

func (ps *PackageStatement) statementNode()       {}
func (ps *PackageStatement) TokenLiteral() string { return ps.Token.Literal }
func (ps *PackageStatement) String() string {
	return "package " + ps.Name.String()
}

// ModuleDeclaration is a nested module (docs/spec/83-modules.md section
// 3.5): `module name { declarations }` inside a package file declares the
// package `<enclosing path>/name` with its own `pub` boundary. The loader
// extracts the body into that package and binds `name` in the enclosing
// package as an implicit import.
type ModuleDeclaration struct {
	BaseNode
	Token token.Token // the contextual 'module' identifier
	Name  *Identifier
	Body  *BlockStatement
}

func (md *ModuleDeclaration) statementNode()       {}
func (md *ModuleDeclaration) TokenLiteral() string { return md.Token.Literal }
func (md *ModuleDeclaration) String() string {
	var out bytes.Buffer
	out.WriteString("module ")
	if md.Name != nil {
		out.WriteString(md.Name.String())
	}
	out.WriteString(" ")
	if md.Body != nil {
		out.WriteString(md.Body.String())
	}
	return out.String()
}

// ImportStatement is a package import (docs/spec/83-modules.md section 3).
// The statement form `import("example.com/net")` binds the path's last
// segment; the binding forms `net := import("example.com/net")` and
// `n: Sig = import("example.com/net")` name the binding explicitly, the
// latter sealing the import to the signature Sig.
type ImportStatement struct {
	BaseNode
	Token token.Token // 'import' token
	// Path is the import path; its Value is the full path text ("a/b").
	Path *Identifier
	// Alias is the explicit binding name of a binding-form import; nil
	// means the last path segment.
	Alias *Identifier
	// Signature is the sealing type of `alias: Sig = import(path)`; nil
	// for an unsealed import.
	Signature Expression
	// Arguments instantiate a generic package: import("...")[u8, 8].
	Arguments []Expression
	// Names are the unqualified bindings of a selective import
	// `{ f, g } := import(path)`; Alias is nil for those.
	Names []*Identifier
	// Open marks `open import(path)`: every exported member of the package
	// is bound unqualified (docs/spec/83-modules.md section 3.2).
	Open bool
	// Implicit marks an import the loader synthesized for a nested module
	// (section 3.5); it is never reported unused.
	Implicit bool
}

func (is *ImportStatement) statementNode()       {}
func (is *ImportStatement) TokenLiteral() string { return is.Token.Literal }
func (is *ImportStatement) String() string {
	var out bytes.Buffer
	if is.Open {
		out.WriteString("open ")
	}
	if is.Alias != nil {
		out.WriteString(is.Alias.String())
		if is.Signature != nil {
			out.WriteString(": ")
			out.WriteString(is.Signature.String())
			out.WriteString(" = ")
		} else {
			out.WriteString(" := ")
		}
	}
	out.WriteString("import(\"")
	if is.Path != nil {
		out.WriteString(is.Path.Value)
	}
	out.WriteString("\")")
	return out.String()
}

// ImportExpression is `import(path)` in expression position. It is legal
// only as the whole initializer of a top-level binding, where the parser
// folds it into an ImportStatement; anywhere else the loader rejects it.
type ImportExpression struct {
	BaseNode
	Token     token.Token // 'import' token
	Path      *Identifier
	Arguments []Expression
}

func (ie *ImportExpression) expressionNode()      {}
func (ie *ImportExpression) TokenLiteral() string { return ie.Token.Literal }
func (ie *ImportExpression) String() string {
	if ie.Path == nil {
		return "import()"
	}
	return "import(\"" + ie.Path.Value + "\")"
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
// LawClause is one declared operator law: its name and, for `identity(e)`,
// the identity element (docs/spec/10-syntax.md section 14a).
type LawClause struct {
	Name     string
	Argument Expression // nil for a bare law name
}

// String prints the clause as declared: `identity(zero())`, `associative`.
func (l *LawClause) String() string {
	if l.Argument == nil {
		return l.Name
	}
	return l.Name + "(" + l.Argument.String() + ")"
}

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
	// Theorem marks `name: theorem (params) { Bool }`
	// (docs/spec/125-verification.md): a Bool-valued function whose
	// parameters are universally quantified. It is checked and compiled as
	// an ordinary function; `oak prove` discharges it.
	Theorem bool
	// ExternSymbol, when non-empty, marks an extern C binding
	// (docs/spec/92-ffi.md section 2.3): the definition was
	// `c.extern("symbol")`, the function has no Oak body, and calls
	// lower to the foreign symbol.
	ExternSymbol string
	// AsmBacked marks a definition-less declaration whose body an asm
	// translation unit provides (docs/spec/94-assembler.md): the Oak side
	// is the typed interface, the unit the instruction sequence. Set by the
	// compilation when a unit's matching signature is found; a body-less
	// declaration with no unit is a compile error.
	AsmBacked bool
	// AsmArch is the lane of the unit backing an AsmBacked declaration
	// ("arm64" or "rv64", docs/spec/94-assembler.md §9): the C backend
	// emits the Oak fallback body under the lane's negated condition.
	AsmArch string
	// NativeBacked marks a body the native backend lowered (nativegen,
	// docs/spec/94-assembler.md §9): the C backend emits the Oak body only
	// for the portable realization, as for an asm unit with a fallback.
	NativeBacked bool
	// Exported marks a `pub` declaration (docs/spec/83-modules.md section
	// 6); visibility is never inferred from spelling. Opaque marks
	// `pub(opaque)`: the name is exported, the definition is not.
	Exported bool
	Opaque   bool
	// Kernel marks a `kernel name: (gid: u32, ...): () = ...` declaration
	// (docs/spec/56-kernels.md): a function in the kernel subset that the
	// Metal emitter compiles to a compute kernel and the C backend to an
	// ordinary function whose first parameter is the grid position.
	Kernel bool
	// Operator is the symbol an `operator(SYM)` marker binds to this
	// function for a left operand of its first parameter's type
	// (docs/spec/10-syntax.md section 14); empty for ordinary functions.
	Operator string
	// ExportSymbol is the C symbol an `export("symbol")` marker gives this
	// function at the C ABI boundary (docs/spec/92-ffi.md section 2.9): a
	// pub function of any package becomes callable from C under that
	// program-unique name. Empty for functions without the marker; the root
	// package's pub functions are exported implicitly as `oak_<name>`.
	ExportSymbol string
	// Effect clauses (docs/spec/60-effects-allocation.md section 2):
	// `effects { Memory.Allocate, ... }` declares the effects this function
	// itself performs (EffectsDeclared distinguishes an empty clause, an
	// assertion of purity for an extern, from no clause); `forbids { ... }`
	// rejects the program when any of these effects is reachable from the
	// function through the call graph.
	Effects         []*EffectName
	EffectsDeclared bool
	Forbids         []*EffectName
	// Laws are the algebraic properties an operator definition declares on
	// the author's authority (`laws { associative, commutative,
	// identity(zero()), idempotent }`, docs/spec/10-syntax.md section
	// 14a): the permission a backend has to regroup or reorder applications
	// of the operator, and a statement the REPL's :lean can put to Lean and
	// `oak prove` can decide. Empty for ordinary functions.
	Laws []*LawClause
	// Lowering, when set, is the compiler-known lowering of a projected
	// protocol step function (docs/spec/112-protocols.md section 2a,
	// 90-backend.md section 14): the C backend emits a transition table
	// or shift-DFA body in place of the Oak body, which remains the
	// function's meaning for the interpreter and the Lean extraction.
	// Set by the protocol projection only; never by the parser.
	Lowering *ProtocolLowering `json:",omitempty"`
}

// ProtocolLowering is the resolved transition table of a protocol without
// a data record, attached to its projected `legal`, `next`, and `run`
// functions. Symbols are the step tags, or the 256 values of the single
// step's u8 payload when ByteSymbol is set (guards over the payload are
// evaluated at compile time for every value). Table holds (States+1) rows
// of Symbols entries: the next state's index, or States (the sink, also
// the illegal sentinel); the sink row maps every symbol to the sink. Shift
// selects the shift-DFA form, admitted when States+1 <= 10, under which the
// state ADT's tags are the offsets 6*i (ADTType.TagValues) and a step is
// (rows[symbol] >> state) & 63. Oak.Protocol proves both forms compute the
// declaration's first-match semantics.
type ProtocolLowering struct {
	Protocol   string
	Kind       string // "legal", "next", or "run"
	States     int
	Symbols    int
	ByteSymbol bool
	StepName   string // the variant carrying the byte payload, ByteSymbol only
	Table      []int
	Shift      bool
}

// EffectName is one `Namespace.Name` in an effect clause.
type EffectName struct {
	BaseNode
	Token     token.Token
	Namespace string
	Name      string
}

func (e *EffectName) TokenLiteral() string { return e.Token.Literal }
func (e *EffectName) String() string       { return e.Namespace + "." + e.Name }

func (fs *FunctionStatement) statementNode()       {}
func (fs *FunctionStatement) TokenLiteral() string { return fs.Token.Literal }
func (fs *FunctionStatement) String() string {
	var out bytes.Buffer
	if fs.Theorem {
		out.WriteString("theorem ")
	} else if fs.Kernel {
		out.WriteString("kernel ")
	} else {
		out.WriteString("fn ")
	}
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
	writeEffects := func(keyword string, names []*EffectName) {
		out.WriteString(" " + keyword + " {")
		for i, e := range names {
			if i > 0 {
				out.WriteString(",")
			}
			out.WriteString(" " + e.String())
		}
		out.WriteString(" }")
	}
	if fs.EffectsDeclared {
		writeEffects("effects", fs.Effects)
	}
	if len(fs.Forbids) > 0 {
		writeEffects("forbids", fs.Forbids)
	}
	if len(fs.Laws) > 0 {
		names := make([]string, 0, len(fs.Laws))
		for _, law := range fs.Laws {
			names = append(names, law.String())
		}
		out.WriteString(" laws { ")
		out.WriteString(strings.Join(names, ", "))
		out.WriteString(" }")
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

// BreakStatement leaves the innermost enclosing while loop
// (docs/spec/85-discipline.md section 3): `break` is legal only inside a
// loop body, and a bounded loop stays bounded when a break leaves it early.
// DeferStatement is `defer <statement>` (docs/spec/10-syntax.md section
// 4b). It exists only between parsing a statement and finishing its
// enclosing block: the parser reorders deferred statements to where they
// run, so no later phase sees this node.
type DeferStatement struct {
	BaseNode
	Token token.Token // 'defer' token
	Body  Statement
}

func (ds *DeferStatement) statementNode()       {}
func (ds *DeferStatement) TokenLiteral() string { return ds.Token.Literal }
func (ds *DeferStatement) String() string {
	if ds.Body == nil {
		return "defer"
	}
	return "defer " + ds.Body.String()
}

type BreakStatement struct {
	BaseNode
	Token token.Token // 'break' token
}

func (bs *BreakStatement) statementNode()       {}
func (bs *BreakStatement) TokenLiteral() string { return bs.Token.Literal }
func (bs *BreakStatement) String() string       { return "break" }

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

// FloatLiteral is a floating-point literal (docs/spec/20-types.md section
// 11.3.2): `1.5`, `2.0e-5`, `1e3`. Text keeps the source spelling so the
// typechecker can round it correctly to the width its context requires
// (f32 or f64) from the exact decimal value, never through an intermediate
// width; Value is the f64 reading for phases that only need a number.
type FloatLiteral struct {
	BaseNode
	Token token.Token
	Text  string
	Value float64
}

func (fl *FloatLiteral) expressionNode()      {}
func (fl *FloatLiteral) TokenLiteral() string { return fl.Token.Literal }
func (fl *FloatLiteral) String() string       { return fl.Text }

// ProtocolDeclaration is `Name: protocol = { ... }` (docs/spec/112-protocols.md):
// a finite control-state machine declared once and projected into the
// state and step types, the legality and transition functions, the
// model-checker module, and (through `via`) the resource protocol facts.
// `protocol` is contextual, like `tag`: only IDENT ':' protocol '=' '{'
// reads as a declaration.
type ProtocolDeclaration struct {
	BaseNode
	Token       token.Token // the protocol name token
	EndToken    token.Token // closing brace
	Name        *Identifier
	Resources   []*Identifier  // `resource T`: nominal types governed by the protocol
	Initial     *Identifier    // `initial S`
	Data        *RecordLiteral // `data { field: T, ... }`: the machine's data record, or nil
	Init        *RecordLiteral // `init { field: value, ... }`: the initial data, required with Data
	Transitions []*ProtocolTransition
	// Fairness and Liveness are the `fair step` / `strongly fair step` and
	// `eventually target` / `eventually from -> target` entries
	// (docs/spec/112-protocols.md section 1): assumptions and temporal
	// properties the model-checker module states; the projection into
	// Oak reads neither.
	Fairness []*ProtocolFairness
	Liveness []*ProtocolLiveness
	Exported bool
}

// ProtocolFairness is one `fair step` (weak) or `strongly fair step`
// entry: every line of the step, its payload quantified.
type ProtocolFairness struct {
	Token  token.Token
	Step   *Identifier
	Strong bool
}

// ProtocolLiveness is one `eventually target` or `eventually from ->
// target` entry. Each side is a state name (spelled like a variant) or a
// Bool expression over `data` in the guard subset.
type ProtocolLiveness struct {
	Token  token.Token
	From   Expression // nil for `eventually target`
	Target Expression
}

// ProtocolTransition is one
// `name(param: T)?: From -> To (when guard)? (then { effects })? (via callable)?` line.
type ProtocolTransition struct {
	Token    token.Token
	Name     *Identifier
	Param    *FunctionParameter // optional payload: one fixed-width scalar or Bool
	From     *Identifier
	To       *Identifier
	Guard    Expression      // optional `when` expression over data.field and the payload
	Effects  *BlockStatement // optional `then { ... }` statements over data.field and the payload
	Callable *Identifier     // optional `via f`: the function that performs it
	// CallableType is set when the callable is spelled `Type.method`: the
	// receiver type whose method performs the transition. The checker knows
	// the method as `Type::method`.
	CallableType *Identifier
	// Trusted marks `via unsafe f(...)`: the result identity written on
	// this line is an assumption the compiler records instead of a claim
	// it validates against f's body (docs/spec/112-protocols.md section 5).
	Trusted      bool
	TrustedToken token.Token
	// Modes are the resource parameter modes written after the callable,
	// `via f(consumed h, borrowed other, borrowed mut receiver)`
	// (docs/spec/112-protocols.md section 5): each names one of f's
	// parameters, or `receiver`, with its authority mode — or, for a
	// function-typed parameter, the callable contract it requires.
	Modes []*ProtocolParameterMode
	// Result is the result identity written after the parenthesized
	// modes, `: fresh`, `: alias h`, `: borrow h, g`, or `: borrow mut h`.
	Result *ProtocolResultClause
}

// ProtocolParameterMode is one entry of a `via` clause: `mode name` for a
// resource parameter, or `name(contract)` for a function-typed parameter.
type ProtocolParameterMode struct {
	Token token.Token // the mode keyword, or the parameter name for a contract entry
	Mode  string      // "borrowed", "borrowed mut", or "consumed"; empty for a contract entry
	Name  *Identifier // a parameter name of the callable, or `receiver`
	// Contract is the callable contract of a function-typed parameter,
	// `op(borrowed, _): fresh`: one mode per parameter of the function
	// type, positionally, and whether the callable must return fresh
	// authority.
	Contract *ProtocolCallableContract
}

// ProtocolCallableContract is the contract a `via` clause requires of the
// function values passed for one function-typed parameter. Modes are
// positional over the function type's parameters: "borrowed", "borrowed
// mut", "consumed", or "_" for a parameter the contract leaves unmarked.
type ProtocolCallableContract struct {
	Token        token.Token
	Modes        []string
	ModeTokens   []token.Token
	ReturnsFresh bool
}

// ProtocolResultClause is the result identity of a `via` line: Kind is
// "fresh" (no names), "alias" (exactly one parameter name), "borrow" or
// "borrow mut" (one or more parameter names, the origins).
type ProtocolResultClause struct {
	Token token.Token
	Kind  string
	Names []*Identifier
}

func (pd *ProtocolDeclaration) statementNode()       {}
func (pd *ProtocolDeclaration) TokenLiteral() string { return pd.Token.Literal }
func (pd *ProtocolDeclaration) String() string {
	var out bytes.Buffer
	out.WriteString(pd.Name.String())
	out.WriteString(": protocol = {")
	for _, r := range pd.Resources {
		out.WriteString(" resource ")
		out.WriteString(r.String())
	}
	if pd.Initial != nil {
		out.WriteString(" initial ")
		out.WriteString(pd.Initial.String())
	}
	for _, t := range pd.Transitions {
		out.WriteString(" ")
		out.WriteString(t.Name.String())
		if t.Param != nil {
			out.WriteString("(")
			out.WriteString(t.Param.Name.String())
			out.WriteString(": ")
			out.WriteString(t.Param.Type.String())
			out.WriteString(")")
		}
		out.WriteString(": ")
		out.WriteString(t.From.String())
		out.WriteString(" -> ")
		out.WriteString(t.To.String())
		if t.Guard != nil {
			out.WriteString(" when ")
			out.WriteString(t.Guard.String())
		}
		if t.Effects != nil {
			out.WriteString(" then ")
			out.WriteString(t.Effects.String())
		}
		if t.Callable != nil {
			out.WriteString(" via ")
			if t.Trusted {
				out.WriteString("unsafe ")
			}
			if t.CallableType != nil {
				out.WriteString(t.CallableType.String())
				out.WriteString(".")
			}
			out.WriteString(t.Callable.String())
			if len(t.Modes) > 0 {
				out.WriteString("(")
				for i, mode := range t.Modes {
					if i > 0 {
						out.WriteString(", ")
					}
					if mode.Contract != nil {
						out.WriteString(mode.Name.String())
						out.WriteString("(")
						out.WriteString(strings.Join(mode.Contract.Modes, ", "))
						out.WriteString(")")
						if mode.Contract.ReturnsFresh {
							out.WriteString(": fresh")
						}
						continue
					}
					out.WriteString(mode.Mode + " " + mode.Name.String())
				}
				out.WriteString(")")
			}
			if t.Result != nil {
				out.WriteString(": ")
				out.WriteString(t.Result.Kind)
				for i, name := range t.Result.Names {
					if i > 0 {
						out.WriteString(",")
					}
					out.WriteString(" ")
					out.WriteString(name.String())
				}
			}
		}
	}
	out.WriteString(" }")
	return out.String()
}
