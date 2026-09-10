package compiler

import (
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/token"
)

// synth builds Oak syntax for derived declarations directly, as typed AST
// nodes, so a derivation is a structured compiler transformation rather than
// a source string that is reparsed (roadmap item 5: typed codec derivation).
// The shapes match what the parser produces for the same source — the Bool
// conditional is a match on literal true/false arms, a field store is an
// index assignment with the Dot mark, a generic application is a chain of
// index expressions — so every later phase sees ordinary syntax.
//
// Every node receives its own synthetic token: the resolution context names
// the generated function (position-keyed records must not alias across
// derivations) and the column is a per-builder counter (they must not alias
// within one). Synthetic tokens carry no source line, so #line directives
// and located asserts never point into the compiler.
type synth struct {
	context string
	next    int
}

func newSynth(context string) *synth {
	return &synth{context: context}
}

// tok mints a fresh token whose literal is the node's spelling.
func (s *synth) tok(kind token.TokenKind, literal string) token.Token {
	s.next++
	return token.Token{
		SemanticContext: s.context,
		TokenKind:       kind,
		Literal:         literal,
		Line:            0,
		Column:          s.next,
		ByteStart:       s.next,
		ByteEnd:         s.next + 1,
		Synthetic:       true,
	}
}

// ---- expressions

func (s *synth) id(name string) *ast.Identifier {
	return &ast.Identifier{Token: s.tok(token.IDENT, name), Value: name}
}

func (s *synth) intLit(value int64) *ast.IntegerLiteral {
	return &ast.IntegerLiteral{Token: s.tok(token.INT, strconv.FormatInt(value, 10)), Value: value}
}

func (s *synth) boolean(value bool) *ast.Boolean {
	return &ast.Boolean{Token: s.tok(token.IDENT, strconv.FormatBool(value)), Value: value}
}

func (s *synth) call(fn string, args ...ast.Expression) *ast.InvocationExpression {
	return &ast.InvocationExpression{Token: s.tok(token.LPAREN, "("), Function: s.id(fn), Arguments: args}
}

// conv is a primitive constructor call: u32(x), u64(x), i64(x).
func (s *synth) conv(typ string, value ast.Expression) ast.Expression {
	return s.call(typ, value)
}

// u8, u32, u64, i64 are typed integer constants: u32(7).
func (s *synth) u8(value int64) ast.Expression  { return s.conv("u8", s.intLit(value)) }
func (s *synth) u32(value int64) ast.Expression { return s.conv("u32", s.intLit(value)) }
func (s *synth) i64(value int64) ast.Expression { return s.conv("i64", s.intLit(value)) }

// u64 spells a full-range unsigned constant; above the signed literal range
// it is composed from two halves, as the decoders have always done.
func (s *synth) u64(value uint64) ast.Expression {
	if value <= 9223372036854775807 {
		return s.conv("u64", s.intLit(int64(value)))
	}
	high := s.conv("u64", s.intLit(int64(value>>32)))
	low := s.conv("u64", s.intLit(int64(value&4294967295)))
	return s.infix(s.infix(high, "*", s.conv("u64", s.intLit(4294967296))), "+", low)
}

func (s *synth) field(base ast.Expression, name string) *ast.IndexExpression {
	return &ast.IndexExpression{Token: s.tok(token.DOT, "."), Left: base, Index: s.id(name), Dot: true}
}

func (s *synth) index(base, at ast.Expression) *ast.IndexExpression {
	return &ast.IndexExpression{Token: s.tok(token.LBRACK, "["), Left: base, Index: at}
}

func (s *synth) prefix(operator string, right ast.Expression) *ast.PrefixExpression {
	return &ast.PrefixExpression{Token: s.tok(token.ILLEGAL, operator), Operator: operator, Right: right}
}

func (s *synth) not(operand ast.Expression) ast.Expression { return s.prefix("!", operand) }
func (s *synth) addressOf(name string) ast.Expression      { return s.prefix("&", s.id(name)) }

func (s *synth) infix(left ast.Expression, operator string, right ast.Expression) *ast.InfixExpression {
	return &ast.InfixExpression{Token: s.tok(token.ILLEGAL, operator), Left: left, Operator: operator, Right: right}
}

// chain folds operands left-associatively under one operator, as the parser
// does for a || b || c.
func (s *synth) chain(operator string, operands ...ast.Expression) ast.Expression {
	result := operands[0]
	for _, operand := range operands[1:] {
		result = s.infix(result, operator, operand)
	}
	return result
}

func (s *synth) eq(a, b ast.Expression) ast.Expression  { return s.infix(a, "==", b) }
func (s *synth) ne(a, b ast.Expression) ast.Expression  { return s.infix(a, "!=", b) }
func (s *synth) lt(a, b ast.Expression) ast.Expression  { return s.infix(a, "<", b) }
func (s *synth) le(a, b ast.Expression) ast.Expression  { return s.infix(a, "<=", b) }
func (s *synth) gt(a, b ast.Expression) ast.Expression  { return s.infix(a, ">", b) }
func (s *synth) ge(a, b ast.Expression) ast.Expression  { return s.infix(a, ">=", b) }
func (s *synth) add(a, b ast.Expression) ast.Expression { return s.infix(a, "+", b) }
func (s *synth) sub(a, b ast.Expression) ast.Expression { return s.infix(a, "-", b) }
func (s *synth) and(operands ...ast.Expression) ast.Expression {
	return s.chain("&&", operands...)
}
func (s *synth) or(operands ...ast.Expression) ast.Expression { return s.chain("||", operands...) }

// variant is a variant literal inferred from context: .Ok(x), .None.
func (s *synth) variant(name string, payload ast.Expression) *ast.VariantExpression {
	return &ast.VariantExpression{Token: s.tok(token.DOT, "."), Variant: s.id(name), Payload: payload}
}

// record is a typed record literal: JsonToken { kind: ..., start: ... }.
func (s *synth) record(typeName string, fields ...recordInit) *ast.RecordLiteral {
	literal := &ast.RecordLiteral{
		Token:    s.tok(token.LBRACE, "{"),
		EndToken: s.tok(token.RBRACE, "}"),
		Fields:   map[string]ast.Expression{},
		TypeName: s.id(typeName),
	}
	for _, field := range fields {
		literal.Fields[field.name] = field.value
		literal.FieldOrder = append(literal.FieldOrder, ast.RecordField{Token: s.tok(token.IDENT, field.name), Name: field.name, Value: field.value})
	}
	return literal
}

type recordInit struct {
	name  string
	value ast.Expression
}

func (s *synth) set(name string, value ast.Expression) recordInit { return recordInit{name, value} }

func (s *synth) block(statements ...ast.Statement) *ast.BlockExpression {
	return &ast.BlockExpression{Token: s.tok(token.LBRACE, "{"), Block: &ast.BlockStatement{Token: s.tok(token.LBRACE, "{"), Statements: statements}}
}

// cond is the Bool conditional cond ? then | otherwise: a match on literal
// true and false arms, exactly as the parser desugars it. A nil otherwise
// is the empty block, so a one-armed conditional stays exhaustive.
func (s *synth) cond(condition, then, otherwise ast.Expression) *ast.MatchExpression {
	if otherwise == nil {
		otherwise = s.block()
	}
	qmark := s.tok(token.ILLEGAL, "?")
	return &ast.MatchExpression{
		Token:     qmark,
		Scrutinee: condition,
		Arms: []*ast.MatchArm{
			{Token: qmark, Pattern: &ast.LiteralPattern{Token: qmark, Value: s.boolean(true)}, Body: then},
			{Token: qmark, Pattern: &ast.LiteralPattern{Token: qmark, Value: s.boolean(false)}, Body: otherwise},
		},
	}
}

// match is a variant match: scrutinee ? | .A(x) => ... | .B => ....
func (s *synth) match(scrutinee ast.Expression, arms ...*ast.MatchArm) *ast.MatchExpression {
	return &ast.MatchExpression{Token: s.tok(token.ILLEGAL, "?"), Scrutinee: scrutinee, Arms: arms}
}

// arm is one variant arm; an empty binding is a payload-less pattern.
func (s *synth) arm(variant, binding string, body ast.Expression) *ast.MatchArm {
	pattern := &ast.VariantPattern{Token: s.tok(token.DOT, "."), Variant: s.id(variant)}
	if binding != "" {
		pattern.Payload = &ast.BindingPattern{Token: s.tok(token.IDENT, binding), Name: s.id(binding)}
	}
	return &ast.MatchArm{Token: s.tok(token.PIPE, "|"), Pattern: pattern, Body: body}
}

// ---- types

// app is a generic type application Name[A, B]: the index chain the parser
// builds.
func (s *synth) app(name string, args ...ast.Expression) ast.Expression {
	var result ast.Expression = s.id(name)
	for _, arg := range args {
		result = &ast.IndexExpression{Token: s.tok(token.LBRACK, "["), Left: result, Index: arg}
	}
	return result
}

func (s *synth) view(element ast.Expression) ast.Expression {
	return &ast.IndexExpression{Token: s.tok(token.LBRACK, "["), Left: element, Index: s.id("")}
}

func (s *synth) span(element ast.Expression) ast.Expression {
	return &ast.IndexExpression{Token: s.tok(token.LBRACK, "["), Left: element, Index: s.id("*")}
}

func (s *synth) array(length int64, element ast.Expression) ast.Expression {
	return &ast.IndexExpression{Token: s.tok(token.LBRACK, "["), Left: element, Index: s.intLit(length)}
}

// ---- statements

// decl is name: typ = value; a nil value is a zero-initialized declaration.
func (s *synth) decl(name string, typ, value ast.Expression) *ast.VariableDeclaration {
	return &ast.VariableDeclaration{Token: s.tok(token.IDENT, name), Name: s.id(name), Type: typ, Value: value}
}

func (s *synth) assign(name string, value ast.Expression) *ast.AssignmentStatement {
	return &ast.AssignmentStatement{Token: s.tok(token.IDENT, name), Name: s.id(name), Value: value}
}

// store is an element or field store: target[i] = v, target.f = v.
func (s *synth) store(target *ast.IndexExpression, value ast.Expression) *ast.IndexAssignmentStatement {
	return &ast.IndexAssignmentStatement{Token: s.tok(token.ASSIGN, "="), Target: target, Value: value}
}

func (s *synth) expr(expression ast.Expression) *ast.ExpressionStatement {
	return &ast.ExpressionStatement{Token: s.tok(token.ILLEGAL, "expr"), Expression: expression}
}

func (s *synth) loop(condition ast.Expression, body ...ast.Statement) *ast.WhileStatement {
	return &ast.WhileStatement{Token: s.tok(token.IDENT, "while"), Condition: condition, Body: &ast.BlockStatement{Token: s.tok(token.LBRACE, "{"), Statements: body}}
}

func (s *synth) param(name string, typ ast.Expression) *ast.FunctionParameter {
	return &ast.FunctionParameter{Token: s.tok(token.IDENT, name), Name: s.id(name), Type: typ}
}

// fn is a declaration-form function with a block body whose last statement
// is its result.
func (s *synth) fn(name string, params []*ast.FunctionParameter, returns ast.Expression, body ...ast.Statement) *ast.FunctionStatement {
	return &ast.FunctionStatement{
		Token:      s.tok(token.IDENT, name),
		EndToken:   s.tok(token.RBRACE, "}"),
		Name:       s.id(name),
		Parameters: params,
		ReturnType: returns,
		Body:       s.block(body...),
	}
}
