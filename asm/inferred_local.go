package asm

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// inferredLocalType checks a deliberately closed fragment of source typing.
// It never consults backend annotations or position-keyed checker metadata:
// both operands must determine the same exact primitive type from the current
// source scope. In particular, no return-context width is used to guess a
// local's type, and untyped literals, nominal types and arbitrary calls stay
// outside this fragment. This only supplies a type to the existing lowering;
// it is not evidence of equality between source and machine code.
func inferredLocalType(expr ast.Expression, lookup func(string) (*oakType, bool), shadowed func(string) bool) (*oakType, bool) {
	primitive := func(t *oakType) bool {
		return t != nil && t.kind == oakScalar && !t.float && (t.width == 1 && !t.signed || t.width == 8 || t.width == 16 || t.width == 32 || t.width == 64)
	}
	var infer func(ast.Expression) (*oakType, bool)
	infer = func(expr ast.Expression) (*oakType, bool) {
		switch e := expr.(type) {
		case *ast.Boolean:
			return &oakType{kind: oakScalar, width: 1}, true
		case *ast.Identifier:
			typ, ok := lookup(e.Value)
			return typ, ok && primitive(typ)
		case *ast.PrefixExpression:
			typ, ok := infer(e.Right)
			if !ok {
				return nil, false
			}
			switch e.Operator {
			case "!":
				return typ, typ.width == 1
			case "^":
				return typ, typ.width > 1 && !typ.signed
			case "-":
				return typ, typ.width > 1 && typ.signed
			}
		case *ast.InfixExpression:
			left, ok := infer(e.Left)
			if !ok {
				return nil, false
			}
			right, ok := infer(e.Right)
			if !ok || left.width != right.width || left.signed != right.signed {
				return nil, false
			}
			switch e.Operator {
			case "&&", "||":
				return left, left.width == 1
			case "==", "!=":
				return &oakType{kind: oakScalar, width: 1}, true
			case "<", "<=", ">", ">=":
				return &oakType{kind: oakScalar, width: 1}, left.width > 1
			case "&", "|", "^":
				return left, left.width > 1 && !left.signed
			case "+", "-", "*", "/", "%":
				return left, left.width > 1
			}
		case *ast.InvocationExpression:
			name, ok := e.Function.(*ast.Identifier)
			if !ok || len(e.Arguments) != 1 || shadowed(name.Value) {
				return nil, false
			}
			width, signed, ok := contractBits(name)
			typ := &oakType{kind: oakScalar, width: width, signed: signed}
			if !ok || width == 1 || name.Value == "f32" || name.Value == "f64" {
				return nil, false
			}
			// A constructor is admitted only for an exactly representable integer
			// literal or an operand already of this exact type. No truncating cast
			// or target-sized default integer is silently assumed.
			if literal, ok := e.Arguments[0].(*ast.IntegerLiteral); ok {
				if literal.Wide {
					return typ, width == 64 && !signed
				}
				if signed {
					if width == 64 {
						return typ, true
					}
					limit := int64(1) << (width - 1)
					return typ, literal.Value >= -limit && literal.Value < limit
				}
				return typ, literal.Value >= 0 && uint64(literal.Value) <= mask(width)
			}
			arg, ok := infer(e.Arguments[0])
			return typ, ok && arg.width == width && arg.signed == signed
		}
		return nil, false
	}
	return infer(expr)
}

func primitiveTypeExpression(typ *oakType) ast.Expression {
	name := "Bool"
	if typ.width != 1 {
		prefix := "u"
		if typ.signed {
			prefix = "i"
		}
		name = fmt.Sprintf("%s%d", prefix, typ.width)
	}
	return &ast.Identifier{Value: name}
}

// sourcePrimitiveScope retains exact source annotations, separately from the
// symbolic execution environment (which may retain loop and branch locals).
// A nil entry shadows constructors but supplies no primitive typing evidence.
func sourcePrimitiveScope(sig *ast.FunctionStatement) map[string]ast.Expression {
	scope := map[string]ast.Expression{}
	if sig.Name != nil {
		if _, _, primitiveName := contractBits(sig.Name); primitiveName {
			scope[sig.Name.Value] = nil // a function cannot impersonate a constructor
		}
	}
	for _, param := range sig.Parameters {
		if param != nil && param.Name != nil {
			name := param.Name.Value
			_, duplicate := scope[name]
			functionCollision := sig.Name != nil && sig.Name.Value == name
			if duplicate || functionCollision {
				// Ambiguous raw/mutated binders never acquire last-wins authority.
				scope[name] = nil
			} else {
				scope[name] = param.Type
			}
		}
	}
	return scope
}

func copyPrimitiveScope(scope map[string]ast.Expression) map[string]ast.Expression {
	copy := make(map[string]ast.Expression, len(scope))
	for name, typ := range scope {
		copy[name] = typ
	}
	return copy
}

func sourcePrimitiveLookup(scope map[string]ast.Expression, name string, shadowed func(string) bool) (*oakType, bool) {
	typ := scope[name]
	// Only a source identifier is a primitive annotation; diagnostic String
	// output from a composite or nominal type never supplies authority.
	ident, ok := typ.(*ast.Identifier)
	if !ok || ident == nil || shadowed(ident.Value) {
		return nil, false
	}
	width, signed, ok := contractBits(ident)
	return &oakType{kind: oakScalar, width: width, signed: signed, float: ident.Value == "f32" || ident.Value == "f64"}, ok
}

func (lo *oakLowering) enterPrimitiveScope() func() {
	saved := lo.primitiveScope
	lo.primitiveScope = copyPrimitiveScope(saved)
	return func() { lo.primitiveScope = saved }
}

func (lo *oakLowering) inferredLocalType(expr ast.Expression) (ast.Expression, bool) {
	shadowed := func(name string) bool {
		_, local := lo.primitiveScope[name]
		_, function := lo.functions[name]
		_, global := lo.globals[name]
		_, constant := lo.constants[name]
		_, record := lo.records[name]
		_, adt := lo.adts[name]
		_, refinement := lo.guards[name]
		return local || function || global || constant || record || adt || refinement
	}
	lookup := func(name string) (*oakType, bool) { return sourcePrimitiveLookup(lo.primitiveScope, name, shadowed) }
	typ, ok := inferredLocalType(expr, lookup, shadowed)
	if !ok {
		return nil, false
	}
	return primitiveTypeExpression(typ), true
}
