package typechecker

// Static globals (docs/spec/60-effects-allocation.md section 10a,
// MISRA/Power-of-Ten style): a top-level binding is static storage, and its
// initializer must be a compile-time constant — literals, arithmetic over
// literals, primitive casts of constants, the named conversions and float
// constructors applied to constants (folded by the compiler, ml finding
// F19), record/array literals of constants, or nothing (zero
// initialization). Runtime initialization is written explicitly in main,
// never hidden in global constructors.

import "github.com/SCKelemen/oak/ast"

// CodeGlobalInitializerNotConstant rejects top-level initializers the C
// backend cannot place in static storage as constant expressions.
const CodeGlobalInitializerNotConstant = "OAK-T0501"

// checkGlobalInitializer enforces the constant rule for one top-level
// declaration.
func (tc *TypeChecker) checkGlobalInitializer(decl *ast.VariableDeclaration) {
	if decl == nil || decl.Value == nil {
		return // zero initialization is always constant
	}
	if isConstantExpression(decl.Value) {
		return
	}
	// A warning: script-style programs may still interpret top-level
	// runtime initializers, the strict profile rejects them, and the C
	// backend fails closed on them (never a hidden global constructor).
	d := tc.addTypeWarning(decl, CodeGlobalInitializerNotConstant,
		"global initializer is not a compile-time constant")
	d.AddNote("static storage is initialized before any code runs: literals, arithmetic over literals, primitive casts of constants, and record/array literals of constants are admitted; the C backend rejects anything else")
	d.AddHelp("initialize at the top of main for runtime values — explicit boot-time initialization, never a hidden global constructor")
}

// IsConstantInitializer is the shared constant-initializer judgment —
// exactly the forms the backend emits as C constant expressions at file
// scope; the backend consults the same function it warns with (one
// authority).
func IsConstantInitializer(expr ast.Expression) bool {
	return isConstantExpression(expr)
}

// isConstantExpression is the shared constant-initializer judgment: exactly
// the forms the backend emits as C constant expressions at file scope.
func isConstantExpression(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.IntegerLiteral, *ast.FloatLiteral, *ast.StringLiteral, *ast.Boolean, *ast.FieldAccessorExpression:
		return true
	case *ast.PrefixExpression:
		return isConstantExpression(e.Right)
	case *ast.InfixExpression:
		return isConstantExpression(e.Left) && isConstantExpression(e.Right)
	case *ast.InvocationExpression:
		// Primitive casts of constants are C cast expressions; the named
		// conversions and the float constructors over constants are folded
		// by the backend (IsFoldedConversion); every other call is runtime.
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent || len(e.Arguments) != 1 {
			return false
		}
		switch ident.Value {
		case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "byte", "rune":
			return isConstantExpression(e.Arguments[0])
		}
		if IsFoldedConversion(e) {
			return isConstantExpression(e.Arguments[0])
		}
		return false
	case *ast.RecordLiteral:
		for _, field := range e.FieldOrder {
			if !isConstantExpression(field.Value) {
				return false
			}
		}
		return true
	case *ast.ArrayLiteral:
		for _, element := range e.Elements {
			if !isConstantExpression(element) {
				return false
			}
		}
		return true
	}
	return false
}

// IsFoldedConversion reports whether a call is a conversion the backend
// folds when it appears in a constant initializer: a `{target}_{op}_{source}`
// row other than `checked` (whose result is an ADT value), or the `f32(x)`
// and `f64(x)` constructors (docs/spec/20-types.md section 11.3.4). The fold
// evaluates the call with the interpreter, the first witness of every
// conversion's bit-exact semantics, and emits the resulting literal.
func IsFoldedConversion(call *ast.InvocationExpression) bool {
	ident, isIdent := call.Function.(*ast.Identifier)
	if !isIdent || len(call.Arguments) != 1 {
		return false
	}
	if IsFloatName(ident.Value) {
		return true
	}
	_, op, _, ok := ConversionParts(ident.Value)
	return ok && op != "checked"
}

// FoldedConstantType names the type a folded constant initializer has: the
// conversion's target, the constructor's float type, or the arithmetic type
// the checker recorded for an operator over folded operands.
func (tc *TypeChecker) FoldedConstantType(expr ast.Expression) (string, bool) {
	switch e := expr.(type) {
	case *ast.InvocationExpression:
		ident, isIdent := e.Function.(*ast.Identifier)
		if !isIdent {
			return "", false
		}
		if IsFloatName(ident.Value) {
			return ident.Value, true
		}
		if _, isPrim := conversionPrimitives[ident.Value]; isPrim && len(e.Arguments) == 1 {
			return ident.Value, true
		}
		target, _, _, ok := ConversionParts(ident.Value)
		return target, ok
	case *ast.InfixExpression:
		if name, ok := tc.ArithmeticType(e.Token); ok {
			return name, true
		}
		if name, ok := tc.FoldedConstantType(e.Left); ok {
			return name, true
		}
		return tc.FoldedConstantType(e.Right)
	case *ast.PrefixExpression:
		if name, ok := tc.ArithmeticType(e.Token); ok {
			return name, true
		}
		return tc.FoldedConstantType(e.Right)
	}
	return "", false
}

// ContainsFoldedConversion reports whether a constant initializer needs the
// backend's fold: some conversion or float constructor sits inside it.
func ContainsFoldedConversion(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.PrefixExpression:
		return ContainsFoldedConversion(e.Right)
	case *ast.InfixExpression:
		return ContainsFoldedConversion(e.Left) || ContainsFoldedConversion(e.Right)
	case *ast.InvocationExpression:
		if IsFoldedConversion(e) {
			return true
		}
		for _, arg := range e.Arguments {
			if ContainsFoldedConversion(arg) {
				return true
			}
		}
	}
	return false
}
