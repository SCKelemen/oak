package typechecker

// Static globals (docs/spec/60-effects-allocation.md section 10a,
// MISRA/Power-of-Ten style): a top-level binding is static storage, and its
// initializer must be a compile-time constant — literals, arithmetic over
// literals, primitive casts of constants, the named conversions and float
// constructors applied to constants (folded by the compiler, ml finding
// F19), record/array literals of constants, or nothing (zero
// initialization). Runtime initialization is written explicitly in main,
// never hidden in global constructors.

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
)

// CodeGlobalInitializerNotConstant rejects top-level initializers the C
// backend cannot place in static storage as constant expressions.
const CodeGlobalInitializerNotConstant = "OAK-T0501"

// CodeMeasuredConstant rejects a malformed measured constant
// (docs/spec/60-effects-allocation.md section 10b): a range that is not
// an integer type's, a pinned value outside it, or an assignment to it.
const CodeMeasuredConstant = "OAK-T0502"

// integerRanges are the value ranges of the fixed-width integer types a
// measured constant may have.
var integerRanges = map[string][2]int64{
	"u8": {0, 255}, "u16": {0, 65535}, "u32": {0, 4294967295}, "u64": {0, 9223372036854775807},
	"i8": {-128, 127}, "i16": {-32768, 32767}, "i32": {-2147483648, 2147483647}, "i64": {-9223372036854775808, 9223372036854775807},
}

// MeasuredConstant is one measured constant as declared: its Oak name, its
// integer type, the inclusive range, and the pinned value the program
// runs with when none is supplied.
type MeasuredConstant struct {
	Name   string
	Type   string
	Lo, Hi int64
	Pinned int64
}

// MeasuredConstants lists the program's measured constants in declaration
// order — the knobs a load-time value may turn, for vet and the extraction.
func (tc *TypeChecker) MeasuredConstants() []MeasuredConstant {
	return append([]MeasuredConstant(nil), tc.measured...)
}

// IsMeasured reports whether name is a measured constant.
func (tc *TypeChecker) IsMeasured(name string) bool {
	for _, m := range tc.measured {
		if m.Name == name {
			return true
		}
	}
	return false
}

// pinnedInteger reads a measured constant's initializer: an integer
// literal, optionally negated or wrapped in its own type's constructor.
func pinnedInteger(expr ast.Expression, typ string) (int64, bool) {
	switch e := expr.(type) {
	case *ast.IntegerLiteral:
		return e.Value, true
	case *ast.PrefixExpression:
		if e.Operator == "-" {
			if v, ok := pinnedInteger(e.Right, typ); ok {
				return -v, true
			}
		}
	case *ast.InvocationExpression:
		if ident, isIdent := e.Function.(*ast.Identifier); isIdent && ident.Value == typ && len(e.Arguments) == 1 {
			return pinnedInteger(e.Arguments[0], typ)
		}
	}
	return 0, false
}

// checkMeasured validates a measured constant (docs/spec/60-effects-allocation.md
// section 10b): an integer type, a range inside the type's, a pinned
// initializer inside the range. A valid one is recorded; it is never a
// constant later initializers fold, since its value is the load's.
func (tc *TypeChecker) checkMeasured(decl *ast.VariableDeclaration) {
	if decl == nil || decl.Measured == nil || decl.Name == nil {
		return
	}
	typeName, isIdent := decl.Type.(*ast.Identifier)
	bounds, integer := integerRanges[""]
	if isIdent {
		bounds, integer = integerRanges[typeName.Value]
	}
	if !isIdent || !integer {
		tc.addTypeDiagnostic(decl, CodeMeasuredConstant, fmt.Sprintf("measured constant %s needs a fixed-width integer type", decl.Name.Value))
		return
	}
	lo, hi := decl.Measured.Lo, decl.Measured.Hi
	if lo > hi || lo < bounds[0] || hi > bounds[1] {
		tc.addTypeDiagnostic(decl, CodeMeasuredConstant, fmt.Sprintf("measured constant %s: the range %d..%d is not a range of %s", decl.Name.Value, lo, hi, typeName.Value))
		return
	}
	if decl.Value == nil {
		tc.addTypeDiagnostic(decl, CodeMeasuredConstant, fmt.Sprintf("measured constant %s needs a pinned value, its initializer", decl.Name.Value))
		return
	}
	pinned, ok := pinnedInteger(decl.Value, typeName.Value)
	if !ok {
		tc.addTypeDiagnostic(decl, CodeMeasuredConstant, fmt.Sprintf("measured constant %s: the pinned value is an integer literal", decl.Name.Value))
		return
	}
	if pinned < lo || pinned > hi {
		tc.addTypeDiagnostic(decl, CodeMeasuredConstant, fmt.Sprintf("measured constant %s: the pinned value %d is outside %d..%d", decl.Name.Value, pinned, lo, hi))
		return
	}
	tc.measured = append(tc.measured, MeasuredConstant{Name: decl.Name.Value, Type: typeName.Value, Lo: lo, Hi: hi, Pinned: pinned})
}

// checkGlobalInitializer enforces the constant rule for one top-level
// declaration.
func (tc *TypeChecker) checkGlobalInitializer(decl *ast.VariableDeclaration) {
	if decl == nil || decl.Value == nil {
		return // zero initialization is always constant
	}
	if _, isTargetConstant := TargetConstantCall(decl.Value); isTargetConstant {
		// A target constant is a C constant expression on the target — the
		// header's definition — so static storage holds it; its value is
		// unknown to Oak, so it is not a constant later initializers may
		// read (a C `static const` is not a constant expression either).
		return
	}
	if decl.Measured != nil {
		// A measured constant's initializer is its pinned value, a literal;
		// the value the program runs with is the load's, so it is not a
		// constant later initializers may fold (checkMeasured).
		return
	}
	if tc.IsConstantInitializer(decl.Value) {
		// A constant global may be read by the constant initializers that
		// follow it (a derived constant such as TOTAL = ROWS * COLS).
		if decl.Name != nil {
			if tc.constantGlobals == nil {
				tc.constantGlobals = map[string]bool{}
			}
			tc.constantGlobals[decl.Name.Value] = true
		}
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
// scope or folds; the backend consults the same function it warns with (one
// authority). A read of an earlier constant global is constant too, and is
// folded with it.
func (tc *TypeChecker) IsConstantInitializer(expr ast.Expression) bool {
	return IsConstantInitializerIn(expr, tc.constantGlobals)
}

// IsConstantInitializer without a checker admits the literal forms only.
func IsConstantInitializer(expr ast.Expression) bool {
	return IsConstantInitializerIn(expr, nil)
}

// IsConstantInitializerIn is the judgment relative to the set of constant
// globals declared earlier: the backend, which emits globals in declaration
// order, passes the set it has emitted so far.
func IsConstantInitializerIn(expr ast.Expression, constants map[string]bool) bool {
	return isConstantExpression(expr, constants)
}

// isConstantExpression is the shared constant-initializer judgment: exactly
// the forms the backend emits as C constant expressions at file scope or
// folds.
func isConstantExpression(expr ast.Expression, constants map[string]bool) bool {
	isConstantExpression := func(e ast.Expression) bool { return isConstantExpression(e, constants) }
	switch e := expr.(type) {
	case *ast.IntegerLiteral, *ast.FloatLiteral, *ast.StringLiteral, *ast.Boolean, *ast.FieldAccessorExpression:
		return true
	case *ast.Identifier:
		return constants[e.Value]
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
		case "u8", "u16", "u32", "u64", "u128", "i8", "i16", "i32", "i64", "byte", "rune":
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
	case *ast.Identifier:
		// A read of an earlier constant global has that global's type.
		if tc.globalEnv != nil {
			if scheme, ok := tc.globalEnv.Get(e.Value); ok && scheme != nil {
				if prim, isPrim := scheme.Type.(*PrimitiveType); isPrim {
					return prim.Name, true
				}
			}
		}
		return "", false
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
// backend's fold: some conversion, float constructor, or read of an earlier
// constant global sits inside it.
func ContainsFoldedConversion(expr ast.Expression) bool {
	switch e := expr.(type) {
	case *ast.Identifier:
		return true
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

// ForeignBorrowCallee reports whether an expression is the callee of an
// inbound buffer borrow, `c.borrow[T]` or `c.borrow_mut[T]`, so the
// lowering keeps its shape instead of treating the index as element access.
func ForeignBorrowCallee(fn ast.Expression) bool {
	_, _, ok := foreignBorrowAccess(fn)
	return ok
}
