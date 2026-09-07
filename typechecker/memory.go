package typechecker

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
)

// AtomicType is the checked type of Atomic[T]. Atomicity is a property of
// accesses to the cell; values loaded from the cell have the ordinary element
// type. v1 deliberately accepts only fixed-width integer carriers.
type AtomicType struct {
	Element Type
}

func (t *AtomicType) String() string {
	if t == nil || t.Element == nil {
		return "Atomic[?]"
	}
	return "Atomic[" + t.Element.String() + "]"
}

func (t *AtomicType) Equals(other Type) bool {
	o, ok := other.(*AtomicType)
	if !ok || t == nil || o == nil || t.Element == nil || o.Element == nil {
		return false
	}
	return t.Element.Equals(o.Element)
}

func IsAtomicCarrier(typ Type) bool {
	prim, ok := typ.(*PrimitiveType)
	if !ok || prim == nil {
		return false
	}
	switch normalizePrimitiveName(prim.Name) {
	case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
		return true
	default:
		return false
	}
}

func NewAtomicType(element Type) (*AtomicType, error) {
	if !IsAtomicCarrier(element) {
		if element == nil {
			return nil, fmt.Errorf("Atomic requires a fixed-width integer carrier")
		}
		return nil, fmt.Errorf("Atomic[%s] is not supported; v1 requires a fixed-width integer carrier", element)
	}
	return &AtomicType{Element: element}, nil
}

func ContainsAtomicStorage(typ Type) bool {
	switch t := typ.(type) {
	case *AtomicType:
		return true
	case *ArrayType:
		return t != nil && ContainsAtomicStorage(t.ElementType)
	case *RecordType:
		if t == nil {
			return false
		}
		for _, field := range t.Fields {
			if ContainsAtomicStorage(field) {
				return true
			}
		}
	case *GenericType:
		if t == nil {
			return false
		}
		for _, arg := range t.TypeArgs {
			if ContainsAtomicStorage(arg) {
				return true
			}
		}
	}
	return false
}

func atomicCellIdentifier(expr ast.Expression) bool {
	_, ok := expr.(*ast.Identifier)
	return ok
}

func (tc *TypeChecker) checkAtomicValueArgument(name string, arg ast.Expression, expected Type) bool {
	valueType := tc.checkExpression(arg, expected)
	if valueType != nil && !tc.isAssignable(valueType, expected) {
		tc.addError(arg, "%s value must be %s, got %s", name, expected, valueType)
		return false
	}
	return true
}

// checkAtomicInvocation types every source-level atomic builtin from the
// semantic descriptor in semir. The first operand is an identifier naming a
// cell, never a temporary value. Strong compare-exchange takes expected and
// desired carrier values and returns the value observed by the atomic compare.
func (tc *TypeChecker) checkAtomicInvocation(name string, expr *ast.InvocationExpression) (Type, bool) {
	spec, recognized := semir.LookupAtomicBuiltin(name)
	if !recognized {
		return nil, false
	}
	if len(expr.Arguments) != int(spec.Arity) {
		tc.addError(expr, "%s expects %d arguments, got %d", name, spec.Arity, len(expr.Arguments))
		if spec.ReturnsValue() {
			return nil, true
		}
		return &UnitType{}, true
	}
	if spec.Kind == semir.AtomicBuiltinFence {
		return &UnitType{}, true
	}
	if !atomicCellIdentifier(expr.Arguments[0]) {
		tc.addError(expr.Arguments[0], "%s requires a named Atomic[T] cell; temporaries and copied cells are forbidden", name)
		return nil, true
	}
	cellType := tc.checkExpression(expr.Arguments[0])
	cell, ok := cellType.(*AtomicType)
	if !ok || cell == nil || cell.Element == nil {
		if cellType != nil {
			tc.addError(expr.Arguments[0], "%s first argument must be Atomic[T], got %s", name, cellType)
		}
		return nil, true
	}

	switch spec.Kind {
	case semir.AtomicBuiltinStore, semir.AtomicBuiltinFetchAdd:
		if !tc.checkAtomicValueArgument(name, expr.Arguments[1], cell.Element) {
			return nil, true
		}
	case semir.AtomicBuiltinCompareExchange:
		okExpected := tc.checkAtomicValueArgument(name+" expected", expr.Arguments[1], cell.Element)
		okDesired := tc.checkAtomicValueArgument(name+" desired", expr.Arguments[2], cell.Element)
		if !okExpected || !okDesired {
			return nil, true
		}
	}

	// Defensive executable check that the source descriptor remains inside the
	// formally specified legality relation. CAS validates the related order pair.
	if !spec.Legal() {
		if spec.Kind == semir.AtomicBuiltinCompareExchange {
			tc.addError(expr, "internal compare-exchange builtin %s has illegal orders success=%s failure=%s", name, spec.Order, spec.FailureOrder)
		} else {
			tc.addError(expr, "internal atomic builtin %s has illegal order %s", name, spec.Order)
		}
		return nil, true
	}

	if spec.ReturnsValue() {
		return cell.Element, true
	}
	return &UnitType{}, true
}
