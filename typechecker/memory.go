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

// IsAtomicCarrier reports whether typ has the unambiguous fixed-width machine
// representation required by the first atomic surface. Native int/uint and
// pointers are intentionally excluded until target-width and provenance rules
// are part of the atomic contract.
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

// NewAtomicType is the single checked constructor used by type elaboration.
func NewAtomicType(element Type) (*AtomicType, error) {
	if !IsAtomicCarrier(element) {
		if element == nil {
			return nil, fmt.Errorf("Atomic requires a fixed-width integer carrier")
		}
		return nil, fmt.Errorf("Atomic[%s] is not supported; v1 requires a fixed-width integer carrier", element)
	}
	return &AtomicType{Element: element}, nil
}

// ContainsAtomicStorage detects atomic cell identity nested inside another
// value. v1 permits Atomic[T] only as a direct local/package cell: aggregate
// embedding and by-value function transport remain rejected until Oak has a
// non-copy storage/borrow contract for them.
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

// checkAtomicInvocation types every source-level atomic builtin from the
// semantic descriptor in semir. The first operand is an identifier naming a
// cell, never a temporary value: this preserves storage identity and prevents
// an implicit atomic copy at the call boundary.
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

	if spec.Kind == semir.AtomicBuiltinStore || spec.Kind == semir.AtomicBuiltinFetchAdd {
		valueType := tc.checkExpression(expr.Arguments[1], cell.Element)
		if valueType != nil && !tc.isAssignable(valueType, cell.Element) {
			tc.addError(expr.Arguments[1], "%s value must be %s, got %s", name, cell.Element, valueType)
			return nil, true
		}
	}

	// This is also a defensive executable check that the source descriptor
	// remains inside the formally specified legality matrix.
	if !semir.LegalAtomicOrder(spec.Operation, spec.Order) {
		tc.addError(expr, "internal atomic builtin %s has illegal order %s", name, spec.Order)
		return nil, true
	}

	if spec.ReturnsValue() {
		return cell.Element, true
	}
	return &UnitType{}, true
}
