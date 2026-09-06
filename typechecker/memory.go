package typechecker

import "fmt"

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

// NewAtomicType is the single checked constructor used by parser lowering and
// future generic-type elaboration. Keeping validation here avoids having one
// source-syntax path accidentally admit carriers another path rejects.
func NewAtomicType(element Type) (*AtomicType, error) {
	if !IsAtomicCarrier(element) {
		if element == nil {
			return nil, fmt.Errorf("Atomic requires a fixed-width integer carrier")
		}
		return nil, fmt.Errorf("Atomic[%s] is not supported; v1 requires a fixed-width integer carrier", element)
	}
	return &AtomicType{Element: element}, nil
}
