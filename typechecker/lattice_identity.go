package typechecker

import "reflect"

// latticeAtomIdentical is the equality decision required by the free
// distributive lattice's opaque atoms.  It is deliberately narrower than
// Type.Equals: several Equals implementations also answer compatibility
// questions (a narrowed ADT case against its parent, or a concrete struct
// against a semantic record shape), and compatibility is not an equivalence
// relation.  Using it as Lean's DecidableEq premise can therefore destroy
// transitivity of IsSubtype.
//
// Every Type implementation in this package is handled below.  A future
// implementation fails closed to object identity until its semantic identity
// is added explicitly; two separately allocated unknown values can never be
// collapsed into one lattice atom by accident.
func latticeAtomIdentical(left, right Type) bool {
	if left == nil || right == nil {
		return left == nil && right == nil
	}
	leftValue := reflect.ValueOf(left)
	rightValue := reflect.ValueOf(right)
	if leftValue.Type() != rightValue.Type() {
		return false
	}
	if leftValue.Kind() == reflect.Ptr && (leftValue.IsNil() || rightValue.IsNil()) {
		return leftValue.IsNil() && rightValue.IsNil()
	}

	switch left := left.(type) {
	case *PrimitiveType:
		right := right.(*PrimitiveType)
		return normalizePrimitiveName(left.Name) == normalizePrimitiveName(right.Name) &&
			left.Refinement == right.Refinement
	case *StringType:
		return left.encoding() == right.(*StringType).encoding()
	case *BoolType, *UnitType, *NeverType, *AnyType:
		return true
	case *ADTType:
		return left.Name == right.(*ADTType).Name
	case *NarrowedADTVariantType:
		right := right.(*NarrowedADTVariantType)
		return left.ADTName == right.ADTName && left.VariantName == right.VariantName &&
			latticeTypeListsIdentical(left.TypeArgs, right.TypeArgs, false)
	case *RecordType:
		return latticeRecordsIdentical(left, right.(*RecordType))
	case *InterfaceType:
		// Interfaces are nominal. Methods are declaration metadata once the
		// interface name has resolved.
		return left.Name == right.(*InterfaceType).Name
	case *UnionType:
		return latticeTypeListsIdentical(left.Types, right.(*UnionType).Types, true)
	case *IntersectionType:
		return latticeTypeListsIdentical(left.Types, right.(*IntersectionType).Types, true)
	case *FieldAccessorType:
		return left.Field == right.(*FieldAccessorType).Field
	case *FunctionType:
		right := right.(*FunctionType)
		return left.Variadic == right.Variadic &&
			latticeTypeListsIdentical(left.Parameters, right.Parameters, false) &&
			latticeAtomIdentical(left.ReturnType, right.ReturnType)
	case *ArrayType:
		right := right.(*ArrayType)
		return left.Length == right.Length && left.IsSlice == right.IsSlice &&
			left.IsSpan == right.IsSpan && left.Align == right.Align &&
			latticeAtomIdentical(left.ElementType, right.ElementType)
	case *GenericType:
		right := right.(*GenericType)
		return left.Name == right.Name &&
			latticeTypeListsIdentical(left.TypeArgs, right.TypeArgs, false)
	case *TypeVar:
		return left == right.(*TypeVar)
	case *constraintSetType:
		right := right.(*constraintSetType)
		if len(left.Requirements) != len(right.Requirements) {
			return false
		}
		for i := range left.Requirements {
			if left.Requirements[i] != right.Requirements[i] {
				return false
			}
		}
		return true
	case *CType:
		return left.Name == right.(*CType).Name
	case *SimdType:
		return left.Name == right.(*SimdType).Name
	case *MmioRegisterType:
		right := right.(*MmioRegisterType)
		return left.Width == right.Width && left.Access == right.Access
	case *BufferType:
		right := right.(*BufferType)
		return left.custody() == right.custody() &&
			latticeAtomIdentical(left.Element, right.Element)
	case *AtomicType:
		return latticeAtomIdentical(left.Element, right.(*AtomicType).Element)
	case *CFnType:
		right := right.(*CFnType)
		return latticeTypeListsIdentical(left.Parameters, right.Parameters, false) &&
			latticeAtomIdentical(left.ReturnType, right.ReturnType)
	case *ConstIntType:
		return left.Value == right.(*ConstIntType).Value
	default:
		return leftValue.Kind() == reflect.Ptr && leftValue.Pointer() == rightValue.Pointer()
	}
}

func latticeRecordsIdentical(left, right *RecordType) bool {
	leftNominal := left.Struct && left.Name != ""
	rightNominal := right.Struct && right.Name != ""
	if leftNominal || rightNominal {
		return leftNominal && rightNominal && left.Name == right.Name
	}
	if left.Open != right.Open || len(left.Fields) != len(right.Fields) {
		return false
	}
	for name, leftType := range left.Fields {
		rightType, ok := right.Fields[name]
		if !ok || !latticeAtomIdentical(leftType, rightType) {
			return false
		}
	}
	return true
}

func latticeTypeListsIdentical(left, right []Type, unordered bool) bool {
	if len(left) != len(right) {
		return false
	}
	if !unordered {
		for i := range left {
			if !latticeAtomIdentical(left[i], right[i]) {
				return false
			}
		}
		return true
	}

	used := make([]bool, len(right))
	for _, leftType := range left {
		matched := false
		for i, rightType := range right {
			if !used[i] && latticeAtomIdentical(leftType, rightType) {
				used[i] = true
				matched = true
				break
			}
		}
		if !matched {
			return false
		}
	}
	return true
}
