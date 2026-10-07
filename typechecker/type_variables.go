package typechecker

// walkTypeVariables visits each binder in a type graph once. Returning true
// from visit stops the walk. All type-variable-bearing constructors must be
// represented here and in Substitution.Apply. Nominal declarations (including
// interface method tables) are not children: their binders have their own scope.
// The visited set is local to this walk; it must never cache mutable inference
// state across substitutions or monomorphic transactions.
func walkTypeVariables(root Type, visit func(*TypeVar) bool) bool {
	pending := []Type{root}
	seen := make(map[Type]bool)
	pushReverse := func(types []Type) {
		for i := len(types) - 1; i >= 0; i-- {
			pending = append(pending, types[i])
		}
	}
	for len(pending) != 0 {
		last := len(pending) - 1
		current := pending[last]
		pending = pending[:last]
		// Only known pointer-backed constructors enter the map. Unknown
		// implementations may be non-comparable; they remain opaque.
		switch current.(type) {
		case *TypeVar, *RecordType, *FunctionType, *ArrayType, *GenericType,
			*UnionType, *IntersectionType, *NarrowedADTVariantType,
			*BufferType, *AtomicType, *CFnType:
		default:
			continue
		}
		if seen[current] {
			continue
		}
		seen[current] = true
		switch t := current.(type) {
		case *TypeVar:
			if t != nil && visit(t) {
				return true
			}
		case *RecordType:
			if t == nil {
				continue
			}
			names := t.orderedFieldNames()
			for i := len(names) - 1; i >= 0; i-- {
				pending = append(pending, t.Fields[names[i]])
			}
		case *FunctionType:
			if t != nil {
				pending = append(pending, t.ReturnType)
				pushReverse(t.Parameters)
			}
		case *ArrayType:
			if t != nil {
				pending = append(pending, t.ElementType)
			}
		case *GenericType:
			if t != nil {
				pushReverse(t.TypeArgs)
			}
		case *UnionType:
			if t != nil {
				pushReverse(t.Types)
			}
		case *IntersectionType:
			if t != nil {
				pushReverse(t.Types)
			}
		case *NarrowedADTVariantType:
			if t != nil {
				pushReverse(t.TypeArgs)
			}
		case *BufferType:
			if t != nil {
				pending = append(pending, t.Element)
			}
		case *AtomicType:
			if t != nil {
				pending = append(pending, t.Element)
			}
		case *CFnType:
			if t != nil {
				pending = append(pending, t.ReturnType)
				pushReverse(t.Parameters)
			}
		}
	}
	return false
}

func (sub Substitution) applyTypeList(types []Type) []Type {
	if types == nil {
		return nil
	}
	out := make([]Type, len(types))
	for i, typ := range types {
		out[i] = sub.Apply(typ)
	}
	return out
}
