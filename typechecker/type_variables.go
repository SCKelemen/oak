package typechecker

// walkTypeVariables visits each binder in a type graph once. Returning true
// from visit stops the walk. All type-variable-bearing constructors must be
// represented here and in Substitution.Apply. Nominal declarations (including
// interface method tables) are not children: their binders have their own scope.
// The visited set is local to this walk; it must never cache mutable inference
// state across substitutions or monomorphic transactions.
func walkTypeVariables(root Type, visit func(*TypeVar) bool) bool {
	// Keep ordinary small signatures allocation-free apart from the caller's
	// result. The bounded linear identity set spills to a map for larger
	// graphs; the bound is fixed, so traversal remains linear in graph size.
	if variable, ok := root.(*TypeVar); ok {
		return variable != nil && visit(variable)
	}
	var initial [32]Type
	pending := append(initial[:0], root)
	var smallSeen [16]Type
	smallCount := 0
	var seen map[Type]bool
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
		if seen != nil {
			if seen[current] {
				continue
			}
			seen[current] = true
		} else {
			duplicate := false
			for i := 0; i < smallCount; i++ {
				if smallSeen[i] == current {
					duplicate = true
					break
				}
			}
			if duplicate {
				continue
			}
			if smallCount < len(smallSeen) {
				smallSeen[smallCount] = current
				smallCount++
			} else {
				seen = make(map[Type]bool, 2*len(smallSeen))
				for _, previous := range smallSeen {
					seen[previous] = true
				}
				seen[current] = true
			}
		}
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
