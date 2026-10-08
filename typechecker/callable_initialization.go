package typechecker

// CodeCallableInitializer reports storage for which there is no callable
// zero value. A null or indeterminate code pointer is not an Oak function.
const CodeCallableInitializer = "OAK-T0801"

// zeroContainsCallable checks the values a value-less declaration would
// construct, not the mere occurrence of a function type in a signature.
// Aliases and record templates have already been resolved by the checker.
// Empty owned arrays and borrowed views/spans construct no element values.
// Sum storage is conservatively checked across its payload alternatives:
// implicit initialization must not invent a function in any stored payload.
func (tc *TypeChecker) zeroContainsCallable(typ Type) (string, bool) {
	type storageNode struct {
		typ     Type
		context string
	}
	seen := make(map[storageNode]bool)
	context := ""
	adts := make(map[string]bool)
	var visit func(Type, string, map[string]bool) (string, bool)
	visit = func(typ Type, path string, bindings map[string]bool) (string, bool) {
		if typ == nil {
			return "", false
		}
		if parameter, ok := typ.(*ADTType); ok {
			if callable, bound := bindings[parameter.Name]; bound {
				return path, callable
			}
		}
		node := storageNode{typ, context}
		if seen[node] {
			return "", false
		}
		seen[node] = true
		defer delete(seen, node)
		switch t := typ.(type) {
		case *FunctionType, *CFnType:
			return path, true
		case *RecordType:
			for _, name := range t.orderedFieldNames() {
				if p, found := visit(t.Fields[name], path+"."+name, bindings); found {
					return p, true
				}
			}
		case *ArrayType:
			if !t.IsSlice && !t.IsSpan && t.Length != 0 {
				return visit(t.ElementType, path+"[]", bindings)
			}
		case *UnionType:
			for _, member := range t.Types {
				if p, found := visit(member, path, bindings); found {
					return p, true
				}
			}
		case *IntersectionType:
			for _, member := range t.Types {
				if p, found := visit(member, path, bindings); found {
					return p, true
				}
			}
		default:
			name, _, args, ok := adtInstantiation(typ)
			if !ok {
				return "", false
			}
			// Template substitution spells nested concrete records by their
			// mangled name; those resolve through the instantiation cache,
			// not necessarily the ordinary named-type environment.
			if record := tc.recordInstantiationCache[name]; record != nil {
				return visit(record, path, bindings)
			}
			if resolved, exists := tc.env.GetType(name); exists && resolved != typ {
				if _, unresolved := resolved.(*ADTType); !unresolved {
					return visit(resolved, path, bindings)
				}
			}
			def := tc.adtTypes[name]
			if def == nil {
				return "", false
			}
			// Abstract each type argument to callable-storage presence.
			// This finite state space terminates even for F[F[T]], while
			// revisiting F with a changed argument cannot hide a callable.
			next := make(map[string]bool)
			key := name + ":"
			for i, parameter := range def.TypeParams {
				callable := false
				if i < len(args) {
					_, callable = visit(args[i], path, bindings)
				}
				next[parameter] = callable
				if callable {
					key += "1"
				} else {
					key += "0"
				}
			}
			if adts[key] {
				return "", false
			}
			adts[key] = true
			defer delete(adts, key)
			previous := context
			context = key
			defer func() { context = previous }()
			for _, variant := range def.Variants {
				// Keep parameter names symbolic; bindings carry only the
				// storage property, never infinitely expanding types.
				payload := tc.instantiatedVariantPayload(name, variant, nil)
				if p, found := visit(payload, path+"::"+variant.Name, next); found {
					return p, true
				}
			}
		}
		return "", false
	}
	return visit(typ, "", nil)
}
