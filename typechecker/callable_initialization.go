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
	seen := make(map[Type]bool)
	adts := make(map[string]bool)
	var visit func(Type, string) (string, bool)
	visit = func(typ Type, path string) (string, bool) {
		if typ == nil || seen[typ] {
			return "", false
		}
		seen[typ] = true
		switch t := typ.(type) {
		case *FunctionType, *CFnType:
			return path, true
		case *RecordType:
			for _, name := range t.orderedFieldNames() {
				if p, found := visit(t.Fields[name], path+"."+name); found {
					return p, true
				}
			}
		case *ArrayType:
			if !t.IsSlice && !t.IsSpan && t.Length != 0 {
				return visit(t.ElementType, path+"[]")
			}
		case *UnionType:
			for _, member := range t.Types {
				if p, found := visit(member, path); found {
					return p, true
				}
			}
		case *IntersectionType:
			for _, member := range t.Types {
				if p, found := visit(member, path); found {
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
				return visit(record, path)
			}
			if resolved, exists := tc.env.GetType(name); exists && resolved != typ {
				if _, unresolved := resolved.(*ADTType); !unresolved {
					return visit(resolved, path)
				}
			}
			if tc.adtTypes[name] == nil || adts[name] {
				return "", false
			}
			adts[name] = true
			defer delete(adts, name)
			def := tc.adtTypes[name]
			bindings := make(map[string]Type)
			for i, parameter := range def.TypeParams {
				if i < len(args) {
					bindings[parameter] = args[i]
				}
			}
			for _, variant := range def.Variants {
				if p, found := visit(tc.instantiatedVariantPayload(name, variant, bindings), path+"::"+variant.Name); found {
					return p, true
				}
			}
		}
		return "", false
	}
	return visit(typ, "")
}
