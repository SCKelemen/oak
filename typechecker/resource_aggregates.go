package typechecker

// Resource paths through aggregates (docs/spec/50-borrowing.md section 9,
// "Resources through aggregates"): a record field holding a resource is the
// path root.field, an ADT payload holding one is root.$Variant, and paths
// compose through nested records and ADTs, including generic
// instantiations such as Option[Handle] and Result[Handle, E]. A path is a
// location the flow analysis tracks like a named resource.

// resourcePathsOf enumerates the resource-typed paths strictly below root
// for a value of type typ. A resource type itself has no paths below it.
func (tc *TypeChecker) resourcePathsOf(root string, typ Type, resourceTypes map[string]bool) []string {
	if typ == nil || resourceTypes[nominalTypeName(typ)] {
		return nil
	}
	var paths []string
	active := make(map[string]bool)
	var visit func(prefix string, t Type, depth int)
	visit = func(prefix string, t Type, depth int) {
		if t == nil || depth > 8 {
			return
		}
		if resourceTypes[nominalTypeName(t)] {
			paths = append(paths, prefix)
			return
		}
		if record, isRecord := t.(*RecordType); isRecord && record != nil {
			for _, name := range record.orderedFieldNames() {
				visit(prefix+"."+name, record.Fields[name], depth+1)
			}
			return
		}
		name, _, args, isADT := adtInstantiation(t)
		if !isADT || tc.adtTypes == nil {
			return
		}
		def := tc.adtTypes[name]
		if def == nil || active[name] {
			return
		}
		active[name] = true
		defer delete(active, name)
		bindings := make(map[string]Type, len(def.TypeParams))
		for i, parameter := range def.TypeParams {
			if i < len(args) {
				bindings[parameter] = args[i]
			}
		}
		for _, variant := range def.Variants {
			payload := tc.instantiatedVariantPayload(name, variant, bindings)
			if payload == nil {
				continue
			}
			visit(prefix+".$"+variant.Name, payload, depth+1)
		}
	}
	visit(root, typ, 0)
	return paths
}

// resourceLike reports whether a type is a resource or an aggregate with
// resource paths below it: the types a resource contract may govern.
func (tc *TypeChecker) resourceLike(typ Type, resourceTypes map[string]bool) bool {
	if typ == nil {
		return false
	}
	return resourceTypes[nominalTypeName(typ)] || len(tc.resourcePathsOf("r", typ, resourceTypes)) > 0
}

// payloadTypeOfVariant is the instantiated payload type of variant in an ADT
// value of type typ, or nil when typ is not that ADT or the variant carries
// no payload.
func (tc *TypeChecker) payloadTypeOfVariant(typ Type, variantName string) Type {
	name, _, args, isADT := adtInstantiation(typ)
	if !isADT || tc.adtTypes == nil {
		return nil
	}
	def := tc.adtTypes[name]
	if def == nil {
		return nil
	}
	variant, found := tc.findADTVariant(name, variantName)
	if !found || variant == nil {
		return nil
	}
	bindings := make(map[string]Type, len(def.TypeParams))
	for i, parameter := range def.TypeParams {
		if i < len(args) {
			bindings[parameter] = args[i]
		}
	}
	return tc.instantiatedVariantPayload(name, variant, bindings)
}
