package optir

import "reflect"

// SnapshotCFG returns an owned deep copy and its exact verified fingerprint.
// The caller must not mutate cfg concurrently with copying. Published graph
// consumers must treat the snapshot as immutable; this is not proof authority.
func SnapshotCFG(cfg CFG) (CFG, string, error) {
	snapshot := cloneCFG(cfg)
	fingerprint, err := FingerprintCFG(snapshot)
	if err != nil {
		return CFG{}, "", err
	}
	return snapshot, fingerprint, nil
}

// ExactCFGEqual compares every ordered semantic field after canonicalizing the
// nil/empty slice distinction used by builders. It validates both operands and
// does not rely on a digest collision assumption. This is identity equality,
// not observational program equivalence.
func ExactCFGEqual(left, right CFG) (bool, error) {
	if err := Verify(left); err != nil {
		return false, err
	}
	if err := Verify(right); err != nil {
		return false, err
	}
	return reflect.DeepEqual(cloneCFG(left), cloneCFG(right)), nil
}

// SnapshotFunction returns an owned deep copy and its exact structured-OptIR
// fingerprint. Project validates both the structured definition and the CFG it
// deterministically denotes before the snapshot can enter an artifact graph.
// This identity is not a semantic-verification verdict.
func SnapshotFunction(function Function) (Function, string, error) {
	snapshot := cloneFunction(function)
	fingerprint, err := FingerprintFunction(snapshot)
	if err != nil {
		return Function{}, "", err
	}
	return snapshot, fingerprint, nil
}

func cloneFunction(function Function) Function {
	function.Parameters = cloneValues(function.Parameters)
	function.Results = append([]Type(nil), function.Results...)
	function.Body = cloneRegion(function.Body)
	function.Facts = cloneFacts(function.Facts)
	return function
}

func cloneRegion(region Region) Region {
	nodes := region.Nodes
	region.Arguments = cloneValues(region.Arguments)
	region.Yield = append([]ValueID(nil), region.Yield...)
	region.Nodes = make([]Node, len(nodes))
	for i, node := range nodes {
		if node.Operation != nil {
			operation := cloneOperation(*node.Operation)
			region.Nodes[i].Operation = &operation
		}
		if node.If != nil {
			branch := *node.If
			branch.Results = cloneValues(branch.Results)
			branch.Then = cloneRegion(branch.Then)
			branch.Else = cloneRegion(branch.Else)
			region.Nodes[i].If = &branch
		}
		if node.While != nil {
			loop := *node.While
			loop.Initial = append([]ValueID(nil), loop.Initial...)
			loop.Results = cloneValues(loop.Results)
			loop.Condition = cloneRegion(loop.Condition)
			loop.Body = cloneRegion(loop.Body)
			region.Nodes[i].While = &loop
		}
	}
	return region
}
