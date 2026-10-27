package typechecker

// signatureTypesIdentical implements the exact, monomorphic signature
// judgment (docs/spec/83-modules.md §6.3). Compatibility is not enough:
// a nominal struct and its shape, or a narrowed ADT and its parent, may be
// compatible without having the same identity. Reuse the closed identity
// policy already required by the lattice instead of inventing a second one.
// This is not assignability, unification, ABI equivalence, or coercion.
func signatureTypesIdentical(actual, promised Type) bool {
	return actual != nil && promised != nil && latticeAtomIdentical(actual, promised)
}
