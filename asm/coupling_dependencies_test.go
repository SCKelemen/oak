package asm

import "testing"

func TestCouplingDependenciesTrackReplacements(t *testing.T) {
	d := couplingDependencies{symbols: map[string]bool{"machine.a": true, "machine.b": true, "machine.c": true}}
	a, b, c := paramTerm("machine.a", 32), paramTerm("machine.b", 32), paramTerm("machine.c", 32)
	next := binaryTerm("add", a, paramTerm("oak.x", 32))
	sigma := map[string]*term{}
	if d.ready(next, sigma) {
		t.Fatal("an unpaired source symbol is unresolved")
	}
	sigma[a.name] = b
	if d.ready(next, sigma) {
		t.Fatal("the replacement introduces an unpaired symbol")
	}
	sigma[b.name] = c
	if !d.ready(next, sigma) {
		t.Fatal("substitution replaces a once by b; it does not follow b to c")
	}
	actual := substitute(next, sigma)
	mentioned := map[string]bool{}
	collectParams(actual, mentioned)
	if !mentioned[b.name] || mentioned[c.name] {
		t.Fatalf("unexpected substitution dependencies: %v", mentioned)
	}
	delete(sigma, b.name)
	if d.ready(next, sigma) {
		t.Fatal("cached dependencies must observe a rolled-back pairing")
	}
	sigma[a.name] = a
	if !d.ready(next, sigma) {
		t.Fatal("an identity replacement is paired, not recursively unresolved")
	}
	sigma[a.name] = paramTerm("oak.y", 32)
	if !d.ready(next, sigma) {
		t.Fatal("ordinary Oak parameters need no machine pairing")
	}
}

func TestCouplingDependenciesMayDeferErasedNames(t *testing.T) {
	d := couplingDependencies{symbols: map[string]bool{"machine.a": true, "machine.b": true}}
	sigma := map[string]*term{"machine.a": binaryTerm("shl", paramTerm("machine.b", 64), constTerm(32, 64))}
	// A 32-bit use discards the high half. Deferring an early valuation
	// here is safe: the full leaf proof still decides the actual term.
	if d.ready(paramTerm("machine.a", 32), sigma) {
		t.Fatal("raw replacement dependencies must conservatively defer")
	}
}
