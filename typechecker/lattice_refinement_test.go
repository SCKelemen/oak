package typechecker

import (
	"fmt"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

// The type-lattice decision against its Lean transliteration
// (spec/lean/Oak/TypeLatticeRefinement.lean): normalize a corpus containing
// every lattice constructor with the live Go latticeDNFOf, decide selected
// orderings with the live Go IsSubtype, and render both results as equations
// checked by Lean's kernel. The test requires those exact equations in the
// proof module, so drift across the covered constructor and decision cases is
// detected immediately.
func TestTypeLatticeMatchesLeanTransliteration(t *testing.T) {
	lean, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "TypeLatticeRefinement.lean"))
	if err != nil {
		t.Fatal(err)
	}
	text := string(lean)

	p := &PrimitiveType{Name: "p"}
	q := &PrimitiveType{Name: "q"}
	r := &PrimitiveType{Name: "r"}
	pOrQ := &UnionType{Types: []Type{p, q}}
	pAndQ := &IntersectionType{Types: []Type{p, q}}
	distributedLeft := &IntersectionType{Types: []Type{
		&UnionType{Types: []Type{p, q}},
		&UnionType{Types: []Type{p, r}},
	}}
	distributedRight := &UnionType{Types: []Type{
		p,
		&IntersectionType{Types: []Type{q, r}},
	}}

	types := []Type{
		&NeverType{},
		&AnyType{},
		p,
		pOrQ,
		pAndQ,
		distributedLeft,
		distributedRight,
		&IntersectionType{Types: []Type{p, p, q}},
		&UnionType{Types: []Type{p, q, r}},
		&IntersectionType{Types: []Type{p, q, r}},
		&UnionType{},
		&IntersectionType{},
	}

	var rendered []string
	for _, typ := range types {
		rendered = append(rendered, fmt.Sprintf(
			"example : dnfOf (%s : LatticeTy String) = %s := by decide",
			renderLatticeType(t, typ), renderLatticeDNF(t, latticeDNFOf(typ)),
		))
	}

	orderings := [][2]Type{
		{&NeverType{}, p},
		{p, &AnyType{}},
		{&AnyType{}, p},
		{p, &NeverType{}},
		{p, p},
		{p, pOrQ},
		{pOrQ, p},
		{pAndQ, p},
		{p, pAndQ},
		{distributedLeft, distributedRight},
		{distributedRight, distributedLeft},
		{&IntersectionType{Types: []Type{p, q, r}}, pAndQ},
		{pOrQ, &UnionType{Types: []Type{p, q, r}}},
		{&UnionType{Types: []Type{p, q, r}}, pOrQ},
	}
	for _, pair := range orderings {
		rendered = append(rendered, fmt.Sprintf(
			"example : decide (dnfOf (%s : LatticeTy String)) (dnfOf (%s : LatticeTy String)) = %v := by decide",
			renderLatticeType(t, pair[0]), renderLatticeType(t, pair[1]), IsSubtype(pair[0], pair[1]),
		))
	}

	var missing []string
	for _, line := range rendered {
		if !strings.Contains(text, line) {
			missing = append(missing, line)
		}
	}
	if len(missing) != 0 {
		t.Fatalf("%d lattice decision(s) not stated in spec/lean/Oak/TypeLatticeRefinement.lean — update the Lean file or the implementation:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}

// renderLatticeType folds Go's n-ary constructors into the binary Lean
// syntax. Empty joins and meets become bottom and top respectively.
func renderLatticeType(t *testing.T, typ Type) string {
	t.Helper()
	switch typ := typ.(type) {
	case *NeverType:
		return ".never"
	case *AnyType:
		return ".any"
	case *PrimitiveType:
		return fmt.Sprintf("(.atom %s)", strconv.Quote(typ.Name))
	case *UnionType:
		return renderLatticeFold(t, ".union", ".never", typ.Types)
	case *IntersectionType:
		return renderLatticeFold(t, ".inter", ".any", typ.Types)
	default:
		t.Fatalf("lattice refinement corpus contains unsupported atom type %T", typ)
		return ""
	}
}

func renderLatticeFold(t *testing.T, constructor, identity string, members []Type) string {
	t.Helper()
	if len(members) == 0 {
		return identity
	}
	result := renderLatticeType(t, members[0])
	for _, member := range members[1:] {
		result = fmt.Sprintf("(%s %s %s)", constructor, result, renderLatticeType(t, member))
	}
	return result
}

func renderLatticeDNF(t *testing.T, dnf latticeDNF) string {
	t.Helper()
	clauses := make([]string, 0, len(dnf))
	for _, clause := range dnf {
		atoms := make([]string, 0, len(clause))
		for _, atom := range clause {
			primitive, ok := atom.(*PrimitiveType)
			if !ok {
				t.Fatalf("lattice refinement DNF contains unsupported atom type %T", atom)
			}
			atoms = append(atoms, strconv.Quote(primitive.Name))
		}
		clauses = append(clauses, "["+strings.Join(atoms, ", ")+"]")
	}
	return "[" + strings.Join(clauses, ", ") + "]"
}
