package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Nested and multiple-origin borrowed results (docs/spec/50-borrowing.md
// section 9 "Borrowed results", authority roadmap milestone 4 stage (c)):
// a result may depend on several arguments at once, a borrow of a
// projection depends on that field path, and a temporary borrowed result
// takes part in call exclusivity with its owner set rather than as an
// untracked value.
func multiOriginDeclarations() []typechecker.ResourceProtocolDeclaration {
	declarations := borrowedResultDeclarations()
	borrowed := typechecker.ResourceParameterBorrowed
	params := func(modes ...typechecker.ResourceParameterMode) []typechecker.ResourceParameterDeclaration {
		out := make([]typechecker.ResourceParameterDeclaration, len(modes))
		for i, m := range modes {
			out[i] = typechecker.ResourceParameterDeclaration{Index: i, Mode: m}
		}
		return out
	}
	declarations[0].Transitions = append(declarations[0].Transitions,
		// merge depends on both arenas.
		typechecker.ResourceTransitionDeclaration{Name: "merge", Callable: "merge", From: "Open", To: "Open",
			Parameters: params(borrowed, borrowed), ReturnsBorrow: true, BorrowsArguments: []int{0, 1}},
		// join depends on both cursors, hence on their owners.
		typechecker.ResourceTransitionDeclaration{Name: "join", Callable: "join", From: "Open", To: "Open",
			Parameters: params(borrowed, borrowed), ReturnsBorrow: true, BorrowsArguments: []int{0, 1}},
		// pick depends on its second argument only.
		typechecker.ResourceTransitionDeclaration{Name: "pick", Callable: "pick", From: "Open", To: "Open",
			Parameters: params(borrowed, borrowed), ReturnsBorrow: true, BorrowsArguments: []int{1}},
	)
	return declarations
}

const multiOriginBase = borrowedResultBase + `
merge: (a: Arena, b: Arena): Cursor = Cursor { pos: a.id + b.id }
join: (c: Cursor, d: Cursor): Cursor = Cursor { pos: c.pos + d.pos }
pick: (a: Arena, b: Arena): Cursor = Cursor { pos: b.id }
Box: type = struct { arena: Arena, tag: u32 }
`

func checkMultiOrigin(t *testing.T, name, body string, extra ...typechecker.ResourceTransitionDeclaration) error {
	t.Helper()
	declarations := multiOriginDeclarations()
	declarations[0].Transitions = append(declarations[0].Transitions, extra...)
	_, err := New().
		WithSource(name+".oak", multiOriginBase+body).
		WithResourceProtocols(declarations).
		Check().
		Get()
	return err
}

func TestMultiOriginResultProtectsEveryOwner(t *testing.T) {
	for name, use := range map[string]string{"first": "mutate(a)", "second": "free(b)"} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkMultiOrigin(t, "multi", `
f: (a: Arena, b: Arena): u32 {
  c: Cursor = merge(a, b)
  `+use+`
  read(c)
  0
}
`), typechecker.CodeResourceDependentResult)
		})
	}
	// Owners not in the set stay free, and reading every owner is fine.
	if err := checkMultiOrigin(t, "multi-ok", `
f: (a: Arena, b: Arena, other: Arena): u32 {
  c: Cursor = merge(a, b)
  inspect(a)
  inspect(b)
  mutate(other)
  read(c)
  0
}
`); err != nil {
		t.Fatalf("owners outside the dependency set must stay free: %v", err)
	}
}

func TestMultiOriginResultThroughNestedBorrows(t *testing.T) {
	// join(cursor_of(a), cursor_of(b)) depends on a and b through two
	// temporary borrowed results; pick(a, b) depends on b alone.
	for name, use := range map[string]string{"first root": "mutate(a)", "second root": "mutate(b)"} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkMultiOrigin(t, "nested", `
f: (a: Arena, b: Arena): u32 {
  c: Cursor = join(cursor_of(a), cursor_of(b))
  `+use+`
  read(c)
  0
}
`), typechecker.CodeResourceDependentResult)
		})
	}
	if err := checkMultiOrigin(t, "pick-ok", `
f: (a: Arena, b: Arena): u32 {
  c: Cursor = pick(a, b)
  mutate(a)
  read(c)
  0
}
`); err != nil {
		t.Fatalf("pick depends on b only, so a stays free: %v", err)
	}
	expectCode(t, "pick-b", checkMultiOrigin(t, "pick-b", `
f: (a: Arena, b: Arena): u32 {
  c: Cursor = pick(a, b)
  mutate(b)
  read(c)
  0
}
`), typechecker.CodeResourceDependentResult)
}

func TestMultiOriginResultUnknownOriginFailsClosed(t *testing.T) {
	// One argument without provenance makes the whole result unknown, so a
	// consuming use of the result fails closed rather than trusting half a
	// dependency.
	expectCode(t, "unknown-origin", checkMultiOrigin(t, "unknown-origin", `
f: (a: Arena, box: Box): u32 {
  c: Cursor = merge(a, box.arena)
  drop_cursor(c)
  0
}
`), typechecker.CodeResourceCallAliasConflict)
}

func TestNestedProjectionOwner(t *testing.T) {
	// A borrow of a record field depends on that path: writing the field,
	// or the whole record, while the dependent lives is rejected; a
	// different field is free.
	for name, use := range map[string]string{
		"field write":  "box.arena = open(u32(9))",
		"record write": "box = other",
		"mutate field": "mutate(box.arena)",
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkMultiOrigin(t, "projection", `
f: (a: Arena, other: Box): u32 {
  box: Box = Box { arena: a, tag: u32(1) }
  c: Cursor = cursor_of(box.arena)
  `+use+`
  read(c)
  0
}
`), typechecker.CodeResourceDependentResult)
		})
	}
	if err := checkMultiOrigin(t, "projection-ok", `
f: (a: Arena): u32 {
  box: Box = Box { arena: a, tag: u32(1) }
  c: Cursor = cursor_of(box.arena)
  inspect(box.arena)
  read(c)
  box.tag
}
`); err != nil {
		t.Fatalf("reading through the projection beside its dependent must be accepted: %v", err)
	}
}

func TestTemporaryBorrowedResultExclusivityPrecision(t *testing.T) {
	// A temporary borrowed result with known owners is distinct from an
	// unrelated mutable argument, so the pair is accepted where an untracked
	// value would have failed closed; pairing it with its own owner stays
	// rejected.
	if err := checkMultiOrigin(t, "precise-ok", `
f: (a: Arena, x: Arena): u32 {
  mutate_with(x, cursor_of(a))
  0
}
`); err != nil {
		t.Fatalf("a temporary borrow of a is distinct from x: %v", err)
	}
	expectCode(t, "precise-owner", checkMultiOrigin(t, "precise-owner", `
f: (a: Arena): u32 {
  mutate_with(a, cursor_of(a))
  0
}
`), typechecker.CodeResourceDependentResult)
	expectCode(t, "precise-alias", checkMultiOrigin(t, "precise-alias", `
f: (a: Arena): u32 {
  same: Arena = a
  mutate_with(same, cursor_of(a))
  0
}
`), typechecker.CodeResourceDependentResult)
}

func TestMultiOriginWrapperContracts(t *testing.T) {
	both := typechecker.ResourceTransitionDeclaration{Name: "wrap", Callable: "wrap", From: "Open", To: "Open",
		Parameters: []typechecker.ResourceParameterDeclaration{
			{Index: 0, Mode: typechecker.ResourceParameterBorrowed}, {Index: 1, Mode: typechecker.ResourceParameterBorrowed}},
		ReturnsBorrow: true, BorrowsArguments: []int{0, 1}}
	second := both
	second.BorrowsArguments = []int{1}
	// A wrapper declaring both origins may return a borrow of both, of one,
	// or either parameter itself.
	for name, body := range map[string]string{
		"both":   "wrap: (a: Arena, b: Arena): Cursor = merge(a, b)",
		"subset": "wrap: (a: Arena, b: Arena): Cursor = cursor_of(b)",
		"nested": "wrap: (a: Arena, b: Arena): Cursor {\n  c: Cursor = cursor_of(a)\n  join(c, cursor_of(b))\n}",
	} {
		t.Run(name, func(t *testing.T) {
			if err := checkMultiOrigin(t, "wrap", "\n"+body+"\n", both); err != nil {
				t.Fatalf("a wrapper covering its result's dependencies must be accepted: %v", err)
			}
		})
	}
	// Declaring fewer origins than the body's result depends on is a lie.
	expectCode(t, "under-declared", checkMultiOrigin(t, "under", `
wrap: (a: Arena, b: Arena): Cursor = merge(a, b)
`, second), typechecker.CodeResourceResultContract)
	// Callers of a multi-origin wrapper protect every declared owner.
	expectCode(t, "wrapper-caller", checkMultiOrigin(t, "wrapper-caller", `
wrap: (a: Arena, b: Arena): Cursor = merge(a, b)
g: (a: Arena, b: Arena): u32 {
  c: Cursor = wrap(a, b)
  mutate(b)
  read(c)
  0
}
`, both), typechecker.CodeResourceDependentResult)
}

func TestMultiOriginSemIRRoundTrip(t *testing.T) {
	result, err := New().WithSource("multi.oak", multiOriginBase).ResourceSemIR(multiOriginDeclarations()).Get()
	if err != nil {
		t.Fatalf("resource SemIR stage failed: %v", err)
	}
	for _, protocol := range result.Module.Protocols {
		for _, transition := range protocol.Transitions {
			if transition.Callable != "merge" {
				continue
			}
			semantics, present, err := transition.ResourceSemantics()
			if err != nil || !present {
				t.Fatalf("merge semantics: present=%v err=%v", present, err)
			}
			if !semantics.ReturnsBorrow || len(semantics.BorrowsArguments) != 2 || semantics.BorrowsArguments[0] != 0 || semantics.BorrowsArguments[1] != 1 {
				t.Fatalf("merge should borrow arguments 0 and 1, got %#v", semantics)
			}
			effects := 0
			for _, effect := range transition.Effects {
				if effect.Name == "return-borrow" {
					effects++
				}
			}
			if effects != 2 {
				t.Fatalf("merge should emit two return-borrow effects, got %d: %#v", effects, transition.Effects)
			}
			return
		}
	}
	t.Fatal("merge transition missing from emitted SemIR")
}
