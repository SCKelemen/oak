package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Mutable reborrows (docs/spec/50-borrowing.md section 9 "Borrowed
// results", authority roadmap milestone 4 stage (d)): a borrowed result
// may carry mutable authority when every origin is borrowed-mut. It may be
// passed to borrowed-mut positions, and while it lives its owners are
// suspended entirely — no reads, projections, calls, rebinding, or return
// — until its scope ends.
func mutableReborrowDeclarations() []typechecker.ResourceProtocolDeclaration {
	declarations := borrowedResultDeclarations()
	mut := typechecker.ResourceParameterBorrowedMut
	declarations[0].Transitions = append(declarations[0].Transitions,
		typechecker.ResourceTransitionDeclaration{Name: "mut_cursor", Callable: "mut_cursor", From: "Open", To: "Open",
			Parameters:    []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: mut}},
			ReturnsBorrow: true, BorrowsArguments: []int{0}, BorrowMutable: true},
		typechecker.ResourceTransitionDeclaration{Name: "mut_advance", Callable: "mut_advance", From: "Open", To: "Open",
			Parameters:    []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: mut}},
			ReturnsBorrow: true, BorrowsArguments: []int{0}, BorrowMutable: true},
	)
	return declarations
}

const mutableReborrowBase = borrowedResultBase + `
mut_cursor: (a: Arena): Cursor = Cursor { pos: a.id }
mut_advance: (c: Cursor): Cursor = Cursor { pos: c.pos + u32(1) }
Holder: type = struct { c: Cursor }
`

func checkMutableReborrows(t *testing.T, name, body string, extra ...typechecker.ResourceTransitionDeclaration) error {
	t.Helper()
	declarations := mutableReborrowDeclarations()
	declarations[0].Transitions = append(declarations[0].Transitions, extra...)
	_, err := New().
		WithSource(name+".oak", mutableReborrowBase+body).
		WithResourceProtocols(declarations).
		Check().
		Get()
	return err
}

func TestMutableReborrowUsableAndReleased(t *testing.T) {
	// The reborrow is mutated, read, reborrowed again (shared and mutable)
	// inside its scope; the owner is usable again once the scope ends.
	if err := checkMutableReborrows(t, "mutable-ok", `
f: (a: Arena, flag: Bool): u32 {
  flag ? {
    c: Cursor = mut_cursor(a)
    bump(c)
    read(c)
    read(advance(c))
    bump(mut_advance(c))
    e: Cursor = c
    bump(e)
  } | { }
  inspect(a)
  mutate(a)
  free(a)
  0
}
`); err != nil {
		t.Fatalf("a mutable reborrow must be usable and released at scope end: %v", err)
	}
}

func TestMutableReborrowSuspendsOwner(t *testing.T) {
	for name, use := range map[string]string{
		"shared read":   "inspect(a)",
		"projection":    "n: u32 = a.id",
		"paired read":   "read_both(a, c)",
		"through alias": "other: Arena = a\n  inspect(other)",
		"mutation":      "mutate(a)",
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkMutableReborrows(t, "suspended", `
f: (a: Arena): u32 {
  c: Cursor = mut_cursor(a)
  `+use+`
  read(c)
  0
}
`), typechecker.CodeResourceSuspendedOwner)
		})
	}
	// Returning the suspended owner is a use of it.
	expectCode(t, "return-owner", checkMutableReborrows(t, "return-owner", `
f: (a: Arena): Arena {
  c: Cursor = mut_cursor(a)
  bump(c)
  a
}
`), typechecker.CodeResourceSuspendedOwner)
}

func TestMutableReborrowTemporarySuspendsOwnerForTheCall(t *testing.T) {
	expectCode(t, "temp-owner", checkMutableReborrows(t, "temp-owner", `
f: (a: Arena): u32 {
  read_both(a, mut_cursor(a))
  0
}
`), typechecker.CodeResourceSuspendedOwner)
	if err := checkMutableReborrows(t, "temp-ok", `
f: (a: Arena, x: Arena): u32 {
  bump(mut_cursor(a))
  read_both(x, mut_cursor(a))
  inspect(a)
  0
}
`); err != nil {
		t.Fatalf("a temporary mutable reborrow releases its owner after the call: %v", err)
	}
}

func TestMutableReborrowKeepsDependentRules(t *testing.T) {
	for name, use := range map[string]string{
		"consume": "drop_cursor(c)",
		"store":   "h: Holder = Holder { c: c }",
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkMutableReborrows(t, "rules", `
f: (a: Arena): u32 {
  c: Cursor = mut_cursor(a)
  `+use+`
  0
}
`), typechecker.CodeResourceDependentResult)
		})
	}
	expectCode(t, "escape", checkMutableReborrows(t, "escape", `
first: (a: Arena): Cursor = mut_cursor(a)
`), typechecker.CodeResourceDependentResult)
}

func TestMutableReborrowCannotBeMintedFromSharedBorrow(t *testing.T) {
	// A shared dependent (or temporary) passed to the borrowed-mut origin
	// of a mutable reborrow is a widening and stays rejected.
	expectCode(t, "widen-temp", checkMutableReborrows(t, "widen-temp", `
f: (a: Arena): u32 {
  d: Cursor = mut_advance(cursor_of(a))
  0
}
`), typechecker.CodeResourceDependentResult)
	expectCode(t, "widen-named", checkMutableReborrows(t, "widen-named", `
f: (a: Arena): u32 {
  c: Cursor = cursor_of(a)
  d: Cursor = mut_advance(c)
  0
}
`), typechecker.CodeResourceDependentResult)
	// Nested mutable reborrows compose and suspend the root owner.
	expectCode(t, "nested-root", checkMutableReborrows(t, "nested-root", `
f: (a: Arena): u32 {
  d: Cursor = mut_advance(mut_cursor(a))
  inspect(a)
  bump(d)
  0
}
`), typechecker.CodeResourceSuspendedOwner)
}

func TestMutableReborrowWrapperContracts(t *testing.T) {
	mutable := typechecker.ResourceTransitionDeclaration{Name: "wrap", Callable: "wrap", From: "Open", To: "Open",
		Parameters:    []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowedMut}},
		ReturnsBorrow: true, BorrowsArguments: []int{0}, BorrowMutable: true}
	shared := mutable
	shared.BorrowMutable = false
	// A mutable wrapper returning a mutable reborrow, directly or through a
	// binding, is honest; a shared wrapper may narrow a mutable one.
	for name, tc := range map[string]struct {
		body     string
		contract typechecker.ResourceTransitionDeclaration
	}{
		"mutable direct": {"wrap: (a: Arena): Cursor = mut_cursor(a)", mutable},
		"mutable named":  {"wrap: (a: Arena): Cursor {\n  c: Cursor = mut_cursor(a)\n  bump(c)\n  c\n}", mutable},
		"narrowing":      {"wrap: (a: Arena): Cursor = mut_cursor(a)", shared},
	} {
		t.Run(name, func(t *testing.T) {
			if err := checkMutableReborrows(t, "wrap", "\n"+tc.body+"\n", tc.contract); err != nil {
				t.Fatalf("an honest wrapper must be accepted: %v", err)
			}
		})
	}
	// Widening a shared borrow into a declared mutable reborrow is a lie.
	for name, body := range map[string]string{
		"widen direct": "wrap: (a: Arena): Cursor = cursor_of(a)",
		"widen named":  "wrap: (a: Arena): Cursor {\n  c: Cursor = cursor_of(a)\n  c\n}",
	} {
		t.Run(name, func(t *testing.T) {
			err := checkMutableReborrows(t, "widen", "\n"+body+"\n", mutable)
			expectCode(t, name, err, typechecker.CodeResourceResultContract)
			if !strings.Contains(err.Error(), "cannot be widened") {
				t.Fatalf("diagnostic should name the widening: %v", err)
			}
		})
	}
	// Callers of a mutable wrapper see a suspended owner.
	expectCode(t, "wrapper-caller", checkMutableReborrows(t, "wrapper-caller", `
wrap: (a: Arena): Cursor = mut_cursor(a)
g: (a: Arena): u32 {
  c: Cursor = wrap(a)
  inspect(a)
  bump(c)
  0
}
`, mutable), typechecker.CodeResourceSuspendedOwner)
}

func TestMutableReborrowDeclarationValidation(t *testing.T) {
	for name, mutate := range map[string]func(*typechecker.ResourceTransitionDeclaration){
		"shared origin": func(d *typechecker.ResourceTransitionDeclaration) {
			d.Parameters[0].Mode = typechecker.ResourceParameterBorrowed
		},
		"mutable without borrow": func(d *typechecker.ResourceTransitionDeclaration) {
			d.ReturnsBorrow, d.BorrowsArguments = false, nil
		},
	} {
		t.Run(name, func(t *testing.T) {
			declarations := mutableReborrowDeclarations()
			for i := range declarations[0].Transitions {
				if declarations[0].Transitions[i].Name == "mut_cursor" {
					mutate(&declarations[0].Transitions[i])
				}
			}
			_, err := New().WithSource("declare.oak", mutableReborrowBase).WithResourceProtocols(declarations).Check().Get()
			if err == nil {
				t.Fatal("invalid mutable-reborrow declaration must be rejected")
			}
		})
	}
}

func TestMutableReborrowSemIRRoundTrip(t *testing.T) {
	result, err := New().WithSource("mut.oak", mutableReborrowBase).ResourceSemIR(mutableReborrowDeclarations()).Get()
	if err != nil {
		t.Fatalf("resource SemIR stage failed: %v", err)
	}
	for _, protocol := range result.Module.Protocols {
		for _, transition := range protocol.Transitions {
			if transition.Callable != "mut_cursor" {
				continue
			}
			semantics, present, err := transition.ResourceSemantics()
			if err != nil || !present {
				t.Fatalf("mut_cursor semantics: present=%v err=%v", present, err)
			}
			if !semantics.ReturnsBorrow || !semantics.BorrowMutable || len(semantics.BorrowsArguments) != 1 || semantics.BorrowsArguments[0] != 0 {
				t.Fatalf("mut_cursor should be a mutable reborrow of argument 0, got %#v", semantics)
			}
			found := false
			for _, effect := range transition.Effects {
				if effect.Name == "return-borrow-mut" && len(effect.Parameters) == 1 && effect.Parameters[0] == "arg:0" {
					found = true
				}
			}
			if !found {
				t.Fatalf("mut_cursor lacks resource.return-borrow-mut arg:0: %#v", transition.Effects)
			}
			return
		}
	}
	t.Fatal("mut_cursor transition missing from emitted SemIR")
}
