package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Borrowed results (docs/spec/50-borrowing.md section 9 "Borrowed
// results", authority roadmap milestone 4 stage (b)): an operation may
// declare its result a shared borrow of one borrowed argument. The result
// is its own authority that depends on the argument's owner for as long as
// its scope: the owner stays readable but cannot be mutated, consumed, or
// rebound while the result lives; the result cannot be mutated, consumed,
// stored in an aggregate, or leave the function except under a contract
// that ties it to the parameter it depends on. The primitive borrowing
// operations build their result from the owner's fields: a borrow is the
// most conservative claim, so a provenance-free result honors it, and
// every wrapper is checked against it too.
func borrowedResultDeclarations() []typechecker.ResourceProtocolDeclaration {
	mode := func(index int, m typechecker.ResourceParameterMode) typechecker.ResourceParameterDeclaration {
		return typechecker.ResourceParameterDeclaration{Index: index, Mode: m}
	}
	borrowed, mut, consumed := typechecker.ResourceParameterBorrowed, typechecker.ResourceParameterBorrowedMut, typechecker.ResourceParameterConsumed
	transition := func(name string, params ...typechecker.ResourceParameterDeclaration) typechecker.ResourceTransitionDeclaration {
		return typechecker.ResourceTransitionDeclaration{Name: name, Callable: name, From: "Open", To: "Open", Parameters: params}
	}
	free := transition("free", mode(0, consumed))
	free.To = "Closed"
	dropCursor := transition("drop_cursor", mode(0, consumed))
	dropCursor.To = "Closed"
	cursorOf := transition("cursor_of", mode(0, borrowed))
	cursorOf.ReturnsBorrow, cursorOf.BorrowsArguments = true, []int{0}
	advance := transition("advance", mode(0, borrowed))
	advance.ReturnsBorrow, advance.BorrowsArguments = true, []int{0}
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "ArenaLifecycle",
		ResourceTypes: []string{"Arena", "Cursor"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{Name: "open", Callable: "open", From: "Open", To: "Open", ReturnsFresh: true},
			cursorOf,
			advance,
			transition("read", mode(0, borrowed)),
			transition("inspect", mode(0, borrowed)),
			transition("mutate", mode(0, mut)),
			transition("bump", mode(0, mut)),
			transition("read_both", mode(0, borrowed), mode(1, borrowed)),
			transition("mutate_with", mode(0, mut), mode(1, borrowed)),
			free,
			dropCursor,
		},
	}}
}

const borrowedResultBase = `
Arena: type = struct { id: u32 }
Cursor: type = struct { pos: u32 }
open: (id: u32): Arena = Arena { id: id }
cursor_of: (a: Arena): Cursor = Cursor { pos: a.id }
advance: (c: Cursor): Cursor = Cursor { pos: c.pos + u32(1) }
read: (c: Cursor): () = {}
inspect: (a: Arena): () = {}
mutate: (a: Arena): () = {}
bump: (c: Cursor): () = {}
read_both: (a: Arena, c: Cursor): () = {}
mutate_with: (a: Arena, c: Cursor): () = {}
free: (a: Arena): () = {}
drop_cursor: (c: Cursor): () = {}
`

func checkBorrowedResults(t *testing.T, name, body string, extra ...typechecker.ResourceTransitionDeclaration) error {
	t.Helper()
	declarations := borrowedResultDeclarations()
	declarations[0].Transitions = append(declarations[0].Transitions, extra...)
	_, err := New().
		WithSource(name+".oak", borrowedResultBase+body).
		WithResourceProtocols(declarations).
		Check().
		Get()
	return err
}

func TestBorrowedResultSharedUseWhileLive(t *testing.T) {
	// The owner stays readable beside its dependent, a borrow of a borrow
	// is fine, and once the dependent's scope ends the owner is free again.
	err := checkBorrowedResults(t, "shared", `
f: (a: Arena, flag: Bool): u32 {
  flag ? {
    c: Cursor = cursor_of(a)
    d: Cursor = advance(c)
    read(c)
    read(advance(d))
    read_both(a, d)
    inspect(a)
  } | { }
  mutate(a)
  free(a)
  0
}
`)
	if err != nil {
		t.Fatalf("shared use beside a live borrowed result must be accepted: %v", err)
	}
}

func TestBorrowedResultOwnerMutationRejected(t *testing.T) {
	for name, use := range map[string]string{
		"mutate":          "mutate(a)",
		"consume":         "free(a)",
		"mutate via pair": "mutate_with(a, c)",
		"through alias":   "other: Arena = a\n  mutate(other)",
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkBorrowedResults(t, "owner", `
f: (a: Arena): u32 {
  c: Cursor = cursor_of(a)
  `+use+`
  read(c)
  0
}
`), typechecker.CodeResourceDependentResult)
		})
	}
}

func TestBorrowedResultOwnerRebindRejected(t *testing.T) {
	expectCode(t, "rebind-owner", checkBorrowedResults(t, "rebind", `
f: (a: Arena): u32 {
  c: Cursor = cursor_of(a)
  a = open(u32(2))
  read(c)
  0
}
`), typechecker.CodeResourceDependentResult)
}

func TestBorrowedResultCannotBeMutatedOrConsumed(t *testing.T) {
	for name, use := range map[string]string{
		"bump dependent":     "bump(c)",
		"drop dependent":     "drop_cursor(c)",
		"bump temporary":     "bump(cursor_of(a))",
		"drop through alias": "e: Cursor = c\n  drop_cursor(e)",
		"owner beside temp":  "mutate_with(a, cursor_of(a))",
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkBorrowedResults(t, "dependent", `
f: (a: Arena): u32 {
  c: Cursor = cursor_of(a)
  `+use+`
  0
}
`), typechecker.CodeResourceDependentResult)
		})
	}
}

func TestBorrowedResultCannotBeStored(t *testing.T) {
	for name, body := range map[string]string{
		"record field from dependent": `
Holder: type = struct { c: Cursor }
f: (a: Arena): u32 {
  c: Cursor = cursor_of(a)
  h: Holder = Holder { c: c }
  h.c.pos
}
`,
		"record field from temporary": `
Holder: type = struct { c: Cursor }
f: (a: Arena): u32 {
  h: Holder = Holder { c: cursor_of(a) }
  h.c.pos
}
`,
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkBorrowedResults(t, "store", body), typechecker.CodeResourceDependentResult)
		})
	}
}

func TestBorrowedResultCannotEscapeWithoutContract(t *testing.T) {
	for name, body := range map[string]string{
		"named":     "first: (a: Arena): Cursor {\n  c: Cursor = cursor_of(a)\n  c\n}",
		"temporary": "first: (a: Arena): Cursor = cursor_of(a)",
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkBorrowedResults(t, "escape", "\n"+body+"\n"), typechecker.CodeResourceDependentResult)
		})
	}
}

// A wrapper preserves the dependency when its own contract declares the
// result a borrow of the parameter the value depends on, and callers of the
// wrapper are held to the same rules.
func TestBorrowedResultWrapperPreservesDependency(t *testing.T) {
	wrapper := typechecker.ResourceTransitionDeclaration{Name: "first", Callable: "first", From: "Open", To: "Open",
		Parameters:    []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}},
		ReturnsBorrow: true, BorrowsArguments: []int{0}}
	if err := checkBorrowedResults(t, "wrapper", `
first: (a: Arena): Cursor {
  c: Cursor = cursor_of(a)
  advance(c)
}
g: (a: Arena, flag: Bool): u32 {
  flag ? {
    c: Cursor = first(a)
    read(c)
  } | { }
  mutate(a)
  0
}
`, wrapper); err != nil {
		t.Fatalf("a contracted wrapper must be accepted: %v", err)
	}
	expectCode(t, "wrapper-caller", checkBorrowedResults(t, "wrapper-caller", `
first: (a: Arena): Cursor = cursor_of(a)
g: (a: Arena): u32 {
  c: Cursor = first(a)
  mutate(a)
  read(c)
  0
}
`, wrapper), typechecker.CodeResourceDependentResult)
}

func TestBorrowedResultWrapperContractMismatch(t *testing.T) {
	borrowOf := func(index int) typechecker.ResourceTransitionDeclaration {
		return typechecker.ResourceTransitionDeclaration{Name: "pick", Callable: "pick", From: "Open", To: "Open",
			Parameters: []typechecker.ResourceParameterDeclaration{
				{Index: 0, Mode: typechecker.ResourceParameterBorrowed}, {Index: 1, Mode: typechecker.ResourceParameterBorrowed}},
			ReturnsBorrow: true, BorrowsArguments: []int{index}}
	}
	// Declared a borrow of b, returns a borrow of a.
	expectCode(t, "wrong-owner", checkBorrowedResults(t, "wrong-owner", `
pick: (a: Arena, b: Arena): Cursor = cursor_of(a)
`, borrowOf(1)), typechecker.CodeResourceResultContract)
	// Declared a borrow of b, returns a value whose literal mentions a.
	expectCode(t, "literal-mentions-other", checkBorrowedResults(t, "literal-mentions-other", `
pick: (a: Arena, b: Arena): Cursor = Cursor { pos: a.id }
`, borrowOf(1)), typechecker.CodeResourceResultContract)
	// Declared fresh, returns a borrowed result.
	fresh := typechecker.ResourceTransitionDeclaration{Name: "pick", Callable: "pick", From: "Open", To: "Open",
		Parameters:   []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}, {Index: 1, Mode: typechecker.ResourceParameterBorrowed}},
		ReturnsFresh: true}
	expectCode(t, "fresh-lie", checkBorrowedResults(t, "fresh-lie", `
pick: (a: Arena, b: Arena): Cursor {
  c: Cursor = cursor_of(a)
  c
}
`, fresh), typechecker.CodeResourceResultContract)
}

func TestBorrowedResultCannotOutliveOwnerScope(t *testing.T) {
	// Reassigning an outer binding to a borrow of an inner-scoped owner
	// would leave the result dangling when the inner scope ends.
	expectCode(t, "outlive", checkBorrowedResults(t, "outlive", `
f: (a: Arena, flag: Bool): u32 {
  c: Cursor = cursor_of(a)
  flag ? {
    local: Arena = open(u32(7))
    c = cursor_of(local)
  } | { }
  read(c)
  0
}
`), typechecker.CodeResourceDependentResult)
	// Reassigning to a borrow of an owner in the same or outer scope is
	// fine, and releases the old dependency.
	if err := checkBorrowedResults(t, "release", `
f: (a: Arena, b: Arena): u32 {
  c: Cursor = cursor_of(a)
  c = cursor_of(b)
  mutate(a)
  read(c)
  0
}
`); err != nil {
		t.Fatalf("rebinding a dependent releases its old dependency: %v", err)
	}
}

func TestBorrowedResultBranchesPreserveEveryDependency(t *testing.T) {
	for name, use := range map[string]string{"first owner": "mutate(a)", "second owner": "mutate(b)"} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkBorrowedResults(t, "branch", `
f: (a: Arena, b: Arena, flag: Bool): u32 {
  c: Cursor = cursor_of(a)
  flag ? { c = cursor_of(b) } | { }
  `+use+`
  read(c)
  0
}
`), typechecker.CodeResourceDependentResult)
		})
	}
}

func TestBorrowedResultDeclarationValidation(t *testing.T) {
	for name, mutate := range map[string]func(*typechecker.ResourceTransitionDeclaration){
		"consumed source": func(d *typechecker.ResourceTransitionDeclaration) {
			d.Parameters[0].Mode = typechecker.ResourceParameterConsumed
		},
		"borrow and fresh": func(d *typechecker.ResourceTransitionDeclaration) { d.ReturnsFresh = true },
		"borrow and alias": func(d *typechecker.ResourceTransitionDeclaration) { d.ReturnsAlias = true },
		"out of range":     func(d *typechecker.ResourceTransitionDeclaration) { d.BorrowsArguments = []int{4} },
		"duplicate":        func(d *typechecker.ResourceTransitionDeclaration) { d.BorrowsArguments = []int{0, 0} },
		"empty":            func(d *typechecker.ResourceTransitionDeclaration) { d.BorrowsArguments = nil },
	} {
		t.Run(name, func(t *testing.T) {
			declarations := borrowedResultDeclarations()
			for i := range declarations[0].Transitions {
				if declarations[0].Transitions[i].Name == "cursor_of" {
					mutate(&declarations[0].Transitions[i])
				}
			}
			_, err := New().WithSource("declare.oak", borrowedResultBase).WithResourceProtocols(declarations).Check().Get()
			if err == nil {
				t.Fatal("invalid borrowed-result declaration must be rejected")
			}
		})
	}
}

func TestBorrowedResultSemIRRoundTrip(t *testing.T) {
	result, err := New().WithSource("borrow.oak", borrowedResultBase).ResourceSemIR(borrowedResultDeclarations()).Get()
	if err != nil {
		t.Fatalf("resource SemIR stage failed: %v", err)
	}
	found := false
	for _, protocol := range result.Module.Protocols {
		for _, transition := range protocol.Transitions {
			if transition.Callable != "advance" {
				continue
			}
			semantics, present, err := transition.ResourceSemantics()
			if err != nil || !present {
				t.Fatalf("advance semantics: present=%v err=%v", present, err)
			}
			if !semantics.ReturnsBorrow || len(semantics.BorrowsArguments) != 1 || semantics.BorrowsArguments[0] != 0 || semantics.ReturnsFresh || semantics.ReturnsAlias {
				t.Fatalf("advance should borrow argument 0, got %#v", semantics)
			}
			for _, effect := range transition.Effects {
				if effect.Name == "return-borrow" && len(effect.Parameters) == 1 && effect.Parameters[0] == "arg:0" {
					found = true
				}
			}
		}
	}
	if !found {
		t.Fatalf("advance lacks resource.return-borrow arg:0 in emitted SemIR: %#v", result.Module.Protocols)
	}
}
