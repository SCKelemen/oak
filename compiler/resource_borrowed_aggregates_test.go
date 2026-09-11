package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Borrowed values in aggregates (docs/spec/50-borrowing.md section 9
// "Borrowed results", authority roadmap milestone 4 stage (e)): a borrowed
// result may be stored in a record field when the record's binding does
// not outlive the owners the value depends on; the field path then carries
// the dependency and permission, and the record cannot escape the function
// through a call or a return.
const aggregateBase = mutableReborrowBase + `
Outer: type = struct { h: Holder, tag: u32 }
take_holder: (h: Holder): () = {}
`

func checkAggregates(t *testing.T, name, body string) error {
	t.Helper()
	_, err := New().
		WithSource(name+".oak", aggregateBase+body).
		WithResourceProtocols(mutableReborrowDeclarations()).
		Check().
		Get()
	return err
}

func TestAggregateFieldCarriesDependency(t *testing.T) {
	for name, tc := range map[string]struct{ init, use string }{
		"temporary, mutate owner": {"Holder { c: cursor_of(a) }", "mutate(a)"},
		"temporary, free owner":   {"Holder { c: cursor_of(a) }", "free(a)"},
		"named, free owner":       {"Holder { c: c }", "free(a)"},
		"consume field":           {"Holder { c: cursor_of(a) }", "drop_cursor(h.c)"},
		"mutate shared field":     {"Holder { c: cursor_of(a) }", "bump(h.c)"},
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkAggregates(t, "field", `
f: (a: Arena): u32 {
  c: Cursor = cursor_of(a)
  h: Holder = `+tc.init+`
  `+tc.use+`
  read(h.c)
  0
}
`), typechecker.CodeResourceDependentResult)
		})
	}
	// Reading through the field beside its owner is fine, and the owner is
	// free again once the record's scope ends.
	if err := checkAggregates(t, "field-ok", `
f: (a: Arena, flag: Bool): u32 {
  flag ? {
    h: Holder = Holder { c: cursor_of(a) }
    read(h.c)
    read_both(a, h.c)
    inspect(a)
  } | { }
  mutate(a)
  0
}
`); err != nil {
		t.Fatalf("a record holding a borrowed result must be usable in its scope: %v", err)
	}
}

func TestAggregateMutableFieldSuspendsOwner(t *testing.T) {
	expectCode(t, "mutable-field", checkAggregates(t, "mutable-field", `
f: (a: Arena): u32 {
  h: Holder = Holder { c: mut_cursor(a) }
  inspect(a)
  bump(h.c)
  0
}
`), typechecker.CodeResourceSuspendedOwner)
	if err := checkAggregates(t, "mutable-field-ok", `
f: (a: Arena, flag: Bool): u32 {
  flag ? {
    h: Holder = Holder { c: mut_cursor(a) }
    bump(h.c)
    read(h.c)
  } | { }
  inspect(a)
  0
}
`); err != nil {
		t.Fatalf("a mutable reborrow in a field must be usable through the path: %v", err)
	}
}

func TestAggregateDestinationMustNotOutliveOwner(t *testing.T) {
	// The outer record would outlive the inner arena.
	expectCode(t, "outlive", checkAggregates(t, "outlive", `
f: (a: Arena, flag: Bool): u32 {
  h: Holder = Holder { c: cursor_of(a) }
  flag ? {
    local: Arena = open(u32(3))
    h.c = cursor_of(local)
  } | { }
  read(h.c)
  0
}
`), typechecker.CodeResourceDependentResult)
	// A record bound in the same scope as the owner is fine, and a field
	// write releases the old dependency.
	if err := checkAggregates(t, "same-scope", `
f: (a: Arena, b: Arena, flag: Bool): u32 {
  flag ? {
    local: Arena = open(u32(3))
    h: Holder = Holder { c: cursor_of(local) }
    h.c = cursor_of(b)
    mutate(local)
    read(h.c)
  } | { }
  0
}
`); err != nil {
		t.Fatalf("a same-scope destination and a releasing field write must be accepted: %v", err)
	}
}

func TestAggregateCannotEscape(t *testing.T) {
	for name, body := range map[string]string{
		"passed": `
f: (a: Arena): u32 {
  h: Holder = Holder { c: cursor_of(a) }
  take_holder(h)
  0
}`,
		"literal passed": `
f: (a: Arena): u32 {
  c: Cursor = cursor_of(a)
  take_holder(Holder { c: c })
  0
}`,
		"returned": `
f: (a: Arena): Holder {
  h: Holder = Holder { c: cursor_of(a) }
  h
}`,
		"literal returned": `
f: (a: Arena): Holder {
  c: Cursor = cursor_of(a)
  Holder { c: c }
}`,
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkAggregates(t, "escape", "\n"+body+"\n"), typechecker.CodeResourceDependentResult)
		})
	}
	// A record without borrowed fields still passes and returns freely.
	if err := checkAggregates(t, "plain", `
g: (a: Arena): Holder {
  h: Holder = Holder { c: Cursor { pos: a.id } }
  take_holder(h)
  h
}
`); err != nil {
		t.Fatalf("a record without borrowed fields is unaffected: %v", err)
	}
}

func TestAggregateCopiesCarryDependency(t *testing.T) {
	// Nesting and whole-record copies carry the dependency to the new
	// paths, so the owner stays protected through every copy.
	for name, body := range map[string]string{
		"nested literal": `
f: (a: Arena): u32 {
  h: Holder = Holder { c: cursor_of(a) }
  o: Outer = Outer { h: h, tag: u32(1) }
  mutate(a)
  read(o.h.c)
  0
}`,
		"record copy": `
f: (a: Arena): u32 {
  h: Holder = Holder { c: cursor_of(a) }
  k: Holder = h
  free(a)
  read(k.c)
  0
}`,
		"record write": `
f: (a: Arena, other: Holder): u32 {
  h: Holder = Holder { c: cursor_of(a) }
  k: Holder = other
  k = h
  mutate(a)
  read(k.c)
  0
}`,
	} {
		t.Run(name, func(t *testing.T) {
			expectCode(t, name, checkAggregates(t, "copy", "\n"+body+"\n"), typechecker.CodeResourceDependentResult)
		})
	}
	// Rebinding the record to a record without borrowed fields releases
	// the dependency.
	if err := checkAggregates(t, "release", `
f: (a: Arena, other: Holder): u32 {
  h: Holder = Holder { c: cursor_of(a) }
  h = other
  mutate(a)
  0
}
`); err != nil {
		t.Fatalf("rebinding the record releases its fields' dependencies: %v", err)
	}
}
