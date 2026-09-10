package compiler

import (
	"errors"
	"sort"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Callee-entry authority (docs/spec/50-borrowing.md section 9, authority
// roadmap milestone 1): a function's own resource contract fixes what its
// body may do with each parameter. A borrowed parameter may be read and
// forwarded to borrowed positions but neither mutated through a
// borrowed-mut contract nor consumed; a borrowed-mut parameter may be
// forwarded to shared and mutable positions but not consumed; a consumed
// parameter has full authority until its own consumption.
// calleeAuthorityDeclarations describes the three primitive operations and
// the wrappers a test declares, each wrapper with its own contract mode on
// its first parameter; a protocol may only name callables the program
// defines, so each test lists the wrappers it declares.
func calleeAuthorityDeclarations(wrappers map[string]typechecker.ResourceParameterMode) []typechecker.ResourceProtocolDeclaration {
	mode := func(m typechecker.ResourceParameterMode) []typechecker.ResourceParameterDeclaration {
		return []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: m}}
	}
	transition := func(callable string, m typechecker.ResourceParameterMode) typechecker.ResourceTransitionDeclaration {
		to := "Open"
		if m == typechecker.ResourceParameterConsumed {
			to = "Closed"
		}
		return typechecker.ResourceTransitionDeclaration{Name: callable, Callable: callable, From: "Open", To: to, Parameters: mode(m)}
	}
	transitions := []typechecker.ResourceTransitionDeclaration{
		transition("inspect", typechecker.ResourceParameterBorrowed),
		transition("update", typechecker.ResourceParameterBorrowedMut),
		transition("close", typechecker.ResourceParameterConsumed),
	}
	names := make([]string, 0, len(wrappers))
	for name := range wrappers {
		names = append(names, name)
	}
	sort.Strings(names)
	for _, name := range names {
		transitions = append(transitions, transition(name, wrappers[name]))
	}
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions:   transitions,
	}}
}

const calleeAuthorityBase = `
Handle: type = struct { id: u32 }
inspect: (h: Handle): () = {}
update: (h: Handle): () = {}
close: (h: Handle): () = {}
`

func checkWithCalleeAuthority(t *testing.T, name, body string, wrappers map[string]typechecker.ResourceParameterMode) error {
	t.Helper()
	_, err := New().
		WithSource(name+".oak", calleeAuthorityBase+body).
		WithResourceProtocols(calleeAuthorityDeclarations(wrappers)).
		Check().
		Get()
	return err
}

func TestCalleeAuthorityPermittedForwarding(t *testing.T) {
	// A borrowed wrapper reads and forwards to borrowed positions; a
	// borrowed-mut wrapper forwards to shared and mutable positions; a
	// consuming wrapper stays free to inspect, update, and finally consume.
	if err := checkWithCalleeAuthority(t, "permitted", `
peek: (h: Handle): u32 {
  inspect(h)
  h.id
}
poke: (h: Handle): () {
  inspect(h)
  update(h)
}
finish: (h: Handle): () {
  inspect(h)
  update(h)
  close(h)
}
`, map[string]typechecker.ResourceParameterMode{"peek": typechecker.ResourceParameterBorrowed, "poke": typechecker.ResourceParameterBorrowedMut, "finish": typechecker.ResourceParameterConsumed}); err != nil {
		t.Fatalf("permitted forwarding rejected: %v", err)
	}
}

func expectForwardingRejection(t *testing.T, name, body, wantText string, wrappers map[string]typechecker.ResourceParameterMode) {
	t.Helper()
	err := checkWithCalleeAuthority(t, name, body, wrappers)
	if err == nil {
		t.Fatalf("%s: expected OAK-B0114, program accepted", name)
	}
	var diagnosticErr *DiagnosticError
	if !errors.As(err, &diagnosticErr) {
		t.Fatalf("%s: expected DiagnosticError, got %T: %v", name, err, err)
	}
	for _, d := range diagnosticErr.Diagnostics {
		if d != nil && d.Code == typechecker.CodeResourceParameterForwarded {
			if !strings.Contains(d.Title, wantText) {
				t.Fatalf("%s: diagnostic %q lacks %q", name, d.Title, wantText)
			}
			if len(d.Labels) < 2 {
				t.Fatalf("%s: diagnostic does not point at the parameter declaration: %#v", name, d.Labels)
			}
			return
		}
		if d != nil && d.Code == typechecker.CodeResourceUsedAfterConsume {
			t.Fatalf("%s: a rejected forwarding must not cascade into %s", name, d.Code)
		}
	}
	t.Fatalf("%s: expected %s, got %#v", name, typechecker.CodeResourceParameterForwarded, diagnosticErr.Diagnostics)
}

func TestCalleeAuthorityRejectsBorrowedWrapperConsuming(t *testing.T) {
	expectForwardingRejection(t, "leaky", `
leaky_peek: (h: Handle): u32 {
  close(h)
  h.id
}
`, `parameter "h" enters with borrowed authority and cannot be passed to the consumed parameter of close`,
		map[string]typechecker.ResourceParameterMode{"leaky_peek": typechecker.ResourceParameterBorrowed})
}

func TestCalleeAuthorityRejectsSharedToMutableForwarding(t *testing.T) {
	expectForwardingRejection(t, "upgrading", `
upgrading_peek: (h: Handle): u32 {
  update(h)
  h.id
}
`, "cannot be passed to the borrowed-mut parameter of update",
		map[string]typechecker.ResourceParameterMode{"upgrading_peek": typechecker.ResourceParameterBorrowed})
}

func TestCalleeAuthorityRejectsMutableWrapperConsuming(t *testing.T) {
	expectForwardingRejection(t, "leaky-poke", `
leaky_poke: (h: Handle): () {
  update(h)
  close(h)
}
`, `parameter "h" enters with borrowed-mut authority and cannot be passed to the consumed parameter of close`,
		map[string]typechecker.ResourceParameterMode{"leaky_poke": typechecker.ResourceParameterBorrowedMut})
}

func TestCalleeAuthorityFollowsAliases(t *testing.T) {
	// Renaming the parameter does not launder its authority.
	expectForwardingRejection(t, "aliased", `
aliased_peek: (h: Handle): u32 {
  same: Handle = h
  close(same)
  h.id
}
`, `parameter "h" enters with borrowed authority`,
		map[string]typechecker.ResourceParameterMode{"aliased_peek": typechecker.ResourceParameterBorrowed})
}

func TestCalleeAuthorityLeavesUnmarkedParametersAlone(t *testing.T) {
	// A function without a contract of its own keeps today's meaning: its
	// parameters enter with full authority.
	if err := checkWithCalleeAuthority(t, "unmarked", `
free: (h: Handle): () {
  update(h)
  close(h)
}
`, nil); err != nil {
		t.Fatalf("unmarked parameter lost its authority: %v", err)
	}
}
