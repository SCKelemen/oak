package compiler

import (
	"reflect"
	"sort"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Result identities, callable contracts, methods, and the trusted boundary
// on protocol `via` lines (docs/spec/112-protocols.md section 5). Until this
// increment those facts existed only as Go-struct injection
// (WithResourceProtocols) and SemIR; now the source declares them and the
// same checker rules (OAK-B0111, B0114, B0116–B0119) follow from the text.

// viaResultsProtocol spells, in source, exactly the contracts that
// resource_borrowed_results_test.go and resource_mutable_reborrows_test.go
// inject as Go structs.
const viaResultsProtocol = `
ArenaLifecycle: protocol = {
  resource Arena
  resource Cursor
  initial Open
  make: Open -> Open via open(): fresh
  cursor: Open -> Open via cursor_of(borrowed a): borrow a
  step: Open -> Open via advance(borrowed c): borrow c
  look: Open -> Open via read(borrowed c)
  peek: Open -> Open via inspect(borrowed a)
  change: Open -> Open via mutate(borrowed mut a)
  poke: Open -> Open via bump(borrowed mut c)
  both: Open -> Open via read_both(borrowed a, borrowed c)
  edit: Open -> Open via mutate_with(borrowed mut a, borrowed c)
  release: Open -> Closed via free(consumed a)
  drop: Open -> Closed via drop_cursor(consumed c)
  mcursor: Open -> Open via mut_cursor(borrowed mut a): borrow mut a
  mstep: Open -> Open via mut_advance(borrowed mut c): borrow mut c
}
`

func checkViaResults(t *testing.T, name, body string) error {
	t.Helper()
	_, err := New().WithSource(name+".oak", mutableReborrowBase+viaResultsProtocol+body).Check().Get()
	return err
}

// viaFacts is the order-independent projection of one via line used to
// compare source-declared facts with injected ones.
type viaFacts struct {
	From, To         string
	Parameters       []typechecker.ResourceParameterDeclaration
	ReturnsFresh     bool
	ReturnsAlias     bool
	AliasesArgument  int
	ReturnsBorrow    bool
	BorrowsArguments []int
	BorrowMutable    bool
	Receiver         typechecker.ResourceParameterMode
	Trusted          bool
}

func factsByCallable(declarations []typechecker.ResourceProtocolDeclaration) map[string]viaFacts {
	out := map[string]viaFacts{}
	for _, declaration := range declarations {
		for _, transition := range declaration.Transitions {
			parameters := append([]typechecker.ResourceParameterDeclaration(nil), transition.Parameters...)
			sort.Slice(parameters, func(i, j int) bool { return parameters[i].Index < parameters[j].Index })
			borrows := append([]int(nil), transition.BorrowsArguments...)
			sort.Ints(borrows)
			out[transition.Callable] = viaFacts{
				From: transition.From, To: transition.To, Parameters: parameters,
				ReturnsFresh: transition.ReturnsFresh, ReturnsAlias: transition.ReturnsAlias, AliasesArgument: transition.AliasesArgument,
				ReturnsBorrow: transition.ReturnsBorrow, BorrowsArguments: borrows, BorrowMutable: transition.BorrowMutable,
				Receiver: transition.Receiver, Trusted: transition.Trusted,
			}
		}
	}
	return out
}

// TestViaResultsElaborateToTheInjectedFacts is the correspondence check:
// the protocol above elaborates to the same resource facts, callable by
// callable, that the borrowed-result and mutable-reborrow tests inject.
func TestViaResultsElaborateToTheInjectedFacts(t *testing.T) {
	tree, err := New().WithSource("facts.oak", mutableReborrowBase+viaResultsProtocol).Parse().Get()
	if err != nil {
		t.Fatalf("parse: %v", err)
	}
	facts, err := lowerProtocols(tree)
	if err != nil {
		t.Fatalf("lowerProtocols: %v", err)
	}
	got := factsByCallable(facts)
	want := factsByCallable(mutableReborrowDeclarations())
	if len(got) != len(want) {
		t.Fatalf("source declares %d callables, injection declares %d", len(got), len(want))
	}
	for callable, wantFacts := range want {
		gotFacts, declared := got[callable]
		if !declared {
			t.Errorf("%s: not declared from source", callable)
			continue
		}
		if !reflect.DeepEqual(gotFacts, wantFacts) {
			t.Errorf("%s:\n  source:    %+v\n  injection: %+v", callable, gotFacts, wantFacts)
		}
	}
	if facts[0].Name != "ArenaLifecycle" || facts[0].Initial != "Open" || !reflect.DeepEqual(facts[0].ResourceTypes, []string{"Arena", "Cursor"}) {
		t.Errorf("protocol shape: %+v", facts[0])
	}
}

func TestViaResultsBorrowedResultsFromSource(t *testing.T) {
	if err := checkViaResults(t, "shared", `
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
`); err != nil {
		t.Fatalf("shared use beside a live borrowed result must be accepted: %v", err)
	}
	expectCode(t, "owner-mutated", checkViaResults(t, "owner", `
f: (a: Arena): u32 {
  c: Cursor = cursor_of(a)
  mutate(a)
  read(c)
  0
}
`), typechecker.CodeResourceDependentResult)
	expectCode(t, "owner-suspended", checkViaResults(t, "suspended", `
f: (a: Arena): u32 {
  c: Cursor = mut_cursor(a)
  inspect(a)
  bump(c)
  0
}
`), typechecker.CodeResourceSuspendedOwner)
}

func TestViaResultsBodiesAreHeldToTheirClaim(t *testing.T) {
	// A shared borrow returned under a declared mutable reborrow is the
	// widening OAK-B0117 exists to catch.
	widening := strings.Replace(viaResultsProtocol, "}\n", "  wide: Open -> Open via wrap(borrowed mut a): borrow mut a\n}\n", 1)
	_, err := New().WithSource("widen.oak", mutableReborrowBase+widening+`
wrap: (a: Arena): Cursor = cursor_of(a)
`).Check().Get()
	expectCode(t, "widening", err, typechecker.CodeResourceResultContract)
}

const viaHandleBase = `
Handle: type = Live: u32 | Dead
open_handle: (id: u32): Handle = Handle.Live(id)
inspect_handle: (h: Handle): () = {}
close_handle: (h: Handle): () = {}
peek_handle: (h: Handle): Handle = h
renew_handle: (h: Handle): Handle = h
fn (h: Handle) peek(): u32 = u32(1)
fn (h: Handle) close(): () = {}
fn (h: Handle) merge(other: Handle): () = {}
`

func checkViaHandle(t *testing.T, name, protocol, body string) error {
	t.Helper()
	_, err := New().WithSource(name+".oak", viaHandleBase+protocol+body).Check().Get()
	return err
}

func TestViaResultsAliasAndFresh(t *testing.T) {
	protocol := `
Lifecycle: protocol = {
  resource Handle
  initial Open
  make: Open -> Open via open_handle(): fresh
  look: Open -> Open via inspect_handle(borrowed h)
  shut: Open -> Closed via close_handle(consumed h)
  same: Open -> Open via peek_handle(borrowed h): alias h
  RENEW
}
`
	// An alias result may return its borrowed parameter (not retention),
	// and the caller learns the result is the argument under a new name.
	honest := strings.Replace(protocol, "  RENEW\n", "", 1)
	if err := checkViaHandle(t, "alias-ok", honest, ""); err != nil {
		t.Fatalf("an alias-return body may return the aliased parameter: %v", err)
	}
	expectCode(t, "alias-consumed", checkViaHandle(t, "alias-consumed", honest, `
f: (h: Handle): u32 {
  g: Handle = peek_handle(h)
  close_handle(g)
  inspect_handle(h)
  u32(0)
}
`), typechecker.CodeResourceUsedAfterConsume)
	// The same body without the alias declaration retains a borrowed
	// parameter (OAK-B0114).
	retained := strings.Replace(honest, "via peek_handle(borrowed h): alias h", "via peek_handle(borrowed h)", 1)
	expectCode(t, "retained", checkViaHandle(t, "retained", retained, ""), typechecker.CodeResourceParameterForwarded)
	// A fresh claim over a body that returns its parameter is a lie.
	lie := strings.Replace(protocol, "  RENEW\n", "  renew: Open -> Open via renew_handle(borrowed h): fresh\n", 1)
	expectCode(t, "fresh-lie", checkViaHandle(t, "fresh-lie", lie, ""), typechecker.CodeResourceResultContract)
}

func TestViaResultsTrustedBoundary(t *testing.T) {
	// cursor_raw returns the result of make_cursor, an operation with no
	// resource contract, so its provenance is unknown and the checker
	// cannot validate an alias claim over the body: without `unsafe` the
	// claim is OAK-B0117; with it the claim is recorded as an assumption
	// and callers reason from it — consuming the arena consumes the cursor
	// it is declared to alias. (A record literal mentioning no other
	// resource would satisfy the claim on its own: a typestate transition
	// rebuilds its handle that way, 112-protocols.md section 5a.)
	claim := func(marker string) string {
		return strings.Replace(viaResultsProtocol, "}\n", "  raw: Open -> Open via "+marker+"cursor_raw(borrowed a): alias a\n}\n", 1)
	}
	body := "\nmake_cursor: (pos: u32): Cursor = Cursor { pos: pos }\ncursor_raw: (a: Arena): Cursor = make_cursor(a.id)\n"
	_, err := New().WithSource("untrusted.oak", mutableReborrowBase+claim("")+body).Check().Get()
	expectCode(t, "untrusted-alias", err, typechecker.CodeResourceResultContract)
	if _, err := New().WithSource("trusted.oak", mutableReborrowBase+claim("unsafe ")+body).Check().Get(); err != nil {
		t.Fatalf("a trusted result claim is not validated against the body: %v", err)
	}
	_, err = New().WithSource("trusted-caller.oak", mutableReborrowBase+claim("unsafe ")+body+`
f: (a: Arena): u32 {
  c: Cursor = cursor_raw(a)
  free(a)
  read(c)
  0
}
`).Check().Get()
	expectCode(t, "trusted-alias-consumed", err, typechecker.CodeResourceUsedAfterConsume)
	// Trust covers the result identity only: entry authority and retention
	// are still checked, so a trusted line cannot launder a borrowed
	// parameter into a return value.
	retention := strings.Replace(viaResultsProtocol, "}\n", "  keep: Open -> Open via unsafe keep(borrowed a): fresh\n}\n", 1)
	_, err = New().WithSource("trusted-retention.oak", mutableReborrowBase+retention+"\nkeep: (a: Arena): Arena = a\n").Check().Get()
	expectCode(t, "trusted-retention", err, typechecker.CodeResourceParameterForwarded)
}

const viaWithEach = `
with_each: (op: (Handle) -> (), h: Handle): u32 {
  op(h)
  op(h)
  u32(0)
}
`

func TestViaResultsCallableContracts(t *testing.T) {
	protocol := viaWithEach + `
Lifecycle: protocol = {
  resource Handle
  initial Open
  look: Open -> Open via inspect_handle(borrowed h)
  shut: Open -> Closed via close_handle(consumed h)
  each: Open -> Open via with_each(op(borrowed), borrowed h)
}
`
	if err := checkViaHandle(t, "contract-ok", protocol, `
f: (h: Handle): u32 = with_each(inspect_handle, h)
`); err != nil {
		t.Fatalf("a borrowed function satisfies a borrowed callable contract: %v", err)
	}
	expectCode(t, "contract-mismatch", checkViaHandle(t, "contract-mismatch", protocol, `
f: (h: Handle): u32 = with_each(close_handle, h)
`), typechecker.CodeResourceCallableContractMismatch)
}

func TestViaResultsMethods(t *testing.T) {
	protocol := `
Lifecycle: protocol = {
  resource Handle
  initial Open
  look: Open -> Open via Handle.peek(borrowed receiver)
  shut: Open -> Closed via Handle.close(consumed receiver)
  join: Open -> Open via Handle.merge(borrowed mut receiver, borrowed other)
}
`
	expectCode(t, "consumed-receiver", checkViaHandle(t, "consumed-receiver", protocol, `
f: (h: Handle): u32 {
  h.close()
  h.peek()
}
`), typechecker.CodeResourceUsedAfterConsume)
	if err := checkViaHandle(t, "borrowed-receiver", protocol, `
f: (h: Handle, g: Handle): u32 {
  h.peek()
  h.merge(g)
  h.peek()
}
`); err != nil {
		t.Fatalf("borrowed and mutable receivers keep authority: %v", err)
	}
	expectCode(t, "receiver-alias-conflict", checkViaHandle(t, "receiver-alias-conflict", protocol, `
f: (h: Handle): u32 {
  h.merge(h)
  h.peek()
}
`), typechecker.CodeResourceCallAliasConflict)
}

func TestViaResultsShapeErrors(t *testing.T) {
	shape := func(name, line string) {
		t.Helper()
		err := checkViaHandle(t, name, viaWithEach+"Bad: protocol = {\n  resource Handle\n  initial Open\n  look: Open -> Open via inspect_handle(borrowed h)\n  "+line+"\n}\n", "")
		if err == nil || !strings.Contains(err.Error(), CodeProtocolShape) {
			t.Errorf("%s: want %s, got %v", name, CodeProtocolShape, err)
		}
	}
	shape("result names unknown parameter", "same: Open -> Open via peek_handle(borrowed h): alias g")
	shape("result names receiver", "look2: Open -> Open via Handle.peek(borrowed receiver): alias receiver")
	shape("borrow names twice", "same: Open -> Open via peek_handle(borrowed h): borrow h, h")
	shape("contract on non-function", "same: Open -> Open via peek_handle(h(borrowed))")
	shape("contract arity", "each: Open -> Open via with_each(op(borrowed, _), borrowed h)")
	shape("empty contract", "each: Open -> Open via with_each(op(_), borrowed h)")
	shape("trusted without result", "same: Open -> Open via unsafe peek_handle(borrowed h)")
	shape("unknown method", "look2: Open -> Open via Handle.inspect(borrowed receiver)")
	shape("method without type", "look2: Open -> Open via peek(borrowed receiver)")

	parse := func(name, line, want string) {
		t.Helper()
		err := checkViaHandle(t, name, viaWithEach+"Bad: protocol = {\n  resource Handle\n  initial Open\n  "+line+"\n}\n", "")
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("%s: want %q, got %v", name, want, err)
		}
	}
	parse("unknown result word", "same: Open -> Open via peek_handle(borrowed h): owned h", "expected a result identity")
	parse("unknown contract mode", "each: Open -> Open via with_each(op(owned), borrowed h)", "expected a parameter mode")
	parse("contract result word", "each: Open -> Open via with_each(op(borrowed): alias, borrowed h)", "a callable contract's result is `fresh`")
}
