package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/typechecker"
)

// Resources through aggregates (docs/spec/50-borrowing.md section 9
// "Resources through aggregates", authority roadmap milestone 5): a
// resource inside an ADT payload is the path root.$Variant; construction
// binds it, a match binding aliases it (inspection keeps the source usable,
// extraction consumes the location), a resource returned inside a variant
// is returned, contracts govern aggregate parameters path by path, and
// generic helpers specialize without erasing authority.
func payloadDeclarations() []typechecker.ResourceProtocolDeclaration {
	mode := func(index int, m typechecker.ResourceParameterMode) typechecker.ResourceParameterDeclaration {
		return typechecker.ResourceParameterDeclaration{Index: index, Mode: m}
	}
	borrowed, mut, consumed := typechecker.ResourceParameterBorrowed, typechecker.ResourceParameterBorrowedMut, typechecker.ResourceParameterConsumed
	return []typechecker.ResourceProtocolDeclaration{{
		Name:          "HandleLifecycle",
		ResourceTypes: []string{"Handle"},
		States:        []string{"Open", "Closed"},
		Initial:       "Open",
		Transitions: []typechecker.ResourceTransitionDeclaration{
			{Name: "open", Callable: "open", From: "Open", To: "Open", ReturnsFresh: true},
			{Name: "inspect", Callable: "inspect", From: "Open", To: "Open", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, borrowed)}},
			{Name: "close", Callable: "close", From: "Open", To: "Closed", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, consumed)}},
			{Name: "update_pair", Callable: "update_pair", From: "Open", To: "Open", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, mut), mode(1, borrowed)}},
			// wrap consumes h and returns it inside Some: an alias result.
			{Name: "wrap", Callable: "wrap", From: "Open", To: "Open", Parameters: []typechecker.ResourceParameterDeclaration{mode(0, consumed)}, ReturnsAlias: true, AliasesArgument: 0},
			// try_open returns a fresh handle inside Ok.
			{Name: "try_open", Callable: "try_open", From: "Open", To: "Open", ReturnsFresh: true},
		},
	}}
}

const payloadBase = `
Option[T]: type = Some: T | None
Result[T, E]: type = Ok: T | Err: E
Handle: type = struct { id: u32 }
Slot: type = Empty | Full: Handle
open: (id: u32): Handle = Handle { id: id }
inspect: (h: Handle): () = {}
close: (h: Handle): () = {}
update_pair: (left: Handle, right: Handle): () = {}
wrap: (h: Handle): Option[Handle] = .Some(h)
try_open: (id: u32): Result[Handle, u32] = .Ok(Handle { id: id })
`

func checkPayloads(t *testing.T, name, body string, extra ...typechecker.ResourceTransitionDeclaration) error {
	t.Helper()
	declarations := payloadDeclarations()
	declarations[0].Transitions = append(declarations[0].Transitions, extra...)
	_, err := New().
		WithSource(name+".oak", payloadBase+body).
		WithResourceProtocols(declarations).
		Check().
		Get()
	return err
}

func TestPayloadInspectionKeepsSourceUsable(t *testing.T) {
	// The payload binding aliases h; borrowed use of it leaves h usable,
	// for Option, Result, and a user ADT alike.
	if err := checkPayloads(t, "inspect", `
f: (h: Handle): u32 {
  o: Option[Handle] = .Some(h)
  o ? | .Some(x) => inspect(x) | .None => {}
  s: Slot = .Full(h)
  s ? | .Full(y) => inspect(y) | .Empty => {}
  inspect(h)
  h.id
}
`); err != nil {
		t.Fatalf("inspecting a payload must leave the source usable: %v", err)
	}
}

func TestPayloadExtractionConsumesLocation(t *testing.T) {
	// Consuming the binding consumes the payload's location, which is h's
	// authority: h is gone, and matching the option again reads a consumed
	// location.
	expectCode(t, "source", checkPayloads(t, "extract-source", `
f: (h: Handle): u32 {
  o: Option[Handle] = .Some(h)
  o ? | .Some(x) => close(x) | .None => {}
  h.id
}
`), typechecker.CodeResourceUsedAfterConsume)
	expectCode(t, "rematch", checkPayloads(t, "extract-rematch", `
f: (h: Handle): u32 {
  o: Option[Handle] = .Some(h)
  o ? | .Some(x) => close(x) | .None => {}
  o ? | .Some(y) => inspect(y) | .None => {}
  0
}
`), typechecker.CodeResourceUsedAfterConsume)
	// A payload of unknown provenance cannot be consumed (fail closed).
	expectCode(t, "unknown", checkPayloads(t, "extract-unknown", `
f: (o: Option[Handle]): u32 {
  o ? | .Some(x) => close(x) | .None => {}
  0
}
`), typechecker.CodeResourceCallAliasConflict)
}

func TestPayloadFromContractedCalls(t *testing.T) {
	// wrap aliases h (consumed): h is gone, the payload is usable. try_open
	// is fresh: the payload is a new class, usable and consumable once.
	expectCode(t, "alias-consumed", checkPayloads(t, "alias", `
f: (h: Handle): u32 {
  o: Option[Handle] = wrap(h)
  inspect(h)
  0
}
`), typechecker.CodeResourceUsedAfterConsume)
	if err := checkPayloads(t, "fresh", `
f: (): u32 {
  r: Result[Handle, u32] = try_open(u32(1))
  r ? | .Ok(x) => close(x) | .Err(e) => {}
  o: Option[Handle] = wrap(open(u32(2)))
  o ? | .Some(y) => close(y) | .None => {}
  try_open(u32(3)) ? | .Ok(z) => close(z) | .Err(e) => {}
  0
}
`); err != nil {
		t.Fatalf("fresh payloads must be usable and consumable once: %v", err)
	}
	expectCode(t, "fresh-twice", checkPayloads(t, "fresh-twice", `
f: (): u32 {
  r: Result[Handle, u32] = try_open(u32(1))
  r ? | .Ok(x) => close(x) | .Err(e) => {}
  r ? | .Ok(y) => close(y) | .Err(e) => {}
  0
}
`), typechecker.CodeResourceUsedAfterConsume)
}

func TestPayloadReturnThroughResult(t *testing.T) {
	consumedAlias := typechecker.ResourceTransitionDeclaration{Name: "lift", Callable: "lift", From: "Open", To: "Open",
		Parameters:   []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}},
		ReturnsAlias: true, AliasesArgument: 0}
	borrowedOnly := typechecker.ResourceTransitionDeclaration{Name: "lift", Callable: "lift", From: "Open", To: "Open",
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}}}
	fresh := typechecker.ResourceTransitionDeclaration{Name: "lift", Callable: "lift", From: "Open", To: "Open",
		Parameters:   []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}},
		ReturnsFresh: true}
	// Returning the consumed parameter inside Ok as an alias is honest and
	// duplicates nothing at the caller.
	if err := checkPayloads(t, "lift-ok", `
lift: (h: Handle): Result[Handle, u32] = .Ok(h)
g: (h: Handle): u32 {
  r: Result[Handle, u32] = lift(h)
  r ? | .Ok(x) => close(x) | .Err(e) => {}
  0
}
`, consumedAlias); err != nil {
		t.Fatalf("returning a consumed parameter inside a variant is honest: %v", err)
	}
	// A borrowed parameter returned inside a variant is retention.
	expectCode(t, "lift-borrowed", checkPayloads(t, "lift-borrowed", `
lift: (h: Handle): Result[Handle, u32] = .Ok(h)
`, borrowedOnly), typechecker.CodeResourceParameterForwarded)
	// A fresh claim over a payload that is the parameter is a lie.
	expectCode(t, "lift-fresh", checkPayloads(t, "lift-fresh", `
lift: (h: Handle): Result[Handle, u32] = .Ok(h)
`, fresh), typechecker.CodeResourceResultContract)
}

func TestPayloadGenericHelperSpecializes(t *testing.T) {
	// A generic helper consuming an Option[Handle] extracts and returns the
	// payload; its contract, declared once, governs the specialization: the
	// caller's option is moved, so matching it afterwards reads a consumed
	// location, and inside the body the payload carries the parameter's
	// entry authority.
	consuming := typechecker.ResourceTransitionDeclaration{Name: "take", Callable: "take", From: "Open", To: "Closed",
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterConsumed}}}
	if err := checkPayloads(t, "take-ok", `
take[T]: (o: Option[Handle], tag: T): Handle {
  o ? | .Some(x) => x | .None => open(u32(0))
}
g: (h: Handle): u32 {
  o: Option[Handle] = .Some(h)
  got: Handle = take(o, u32(7))
  0
}
`, consuming); err != nil {
		t.Fatalf("a consuming generic helper must specialize: %v", err)
	}
	expectCode(t, "take-moved", checkPayloads(t, "take-moved", `
take[T]: (o: Option[Handle], tag: T): Handle {
  o ? | .Some(x) => x | .None => open(u32(0))
}
g: (h: Handle): u32 {
  o: Option[Handle] = .Some(h)
  got: Handle = take(o, true)
  o ? | .Some(y) => inspect(y) | .None => {}
  0
}
`, consuming), typechecker.CodeResourceUsedAfterConsume)
	// Under a borrowed contract the payload may be inspected but not
	// consumed or returned.
	borrowed := consuming
	borrowed.To = "Open"
	borrowed.Parameters = []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowed}}
	if err := checkPayloads(t, "peek-ok", `
take[T]: (o: Option[Handle], tag: T): u32 {
  o ? | .Some(x) => inspect(x) | .None => {}
  0
}
g: (h: Handle): u32 {
  o: Option[Handle] = .Some(h)
  take(o, u32(1))
  inspect(h)
  0
}
`, borrowed); err != nil {
		t.Fatalf("a borrowing generic helper must specialize: %v", err)
	}
	expectCode(t, "peek-consumes", checkPayloads(t, "peek-consumes", `
take[T]: (o: Option[Handle], tag: T): u32 {
  o ? | .Some(x) => close(x) | .None => {}
  0
}
g: (h: Handle): u32 {
  o: Option[Handle] = .Some(h)
  take(o, u32(1))
}
`, borrowed), typechecker.CodeResourceParameterForwarded)
}

func TestPayloadSiblingPathsFailClosed(t *testing.T) {
	// Two fields of one contracted aggregate parameter are never proven
	// distinct, so an exclusive pairing of them fails closed.
	borrowed := typechecker.ResourceTransitionDeclaration{Name: "both", Callable: "both", From: "Open", To: "Open",
		Parameters: []typechecker.ResourceParameterDeclaration{{Index: 0, Mode: typechecker.ResourceParameterBorrowedMut}}}
	err := checkPayloads(t, "siblings", `
Pair: type = struct { a: Handle, b: Handle }
both: (p: Pair): u32 {
  update_pair(p.a, p.b)
  0
}
`, borrowed)
	expectCode(t, "siblings", err, typechecker.CodeResourceCallAliasConflict)
	if !strings.Contains(err.Error(), "aliases the same resource") {
		t.Fatalf("diagnostic should explain the possible aliasing: %v", err)
	}
	// Fields of two different parameters are distinct classes.
	if err := checkPayloads(t, "distinct", `
Pair: type = struct { a: Handle, b: Handle }
both: (p: Pair, q: Pair): u32 {
  update_pair(p.a, q.b)
  0
}
`, typechecker.ResourceTransitionDeclaration{Name: "both", Callable: "both", From: "Open", To: "Open",
		Parameters: []typechecker.ResourceParameterDeclaration{
			{Index: 0, Mode: typechecker.ResourceParameterBorrowedMut}, {Index: 1, Mode: typechecker.ResourceParameterBorrowed}}}); err != nil {
		t.Fatalf("paths of distinct parameters are distinct: %v", err)
	}
}
