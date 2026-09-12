package prove

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
)

func check(t *testing.T, src string) *compiler.SemanticModel {
	t.Helper()
	model, err := compiler.New().WithSyntaxRewrite(ProtocolObligations).WithSource("theorems.oak", src).Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	return model
}

// The exhaustive decider settles theorems over small finite domains, finds
// counterexamples, and leaves the rest open with a reason
// (docs/spec/125-verification.md sections 2 and 3).
func TestTheoremsLadder(t *testing.T) {
	src := `
Color: type = Red | Green | Blue

next: (c: Color): Color = c ? | .Red => .Green | .Green => .Blue | .Blue => .Red

add_commutes: theorem (x: u8, y: u8) { x + y == y + x }

wraps: theorem (x: u8) = x + u8(255) == x - u8(1)

not_monotone: theorem (x: u8, y: u8) { !(x < y) || x + u8(1) < y + u8(1) }

cycle: theorem (c: Color) { next(next(next(c))) == c }

implies_true: theorem (a: Bool, b: Bool) = (!a || b) == (a ? b | true)

wide: theorem (x: u32) { x + u32(1) - u32(1) == x }

main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	want := map[string]Status{
		"add_commutes": Decided, "wraps": Decided, "not_monotone": Refuted, "cycle": Decided,
		"implies_true": Decided, "wide": Decided,
	}
	if len(results) != len(want) {
		t.Fatalf("got %d results, want %d: %+v", len(results), len(want), results)
	}
	for _, r := range results {
		if r.Status != want[r.Name] {
			t.Errorf("%s: status %s (%s), want %s", r.Name, r.Status, r.Detail, want[r.Name])
		}
	}
	for _, r := range results {
		switch r.Name {
		case "not_monotone":
			if !strings.Contains(r.Detail, "x = 255, y = 255") && !strings.Contains(r.Detail, "counterexample") {
				t.Errorf("not_monotone: detail %q", r.Detail)
			}
		case "add_commutes":
			if r.Detail != "all 65536 cases" {
				t.Errorf("add_commutes: detail %q", r.Detail)
			}
		case "wide":
			if !strings.Contains(r.Detail, "bit level") {
				t.Errorf("wide: detail %q", r.Detail)
			}
		}
	}
}

// Shape errors are reported with their code; a theorem's body must be Bool.
func TestTheoremShape(t *testing.T) {
	for _, tc := range []struct{ name, src, want string }{
		{"generic", "t[T]: theorem (x: T) { true }\nmain: (): i32 = 0\n", "OAK-V0001"},
		{"return", "t: theorem (x: u8): Bool { true }\nmain: (): i32 = 0\n", "declares no return type"},
		{"body", "t: theorem (x: u8) { x + u8(1) }\nmain: (): i32 = 0\n", "Bool"},
	} {
		_, err := compiler.New().WithSource("shape.oak", tc.src).Check().Get()
		if err == nil || !strings.Contains(err.Error(), tc.want) {
			t.Errorf("%s: err = %v, want %q", tc.name, err, tc.want)
		}
	}
}

// A theorem is an ordinary Bool function to the rest of the program: it
// compiles, and it can be called.
func TestTheoremCompiles(t *testing.T) {
	src := `
even_or_odd: theorem (x: u8) { x % u8(2) == u8(0) || x % u8(2) == u8(1) }
main: (): i32 = even_or_odd(u8(3)) ? 0 | 1
`
	output, err := compiler.New().WithSource("call.oak", src).EmitC().Get()
	if err != nil {
		t.Fatalf("compile failed: %v", err)
	}
	if !strings.Contains(output, "oak_even_or_odd") {
		t.Fatalf("theorem not compiled as a function:\n%s", output)
	}
}

// A protocol is a model: its projections are ordinary functions, so an
// inductive invariant is two theorems over the projected types, and the
// exhaustive decider checks them on the finite state space — here finding
// the wraparound of an 8-bit counter (docs/spec/125-verification.md §2a).
func TestProtocolInvariant(t *testing.T) {
	src := `
Turnstile: protocol = {
  data { coins: u8 }
  init { coins: u8(0) }
  initial Locked
  coin: Locked -> Unlocked then { data.coins = data.coins + u8(1) }
  coin: Unlocked -> Unlocked then { data.coins = data.coins + u8(1) }
  push: Unlocked -> Locked
  push: Locked -> Locked
}

paid: (s: TurnstileState, d: TurnstileData): Bool = s == .Locked || d.coins > u8(0)

paid_initially: theorem () { paid(turnstile_initial(), turnstile_initial_data()) }

paid_preserved: theorem (s: TurnstileState, d: TurnstileData, step: TurnstileStep) {
  buf: [1]TurnstileData = [1]TurnstileData{ d }
  !(paid(s, d) && turnstile_legal(s, d, step)) || paid(turnstile_next(s, span(&buf), step), buf[0])
}

main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 2 {
		t.Fatalf("results: %+v", results)
	}
	if results[0].Status != Decided || results[0].Detail != "all 1 cases" {
		t.Errorf("paid_initially: %+v", results[0])
	}
	if results[1].Status != Refuted || !strings.Contains(results[1].Detail, "coins: 255") {
		t.Errorf("paid_preserved: %+v (the 8-bit counter wraps at 255)", results[1])
	}
}

// The bit-level decider covers the 32- and 64-bit statements the exhaustive
// decider cannot reach, refutes with a counterexample, and leaves calls and
// data-dependent loops to Lean (docs/spec/125-verification.md §3).
func TestBitLevelDecider(t *testing.T) {
	src := `
double: (x: u32): u32 = x + x
rotl: (x: u32, n: u32): u32 = (x << (n & u32(31))) | (x >> ((u32(32) - n) & u32(31)))
rotr: (x: u32, n: u32): u32 = (x >> (n & u32(31))) | (x << ((u32(32) - n) & u32(31)))
loops_forever: (x: u32): u32 = x == u32(0) ? u32(0) | loops_forever(x - u32(1))
count8: (i: u32, acc: u32): u32 = i == u32(8) ? acc | count8(i + u32(1), acc + u32(2))

shift_is_double: theorem (x: u32) { x << u32(1) == x + x }
mask_bound: theorem (x: u64, m: u64) { (x & m) <= m }
xor_cancel: theorem (a: u32, b: u32) { (a ^ b) ^ b == a }
overflow: theorem (x: u32) { x + u32(1) > x }
signed_wrap: theorem (x: i32) { x - x == i32(0) }
calls: theorem (x: u32) { double(x) == x * u32(2) }
rotations: theorem (x: u32, n: u32) { rotr(rotl(x, n), n) == x }
unmasked: theorem (x: u32, n: u32) { (x << n) >> n <= x }
recursion: theorem (x: u32) { loops_forever(x) == u32(0) }
tail_counted: theorem (x: u32) { count8(u32(0), x) == x + u32(16) }
counted: theorem (x: u32) {
  acc: u32 = 0
  i: u32 = 0
  while i < u32(4) {
    acc = acc + x
    i = i + u32(1)
  }
  acc == x * u32(4)
}
main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	want := map[string]Status{
		"shift_is_double": Decided, "mask_bound": Decided, "xor_cancel": Decided, "overflow": Refuted,
		"signed_wrap": Decided, "calls": Decided, "counted": Decided, "rotations": Decided, "recursion": Open, "unmasked": Refuted, "tail_counted": Decided,
	}
	for _, r := range results {
		if r.Status != want[r.Name] {
			t.Errorf("%s: status %s (%s), want %s", r.Name, r.Status, r.Detail, want[r.Name])
		}
		if r.Name == "overflow" && !strings.Contains(r.Detail, "x=4294967295") {
			t.Errorf("overflow: detail %q", r.Detail)
		}
		if r.Name == "unmasked" && !strings.Contains(r.Detail, "traps") {
			t.Errorf("unmasked: detail %q", r.Detail)
		}
	}
}

// An invariant candidate — a theorem over a protocol's projected state and
// data — gets its base and step obligations generated; a machine without
// data, with a payload-carrying step, enumerates the payload
// (docs/spec/125-verification.md §2a).
func TestGeneratedObligations(t *testing.T) {
	src := `
Turnstile: protocol = {
  data { coins: u8 }
  init { coins: u8(0) }
  initial Locked
  coin: Locked -> Unlocked then { data.coins = data.coins + u8(1) }
  coin: Unlocked -> Unlocked then { data.coins = data.coins + u8(1) }
  push: Unlocked -> Locked
  push: Locked -> Locked
}

paid: theorem (s: TurnstileState, d: TurnstileData) { s == .Locked || d.coins > u8(0) }
counted: theorem (s: TurnstileState, d: TurnstileData) { d.coins == d.coins }

Irq: protocol = {
  initial Idle
  inject: Idle -> Pending
  acknowledge: Pending -> Active
  eoi: Active -> Idle
  program(compare: u8): Idle -> Idle
}

never_stuck: theorem (s: IrqState) { s == .Idle || s == .Pending || s == .Active }

main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	got := map[string]Result{}
	for _, r := range results {
		got[r.Name] = r
	}
	want := map[string]Status{
		"paid":    Refuted,
		"counted": Decided, "counted__base": Decided, "counted__step": Decided,
		"never_stuck": Decided, "never_stuck__base": Decided, "never_stuck__step": Decided,
	}
	for name, status := range want {
		r, found := got[name]
		if !found {
			t.Errorf("%s: missing (%v)", name, results)
			continue
		}
		if r.Status != status {
			t.Errorf("%s: status %s (%s), want %s", name, r.Status, r.Detail, status)
		}
	}
	if !strings.Contains(got["paid"].Detail, "coins: 255") {
		t.Errorf("paid: %s", got["paid"].Detail)
	}
	// The inductive step's counterexample sits at coins = 255; the reachable
	// exploration then names a state a run actually reaches (the wrapped
	// counter, Unlocked with no coins), keeping the inductive detail.
	if !strings.HasPrefix(got["paid"].Detail, "invariant fails at the reachable state Unlocked with {coins: 0} (invariant is not preserved: ") {
		t.Errorf("paid: %s", got["paid"].Detail)
	}
	if _, kept := got["paid__step"]; kept {
		t.Errorf("paid__step: the obligation rows are folded into the reachable verdict")
	}
	if !strings.HasPrefix(got["counted"].Detail, "invariant: base all 1 cases, step all") {
		t.Errorf("counted: %s", got["counted"].Detail)
	}
	// The payload-carrying step enumerates: 3 states × (3 + 256) steps.
	if got["never_stuck__step"].Detail != "all 777 cases" {
		t.Errorf("never_stuck__step: %s", got["never_stuck__step"].Detail)
	}
	if inv, ok := IsObligation("paid__step"); !ok || inv != "paid" {
		t.Errorf("IsObligation: %s %v", inv, ok)
	}
}

// A parameter of a refinement type ranges over the base values its
// construction accepts (docs/spec/20-types.md section 12).
func TestRefinedDomains(t *testing.T) {
	src := `
Digit: type = u8 where value < u8(10)
Even: type = u8 where value % u8(2) == u8(0)

digits_small: theorem (d: Digit) { u32(d) * u32(9) < u32(100) }
even_half: theorem (e: Even) { (e / u8(2)) * u8(2) == e }
main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 2 || results[0].Status != Decided || results[0].Detail != "all 10 cases" ||
		results[1].Status != Decided || results[1].Detail != "all 128 cases" {
		t.Fatalf("results: %+v", results)
	}
}

// A generic refinement's instantiation is enumerated like any refinement:
// the specialized predicate filters the base (docs/spec/20-types.md
// section 12.1).
func TestRefinedTemplateDomains(t *testing.T) {
	src := `
IrqId[N: u32]: type = u16 where value < N

irq_small: theorem (i: IrqId[4]) { u32(i) + u32(1) < u32(5) }
irq_wide: theorem (i: IrqId[300]) { u32(i) < u32(300) }
main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 2 || results[0].Status != Decided || results[0].Detail != "all 4 cases" ||
		results[1].Status != Decided || results[1].Detail != "all 300 cases" {
		t.Fatalf("results: %+v", results)
	}
}

// The bit-level decider sees a refined parameter as its base under the
// predicate as a hypothesis, and a construction in a body as a trap
// obligation (docs/spec/125-verification.md section 3).
func TestRefinedBitLevel(t *testing.T) {
	src := `
Pos: type = u32 where value >= u32(1) && value < u32(1000)

step: (p: Pos): u32 = u32(p) - u32(1)

step_bounded: theorem (p: Pos) { step(p) < u32(999) }
step_wide: theorem (p: Pos) { step(p) < u32(500) }
construct_traps: theorem (n: u32) { u32(Pos(n)) < u32(1000) }
construct_safe: theorem (n: u32) { u32(Pos((n & u32(511)) + u32(1))) < u32(1000) }
main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	got := map[string]Result{}
	for _, r := range results {
		got[r.Name] = r
	}
	if r := got["step_bounded"]; r.Status != Decided || !strings.Contains(r.Detail, "bit level") {
		t.Errorf("step_bounded: %+v", r)
	}
	if r := got["step_wide"]; r.Status != Refuted || !strings.Contains(r.Detail, "counterexample") {
		t.Errorf("step_wide: %+v", r)
	}
	if r := got["construct_traps"]; r.Status != Refuted || !strings.Contains(r.Detail, "traps") {
		t.Errorf("construct_traps: %+v", r)
	}
	if r := got["construct_safe"]; r.Status != Decided || !strings.Contains(r.Detail, "bit level") {
		t.Errorf("construct_safe: %+v", r)
	}
}

// Strings evaluate in the interpreter (str_bytes, str_from_utf8, len), so
// a closed theorem over them is decided exhaustively.
func TestStringTheorems(t *testing.T) {
	src := `
greet: (): string = "hi"
size: (s: string): u32 = len(str_bytes(s))
greeting_size: theorem () { size(greet()) == u32(2) }
main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 1 || results[0].Status != Decided || results[0].Detail != "all 1 cases" {
		t.Fatalf("results: %+v", results)
	}
}

// Protocol liveness (docs/spec/125-verification.md section 2b): the
// `eventually` entries are decided over the reachable states of the
// projection under the declared fairness.
func TestProtocolLiveness(t *testing.T) {
	quantum := func(fairness string) string {
		return `
Quantum: protocol = {
  data { budget: u32 }
  init { budget: u32(2) }
  initial Running
  tick: Running -> Running when data.budget > u32(1) then { data.budget = data.budget - u32(1) }
  tick: Running -> Yielded when data.budget <= u32(1) then { data.budget = u32(2) }
  resume: Yielded -> Running
  signal(on: Bool): Running -> Running
` + fairness + `
  eventually Yielded
  eventually Running -> Yielded
  eventually Yielded -> Running
  eventually Running -> data.budget == u32(1)
}
main: (): i32 = 0
`
	}
	results, err := Theorems(check(t, quantum("  fair tick\n  fair resume\n  fair signal\n")), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 4 {
		t.Fatalf("results: %+v", results)
	}
	for _, r := range results {
		if r.Status != Decided || !strings.Contains(r.Detail, "holds on all 3 reachable states under fair tick, fair resume, fair signal") {
			t.Errorf("fair: %+v", r)
		}
	}
	results, err = Theorems(check(t, quantum("")), 0)
	if err != nil {
		t.Fatal(err)
	}
	for _, r := range results {
		if r.Status != Refuted || !strings.Contains(r.Detail, "counterexample with no fairness declared") {
			t.Errorf("unfair: %+v", r)
		}
	}
	if !strings.Contains(results[0].Detail, "eventually Yielded: counterexample") || !strings.Contains(results[0].Detail, "from Running with {budget: 2}") {
		t.Errorf("counterexample detail: %s", results[0].Detail)
	}

	// An intermittently enabled step needs strong fairness: under weak
	// fairness the flip-flop cycle is a fair trap (go is disabled in B).
	toggle := func(go_ string) string {
		return "Toggle: protocol = {\n  initial A\n  flip: A -> B\n  flop: B -> A\n  go: A -> Done\n  fair flip\n  fair flop\n  " + go_ + " go\n  eventually Done\n}\nmain: (): i32 = 0\n"
	}
	results, err = Theorems(check(t, toggle("strongly fair")), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 1 || results[0].Status != Decided {
		t.Fatalf("strong: %+v", results)
	}
	results, err = Theorems(check(t, toggle("fair")), 0)
	if err != nil {
		t.Fatal(err)
	}
	if len(results) != 1 || results[0].Status != Refuted || !strings.Contains(results[0].Detail, "staying within {A; B}") {
		t.Fatalf("weak: %+v", results)
	}
}

// An invariant over a data domain the exhaustive decider cannot enumerate
// (a u32 budget) is decided inductively at the bit level; a false one is
// refuted there and reported at a state a run reaches.
func TestInvariantOverReachableStates(t *testing.T) {
	src := `
Quantum: protocol = {
  data { budget: u32 }
  init { budget: u32(2) }
  initial Running
  tick: Running -> Running when data.budget > u32(1) then { data.budget = data.budget - u32(1) }
  tick: Running -> Yielded when data.budget <= u32(1) then { data.budget = u32(2) }
  resume: Yielded -> Running
}

bounded: theorem (s: QuantumState, d: QuantumData) { d.budget >= u32(1) && d.budget <= u32(2) }
always_full: theorem (s: QuantumState, d: QuantumData) { d.budget == u32(2) }
main: (): i32 = 0
`
	results, err := Theorems(check(t, src), 0)
	if err != nil {
		t.Fatal(err)
	}
	got := map[string]Result{}
	for _, r := range results {
		got[r.Name] = r
	}
	// The inductive step over the u32 record decides at the bit level; the
	// false candidate is refuted there and then named at a reachable state.
	if r := got["bounded"]; r.Status != Decided || !strings.Contains(r.Detail, "step at the bit level") {
		t.Errorf("bounded: %+v", r)
	}
	if r := got["always_full"]; r.Status != Refuted || !strings.Contains(r.Detail, "fails at the reachable state Running with {budget: 1}") {
		t.Errorf("always_full: %+v", r)
	}
}
