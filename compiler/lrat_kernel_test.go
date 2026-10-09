package compiler

import (
	"context"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/internal/lrat"
)

func lratKernelSource(t *testing.T) string {
	t.Helper()
	source, err := os.ReadFile(filepath.Join("..", "prove", "solver", "lrat.oak"))
	if err != nil {
		t.Fatal(err)
	}
	return string(source)
}

// This exercises the actual Oak checker with raw words and independently
// bounded scratch. The Go encoder and the allocating solver driver are not
// involved: they would filter out precisely the hostile inputs under test.
func TestLRATKernelRawWords(t *testing.T) {
	type testCase struct {
		name  string
		words []uint32
		out   uint32
		want  int // -1: rejection required; -2: acceptance must agree with Go
	}
	var cases []testCase
	add := func(name string, words []uint32, want int) {
		cases = append(cases, testCase{name, words, 3, want})
	}
	record := func(vars uint32, initial, steps []uint32, clauses uint32) []uint32 {
		words := []uint32{lrat.Magic, vars, clauses, uint32(len(initial)), uint32(len(steps)), 31, 128, 0}
		words = append(words, initial...)
		return append(words, steps...)
	}
	// (x) / (!x), followed by the empty-clause derivation.
	valid := record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, 0, 2, 1, 2}, 2)
	add("unit conflict", valid, 0)
	add("successive additions", record(2, []uint32{2, 1, 3, 1, 0, 1, 2},
		[]uint32{0, 4, 1, 3, 2, 1, 2, 0, 5, 0, 2, 4, 3}, 3), 0)
	add("refusal after successful addition", record(2, []uint32{2, 1, 3, 1, 0, 1, 2},
		[]uint32{0, 4, 1, 3, 2, 1, 2, 0, 5, 0, 2, 4, 31}, 3), -1)
	add("mixed-width initial clauses", record(2, []uint32{2, 1, 3, 1, 0, 1, 2},
		[]uint32{0, 4, 0, 3, 2, 1, 3}, 3), 0)
	add("invalid second initial clause", record(1, []uint32{1, 1, 1, 2}, nil, 2), -1)
	add("truncated second initial clause", record(1, []uint32{1, 1, 2, 0}, nil, 2), -1)
	add("extra initial length word", record(1, []uint32{1, 1, 0}, nil, 1), -1)
	add("empty deletion advances", record(1, []uint32{1, 1, 1, 0},
		[]uint32{1, 2, 0, 0, 3, 0, 2, 1, 2}, 2), 0)
	add("deletion then addition", record(1, []uint32{1, 1, 1, 1, 1, 0},
		[]uint32{1, 3, 1, 1, 0, 4, 0, 2, 2, 3}, 3), 0)
	add("partial deletion cannot recover", record(1, []uint32{1, 1, 1, 0},
		[]uint32{1, 2, 2, 1, 31, 0, 3, 0, 2, 1, 2}, 2), -1)
	add("maximal addition length", record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, ^uint32(0)}, 2), -1)
	add("maximal deletion length", record(1, []uint32{1, 1, 1, 0}, []uint32{1, 2, ^uint32(0)}, 2), -1)
	add("maximal hint length", record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, 0, ^uint32(0)}, 2), -1)
	add("unknown record cannot recover", record(1, []uint32{1, 1, 1, 0},
		[]uint32{42, 0, 3, 0, 2, 1, 2}, 2), -1)
	add("initial empty", record(0, []uint32{0}, nil, 1), 0)
	add("empty deleted after derivation", record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, 0, 2, 1, 2, 1, 3, 1, 3}, 2), 0)
	add("no empty", record(1, []uint32{1, 1}, nil, 1), -1)
	add("valid addition without empty", record(1, []uint32{1, 1}, []uint32{0, 2, 1, 1, 1, 1}, 1), 6)
	add("non-unit hint", record(2, []uint32{2, 1, 3}, []uint32{0, 2, 0, 1, 1}, 1), -1)
	add("missing hint", record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, 0, 1, 3}, 2), -1)
	add("suffix after conflict", record(1, []uint32{1, 1, 1, 0}, []uint32{0, 3, 0, 3, 1, 2, 1}, 2), -1)
	add("dead hint", record(1, []uint32{1, 1, 1, 0}, []uint32{1, 2, 1, 1, 0, 3, 0, 2, 1, 2}, 2), -1)
	add("duplicate unit literals", record(1, []uint32{2, 1, 1, 1, 0}, []uint32{0, 3, 0, 2, 1, 2}, 2), 0)
	add("tautology", record(1, []uint32{0}, []uint32{0, 2, 2, 1, 0, 0}, 1), 0)
	add("tautology invalid suffix", record(1, []uint32{0}, []uint32{0, 2, 3, 1, 0, 2, 0}, 1), -1)
	add("trailing word", append(append([]uint32(nil), valid...), 42), -1)
	for n := 0; n < len(valid); n++ {
		add(fmt.Sprintf("truncated/%d", n), append([]uint32(nil), valid[:n]...), -1)
	}
	for _, field := range []int{3, 4, 8, 14, 15} {
		for _, count := range []uint32{0xfffffff0, 0xfffffff8, 0xfffffffc, 0xfffffffe, 0xffffffff} {
			words := append([]uint32(nil), valid...)
			words[field] = count
			add(fmt.Sprintf("overflow/%d/%x", field, count), words, -1)
		}
	}
	add("deletion count wraps", record(0, []uint32{0}, []uint32{1, 1, 0xfffffff8}, 1), -1)
	add("addition literals wrap", record(0, []uint32{0}, []uint32{0, 2, 0xfffffff8, 0}, 1), -1)
	add("hint count wraps", record(0, []uint32{0}, []uint32{0, 2, 0, 0xfffffff8}, 1), -1)
	for _, field := range []int{1, 2, 5, 6} {
		words := append([]uint32(nil), valid...)
		words[field] = 0xffffffff
		add(fmt.Sprintf("scratch capacity/%d", field), words, -1)
	}
	for n := uint32(0); n < 3; n++ {
		cases = append(cases, testCase{fmt.Sprintf("short output/%d", n), valid, n, 7})
	}
	// Deterministic mutation checks against the independent Go acceptance
	// kernel. Keep scratch metadata valid: Go does not use those hints.
	rng := rand.New(rand.NewSource(20261006))
	for i := 0; i < 512; i++ {
		words := append([]uint32(nil), valid...)
		index := []int{0, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17}[rng.Intn(14)]
		words[index] = uint32(rng.Intn(24))
		add(fmt.Sprintf("mutation/%d", i), words, -2)
	}
	var data, offsets, sizes, outs []uint32
	for _, tc := range cases {
		offsets = append(offsets, uint32(len(data)))
		sizes = append(sizes, uint32(len(tc.words)))
		outs = append(outs, tc.out)
		data = append(data, tc.words...)
	}
	source := `import(std)
putchar: (ch: c.Int): c.Int = c.extern("putchar")
` + lratKernelSource(t) + `
check_case: (words: []u32, out_n: u32): u32 {
  starts: [32]u32
  lengths: [32]u32
  alive: [32]u8
  store: [128]u32
  assign: [8]u8 = [8]u8{0, 0, 0, 0, 0, 0, 0, 0}
  trail: [8]u32
  out: [4]u32 = [4]u32{99, 99, 99, 99}
  status: u32 = 0
  true ? {
    dest: [*]u32 = span(&out)
    status = lrat_check(words, span(&starts), span(&lengths), span(&alive), span(&store), span(&assign), span(&trail), dest[0:out_n])
  } | { }
  assert(out[3] == 99)
  out_n < 3 ? { assert(out[0] == 99 && out[1] == 99 && out[2] == 99) } | { assert(out[0] == status) }
  // Every completed RUP call must undo scratch, even on refusal. The
  // undeclared suffix starts zero and must never be touched either.
  v: u32 = 0
  while v < 8 {
    assert(assign[v] == 0)
    v = v + 1
  }
  status
}

main: (): i32 {
` + fmt.Sprintf("data: [%d]u32 = %s\noffsets: [%d]u32 = %s\nsizes: [%d]u32 = %s\nouts: [%d]u32 = %s\n", len(data), oakU32Array(data), len(offsets), oakU32Array(offsets), len(sizes), oakU32Array(sizes), len(outs), oakU32Array(outs)) + `
  all: []u32 = view(&data)
  i: u32 = 0
  while i < len(offsets) {
    status: u32 = check_case(subslice(all, offsets[i], sizes[i]), outs[i])
    _ = putchar(c.Int(i32_bits_u32(status + 65)))
    i = i + 1
  }
  0
}
`
	output, code, abnormal := buildAndRunOutput(t, "lrat_kernel", source)
	if abnormal || code != 0 || len(output) != len(cases) {
		t.Fatalf("raw kernel exit (%d, %v), %d/%d results: %q", code, abnormal, len(output), len(cases), output)
	}
	for i, tc := range cases {
		got := int(output[i]) - 65
		_, err := lrat.CheckWords(tc.words)
		switch {
		case tc.want >= 0 && got != tc.want:
			t.Errorf("%s: status %d, want %d", tc.name, got, tc.want)
		case tc.want == -1 && got == 0:
			t.Errorf("%s: malformed record accepted", tc.name)
		case tc.want == -2 && (got == 0) != (err == nil):
			t.Errorf("%s: Oak status %d, Go error %v; words %v", tc.name, got, err, tc.words)
		}
	}
	t.Logf("checked %d raw records, including short output spans", len(cases))
}

// Tie the proof to the production guard, not a handwritten equivalent.
func TestLRATKernelBoundsExtract(t *testing.T) {
	lratKernelExtract(t, "LRATBounds", []string{"lrat_fits", "lrat_alloc_fits"})
}

func TestLRATKernelRUPExtract(t *testing.T) {
	lratKernelExtract(t, "LRATRUP", []string{"lrat_rup"})
}

func TestLRATKernelBindingExtract(t *testing.T) {
	lratKernelExtract(t, "LRATBinding", []string{"lrat_matches_formula"})
}

func TestLRATKernelCheckerExtract(t *testing.T) {
	lratKernelExtract(t, "LRATChecker", []string{"lrat_check"})
}

func lratKernelExtract(t *testing.T, module string, roots []string) {
	t.Helper()
	extracted, err := New().WithSource("lrat.oak", lratKernelSource(t)).EmitLeanRoots("Oak."+module, roots).Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(extracted, "sorry") {
		t.Fatal("extraction contains sorry")
	}
	path := filepath.Join("..", "spec", "lean", "Oak", module+"Extracted.lean")
	if os.Getenv("OAK_LEAN_EXTRACT_UPDATE") == "1" {
		if err := os.WriteFile(path, []byte(extracted), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	committed, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	if string(committed) != extracted {
		t.Fatalf("%s extraction drift; regenerate with OAK_LEAN_EXTRACT_UPDATE=1", module)
	}
}

func TestLRATKernelTrailSoundness(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_TRAIL_LEAN") != "" {
			t.Fatal("lake is required for the production LRAT proof gate")
		}
		t.Skip("lake not on PATH; formal CI requires production LRAT proofs")
	}
	source := `import Oak.LRATRecord
open Oak.LRATRUP
example (fuel : Nat) (words : Array UInt32)
    (target_at target_n hints_at hints_n : UInt32) (starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8) (trail : Array UInt32)
    (variables max_id status : UInt32) (starts' lengths' : Array UInt32)
    (alive' : Array UInt8) (store' : Array UInt32) (assign' : Array UInt8) (trail' : Array UInt32)
    (assignCapacity : variables.toNat ≤ assign.size) (trailCapacity : variables.toNat ≤ trail.size)
    (zero : ∀ v, v < variables.toNat → assign.getD v 0 = 0)
    (valid : LiveVariables starts lengths alive store variables max_id)
    (run : lrat_rup words target_at target_n hints_at hints_n starts lengths alive store assign trail variables max_id fuel =
      some (status, starts', lengths', alive', store', assign', trail')) :
    assign'.size = assign.size ∧ trail'.size = trail.size ∧
      ∀ v, v < variables.toNat → assign'.getD v 0 = 0 :=
  production_rup_restores_zero fuel words target_at target_n hints_at hints_n starts lengths alive store assign trail
    variables max_id status starts' lengths' alive' store' assign' trail' assignCapacity trailCapacity zero valid run
open Oak.LRATChecker in
example (fuel : Nat) (words starts lengths : Array UInt32)
    (alive : Array UInt8) (store : Array UInt32) (assign : Array UInt8)
    (variables count max_id store_words at_ end_ : UInt32)
    (reset : Array UInt8) (resetEnd : UInt32) (scratch : Array UInt8) (scratchEnd : UInt32)
    (starts' lengths' : Array UInt32) (alive' : Array UInt8) (store' : Array UInt32)
    (at' used' : UInt32) (empty' : Bool) (c' : UInt32) (a : Oak.RupCheck.Assignment)
    (startCap : max_id.toNat < starts.size) (lengthCap : max_id.toNat < lengths.size)
    (aliveCap : max_id < alive.size.toUInt32) (storeCap : store_words.toNat ≤ store.size)
    (assignCap : variables.toNat ≤ assign.size)
    (wordCap : end_.toNat ≤ words.size) (cursor : at_ ≤ end_) (countBound : count ≤ max_id)
    (input : ∀ clause ∈ initialClauses words at_.toNat count.toNat, Oak.RupCheck.SatisfiesClause a clause)
    (liveRun : lrat_check.loop1 alive true max_id 0 fuel = some (reset, resetEnd))
    (scratchRun : lrat_check.loop2 assign true variables 0 fuel = some (scratch, scratchEnd))
    (run : lrat_check.loop3 words starts lengths reset store Oak.LRATChecker.LRAT_ACCEPTED variables count store_words
      at_ end_ 0 false 1 fuel = some (starts', lengths', alive', store', Oak.LRATChecker.LRAT_ACCEPTED, at', used', empty', c')) :
    InitialState words starts' lengths' alive' store' variables max_id store_words at' end_ used' empty' a ∧
      c'.toNat = count.toNat + 1 ∧ scratch.size = assign.size ∧
      (∀ v, v < variables.toNat → scratch.getD v 0 = 0) :=
  production_initialization fuel words starts lengths alive store assign variables count max_id store_words
    at_ end_ reset resetEnd scratch scratchEnd starts' lengths' alive' store' at' used' empty' c' a
    startCap lengthCap aliveCap storeCap assignCap wordCap cursor countBound input liveRun scratchRun run
open Oak.LRATChecker in
example (fuel : Nat) (words store : Array UInt32) (at_ n m used capacity end_ : UInt32)
    (wc : end_.toNat ≤ words.size) (sc : capacity.toNat ≤ store.size)
    (header : Oak.LRATChecker.lrat_fits at_ 3 end_ fuel = some true)
    (literals : Oak.LRATChecker.lrat_fits (at_ + 3) n end_ fuel = some true)
    (countWord : at_ + 3 + n < end_)
    (hints : Oak.LRATChecker.lrat_fits (at_ + 3 + n + 1) m end_ fuel = some true)
    (space : Oak.LRATChecker.lrat_fits used n capacity fuel = some true) :
    AdditionBounds words store at_ n m used capacity end_ :=
  addition_record_bounds fuel words store at_ n m used capacity end_ wc sc header literals countWord hints space
#print axioms Oak.LRATRUP.production_rup_restores_zero
#print axioms Oak.LRATChecker.production_addition_state
#print axioms Oak.LRATChecker.initial_loop_preserves
#print axioms Oak.LRATChecker.initial_state_from_reset
#print axioms Oak.LRATChecker.production_initialization
#print axioms Oak.LRATChecker.deletion_record_bounds
#print axioms Oak.LRATChecker.addition_record_bounds
#print axioms Oak.LRATChecker.deletion_record_state
#print axioms Oak.LRATChecker.addition_record_state
#print axioms Oak.LRATChecker.record_input_accepted
`
	path := filepath.Join(t.TempDir(), "LRATTrailContract.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.LRATRecord"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("..", "spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("Lean production LRAT proofs: %v (%v)\n%s", err, ctx.Err(), out)
		}
		if strings.Contains(string(out), "sorryAx") {
			t.Fatalf("production LRAT proof depends on a proof hole:\n%s", out)
		}
	}
}

// Initialization must establish the proof's starting invariants from arbitrary
// old buffer contents. Nonzero suffix sentinels also detect excess clearing.
func TestLRATKernelDirtyInitialization(t *testing.T) {
	source := `import(std)
` + lratKernelSource(t) + `
check_dirty: (words: []u32, expected: u32): () {
  starts: [9]u32
  lengths: [9]u32
  alive: [9]u8
  store: [16]u32
  assign: [4]u8 = [4]u8{7, 7, 7, 7}
  trail: [4]u32 = [4]u32{99, 99, 99, 99}
  out: [3]u32
  i: u32 = 0
  while i < 9 {
    starts[i] = 99
    lengths[i] = 99
    alive[i] = 7
    i = i + 1
  }
  i = 0
  while i < 16 { store[i] = 99; i = i + 1 }
  status: u32 = lrat_check(words, span(&starts), span(&lengths), span(&alive), span(&store), span(&assign), span(&trail), span(&out))
  assert(status == expected && out[0] == expected)
  assert(assign[0] == 0 && assign[1] == 0)
  assert(assign[2] == 7 && assign[3] == 7)
  assert(alive[0] == 0 && alive[5] == 0 && alive[6] == 0 && alive[7] == 0)
  assert(alive[8] == 7 && starts[8] == 99 && lengths[8] == 99)
  status == 0 ? {
    assert(alive[1] == 1 && alive[2] == 1 && alive[3] == 1 && alive[4] == 1)
    assert(starts[1] == 0 && lengths[1] == 2)
    assert(starts[2] == 2 && lengths[2] == 1)
    assert(starts[3] == 3 && lengths[3] == 1)
    assert(starts[4] == 4 && lengths[4] == 0)
    assert(store[0] == 1 && store[1] == 3 && store[2] == 0 && store[3] == 2)
    assert(store[4] == 99 && store[15] == 99)
  } | { }
}
main: (): i32 {
  valid: [22]u32 = [22]u32{1280459348, 2, 3, 7, 7, 7, 16, 0, 2, 1, 3, 1, 0, 1, 2, 0, 4, 0, 3, 2, 1, 3}
  invalid: [22]u32 = [22]u32{1280459348, 2, 3, 7, 7, 7, 16, 0, 2, 1, 3, 1, 4, 1, 2, 0, 4, 0, 3, 2, 1, 3}
  check_dirty(view(&valid), 0)
  check_dirty(view(&invalid), 1)
  0
}
`
	_, code, abnormal := buildAndRunOutput(t, "lrat_dirty_initialization", source)
	if abnormal || code != 0 {
		t.Fatalf("dirty initialization exit (%d, %v)", code, abnormal)
	}
}

// Pin whole-record soundness without caller-provided parser traces, fuel
// bounds, initialized scratch, or database invariants.
func TestLRATKernelRecordSoundness(t *testing.T) {
	lake, err := exec.LookPath("lake")
	if err != nil {
		if os.Getenv("OAK_REQUIRE_LRAT_RECORD_LEAN") != "" {
			t.Fatal("lake is required for the production LRAT whole-record gate")
		}
		t.Skip("lake not on PATH; formal CI requires whole-record soundness")
	}
	source := `import Oak.LRATBoundRecord
open Oak.LRATChecker
example (words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (fuel : Nat)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (run : lrat_check words starts lengths alive store assign trail out fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    ¬ ∃ a, InitialModels words (words.getD 2 0).toNat 8 a :=
  production_record_sound words starts lengths alive store assign trail out fuel s l v t x y o run
example (formula words starts lengths : Array UInt32) (alive : Array UInt8)
    (store : Array UInt32) (assign : Array UInt8) (trail out : Array UInt32) (bindingFuel fuel : Nat)
    (s l : Array UInt32) (v : Array UInt8) (t : Array UInt32) (x : Array UInt8) (y o : Array UInt32)
    (binding : Oak.LRATBinding.lrat_matches_formula formula words bindingFuel = some true)
    (run : lrat_check words starts lengths alive store assign trail out fuel = some (LRAT_ACCEPTED, s, l, v, t, x, y, o)) :
    ¬ ∃ a, InitialModels formula (formula.getD 2 0).toNat 8 a :=
  production_bound_record_sound formula words starts lengths alive store assign trail out bindingFuel fuel s l v t x y o binding run
#print axioms Oak.LRATChecker.production_binding_exact
#print axioms Oak.LRATChecker.initial_loop_locality
#print axioms Oak.LRATChecker.production_bound_record_sound
#print axioms Oak.LRATChecker.production_initialization
#print axioms Oak.LRATChecker.steps_loop_models
#print axioms Oak.LRATChecker.checker_eq_body
#print axioms Oak.LRATChecker.production_record_sound
`
	path := filepath.Join(t.TempDir(), "LRATRecordContract.lean")
	if err := os.WriteFile(path, []byte(source), 0600); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 5*time.Minute)
	defer cancel()
	for _, args := range [][]string{{"build", "Oak.LRATBoundRecord"}, {"env", "lean", path}} {
		cmd := exec.CommandContext(ctx, lake, args...)
		cmd.Dir = filepath.Join("..", "spec", "lean")
		out, err := cmd.CombinedOutput()
		if err != nil {
			t.Fatalf("Lean whole-record soundness: %v (%v)\n%s", err, ctx.Err(), out)
		}
		if strings.Contains(string(out), "sorryAx") {
			t.Fatalf("whole-record soundness depends on a proof hole:\n%s", out)
		}
		for _, line := range strings.Split(string(out), "\n") {
			const marker = "depends on axioms: ["
			_, axioms, found := strings.Cut(line, marker)
			if !found {
				continue
			}
			axioms = strings.TrimSuffix(strings.TrimSpace(axioms), "]")
			for _, axiom := range strings.Split(axioms, ",") {
				switch strings.TrimSpace(axiom) {
				case "", "propext", "Classical.choice", "Quot.sound":
				default:
					t.Fatalf("non-foundational axiom in LRAT record proof: %s", line)
				}
			}
		}
	}
}
