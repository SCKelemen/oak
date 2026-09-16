package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Stores past conditionals (docs/spec/94-assembler.md §9): the machine
// side, folding every path to its end, logs a store after a conditional
// once per path and the log doubles at every conditional, so the two
// sides' logs do not align write by write and the whole memory would go
// to the diagrams, which the symbolic-index reads exhaust. Verify defers
// that decision and runs the body again merging the paths at their
// joins, whose log matches the Oak side's write for write; the pairs then
// decide with the machine's reads through the log replaced by the Oak
// side's over the prefixes already proven (alignReads), the Oak guard on
// both sides of a proven guard pair, and the join's tautologies and
// duplicate conjuncts folded (conjoin, disjoin). The body is the
// prover's protocol_line_done verbatim: seven guarded pushes through an
// accumulator whose stack pointer lives in the same span, then an
// unconditional and a conditional store — evidence after minutes before,
// proven in seconds now.
const nativeGuardedWritesProgram = `
Par: type = struct {
  tokens_at: u32,
  strings_at: u32,
  pool_at: u32,
  types_at: u32,
  funcs_at: u32,
  params_at: u32,
  records_at: u32,
  fields_at: u32,
  adts_at: u32,
  variants_at: u32,
  nodes_at: u32,
  lists_at: u32,
  frames_at: u32,
  acc_at: u32,
  pextra_at: u32,
  protos_at: u32,
  state_at: u32,
  total: u32,
  out_total: u32
}
PX_ACC: u32 = 16384
PS_FAILED: u32 = 0
PS_SP: u32 = 1
PS_RET: u32 = 2
PS_ACC_SP: u32 = 4
PS_CUR: u32 = 5
PS_NTOKENS: u32 = 6
PP_ENTRY: u32 = 0
pst: (p: Par, w: [*]u32, k: u32): u32 = w[p.state_at + k]
set_pst: (p: Par, w: [*]u32, k: u32, v: u32): () { w[p.state_at + k] = v }
cur: (p: Par, w: [*]u32): u32 = pst(p, w, PS_CUR)
px_fail: (p: Par, w: [*]u32, code: u32): () {
  w[p.state_at + PS_FAILED] == u32(0) ? { w[p.state_at + PS_FAILED] = code } | { }
}
px_acc_push: (p: Par, w: [*]u32, v: u32): () {
  sp: u32 = pst(p, w, PS_ACC_SP)
  sp >= PX_ACC ? { px_fail(p, w, u32(260)) } | {
    w[p.acc_at + sp] = v
    set_pst(p, w, PS_ACC_SP, sp + u32(1))
  }
}
px_advance: (p: Par, w: [*]u32): () {
  c: u32 = cur(p, w)
  c + u32(1) < pst(p, w, PS_NTOKENS) ? { set_pst(p, w, PS_CUR, c + u32(1)) } | { }
}
protocol_line_done: (p: Par, w: [*]u32, at: u32): () {
  px_acc_push(p, w, w[at + u32(5)])
  px_acc_push(p, w, w[at + u32(6)])
  px_acc_push(p, w, w[at + u32(7)])
  px_acc_push(p, w, w[at + u32(8)])
  px_acc_push(p, w, w[at + u32(9)])
  px_acc_push(p, w, w[at + u32(10)])
  px_acc_push(p, w, w[at + u32(11)])
  w[at + u32(1)] = PP_ENTRY
  px_advance(p, w)
}

main: (): i32 {
  42
}
`

func TestE2ENativeGuardedWrites(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("guarded.oak", nativeGuardedWritesProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_guarded_writes", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native guarded writes: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	if !strings.Contains(joined, "asm unit protocol_line_done: proven equal to its Oak body in the span memory it writes (w)") {
		t.Errorf("protocol_line_done's seven guarded pushes and the stores after them must be proven write by write; diagnostics:\n%s", joined)
	}
}
