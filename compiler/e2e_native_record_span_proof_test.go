package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// Readers of spans of records are proven, not trusted (docs/spec/94-
// assembler.md §9, the OS pilot's V1): a field of an element, an element
// of an array field by a symbolic or constant index, and the N4 shape,
// through a view or a span, with a small element (the shifted add) and a
// 4 KiB one (the umaddl stride); the writers are proven in the leaf
// memories they write. Native exit == C exit.
const nativeRecordSpanProofProgram = `
Node: type = struct { value: u32, next: u32, weight: u64 }
Leaf: type = struct { entries: [512]u64, level: u32, flags: u32 }
Dom: type = struct { pending: [8]u32, count: u32 }

peek: (pool: []Node, i: u32): u32 {
  i < len(pool) ? { pool[i].value + pool[i].next } | { u32(0) }
}

heavy: (pool: [*]Node, i: u32): u64 {
  i < len(pool) ? { pool[i].weight } | { u64(0) }
}

walk: (leaves: [*]Leaf, t: u32, idx: u32): u64 {
  t < len(leaves) && idx < u32(512) ? { leaves[t].entries[idx] + u64(leaves[t].level) } | { u64(0) }
}

fixed: (leaves: []Leaf, t: u32): u64 {
  t < len(leaves) ? { leaves[t].entries[u32(7)] } | { u64(1) }
}

pend: (doms: [*]Dom, d: u32, i: u32): u32 {
  d < len(doms) && i < u32(8) ? { doms[d].pending[i] + doms[d].count } | { u32(0) }
}

set_level: (leaves: [*]Leaf, t: u32, v: u32): () {
  t < len(leaves) ? { leaves[t].level = v; leaves[t].entries[u32(9)] = u64(40); leaves[t].entries[u32(7)] = u64(5) } | { }
}

// Callees taking spans of records: a writer callee and a reader callee,
// the caller proven through the summaries.
bump_value: (pool: [*]Node, i: u32): () {
  i < len(pool) ? { pool[i].value = pool[i].value + u32(1) } | { }
}

node_sum: (pool: [*]Node, i: u32): u32 {
  i < len(pool) ? { pool[i].value + pool[i].next } | { u32(0) }
}

total: (pool: [*]Node, i: u32): u32 {
  bump_value(pool, i)
  node_sum(pool, i)
}

// A writer over a counted loop and a symbolic element index.
fill: (doms: [*]Dom, d: u32, base: u32): u32 {
  d < len(doms) ? {
    i: u32 = u32(0)
    while i < u32(8) {
      doms[d].pending[i] = base + i * u32(2)
      i = i + u32(1)
    }
    doms[d].count = u32(8)
    doms[d].pending[u32(3)] + doms[d].count
  } | { u32(0) }
}

main: (): i32 {
  nodes: [3]Node
  nodes[u32(1)].value = u32(6)
  nodes[u32(1)].next = u32(4)
  nodes[u32(2)].weight = u64(11)
  leaves: [1]Leaf
  doms: [2]Dom
  doms[u32(1)].pending[u32(2)] = u32(8)
  doms[u32(1)].count = u32(1)
  set_level(span(&leaves), u32(0), u32(3))
  f: u32 = fill(span(&doms), u32(0), u32(1))   // 7 + 8 = 15
  t: u32 = total(span(&nodes), u32(1))          // (6 + 1) + 4 = 11; peek then sees 7 + 4 = 11
  // 11 + 11 + (40 + 3) + 5 + 9 + 15 + 11 = 105
  i32_bits_u32(peek(view(&nodes), u32(1)) + u32_trunc_u64(heavy(span(&nodes), u32(2)) + walk(span(&leaves), u32(0), u32(9)) + fixed(view(&leaves), u32(0))) + pend(span(&doms), u32(1), u32(2)) + f + t)
}
`

func TestE2ENativeRecordSpanReadersProven(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("record_span_proof.oak", nativeRecordSpanProofProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_record_span_proof", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 105 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 105\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"peek", "heavy", "walk", "fixed", "pend"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s reads a span of records and must be proven; diagnostics:\n%s", fn, joined)
		}
	}
	// Writers are proven in the leaf memories they write: the span's
	// final memory at a fresh index agrees on both sides.
	if !strings.Contains(joined, "asm unit set_level: proven equal to its Oak body in the span memory it writes (leaves.entries, leaves.level)") {
		t.Errorf("set_level must be proven in the memories it writes; diagnostics:\n%s", joined)
	}
	// A caller whose callees take the span of records is proven through
	// the summaries: the writer callee's store and the reader callee's
	// result both in the caller's terms.
	if !strings.Contains(joined, "asm unit total: proven") || !strings.Contains(joined, "span memory it writes (pool.value)") {
		t.Errorf("total (calls a writer and a reader over the span of records) must be proven; diagnostics:\n%s", joined)
	}
	if !strings.Contains(joined, "asm unit fill: proven") || !strings.Contains(joined, "span memory it writes (doms.count, doms.pending)") {
		t.Errorf("fill (a counted loop of stores, then a read back) must be proven in result and memories; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_span_proof_c", New().WithSource("record_span_proof.oak", nativeRecordSpanProofProgram)); abnormal || code != 105 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 105", code, abnormal)
	}
}
