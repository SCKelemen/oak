package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// A record element assigned from a call (`out[0] = make_pair(5)`, the dbs
// pilot's `out[0] = time.time_source_native()`): the call is lowered
// before the element address is formed, so the address never crosses the
// call through a spill slot — a reload the checker cannot read as an
// element region refused the store ("x10 is neither" the frame nor a
// span base). Both backends agree on the stored fields.
const nativeRecordElementCallProgram = `
Pair: type = struct { lo: u64, hi: u64, mid: u64, tag: u32, flag: Bool }

make_pair: (a: u64): Pair = Pair { lo: a, hi: a + u64(1), mid: u64(3), tag: u32(7), flag: true }

fill: (out: [*]Pair, at: u32): () {
  at < len(out) ? { out[at] = make_pair(u64(5)) } | { }
}

main: (): i32 {
  buf: [2]Pair = [2]Pair{ Pair { lo: u64(0), hi: u64(0), mid: u64(0), tag: u32(0), flag: false }, Pair { lo: u64(0), hi: u64(0), mid: u64(0), tag: u32(0), flag: false } }
  fill(span(&buf), u32(1))
  fill(span(&buf), u32(9))
  // 7 + 6 + 3 + 1 = 17 from the second element; the first stays zero.
  i32_bits_u32(buf[1].tag + u32_trunc_u64(buf[1].hi) + u32_trunc_u64(buf[1].mid) + (buf[1].flag ? u32(1) | u32(0)) + buf[0].tag)
}
`

func TestE2ENativeRecordElementFromCall(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("relem.oak", nativeRecordElementCallProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	if _, err := comp.Check().Get(); err != nil {
		t.Fatal(err)
	}
	joined := strings.Join(infos, "\n")
	if strings.Contains(joined, "the checker refuses the lowering of fill") {
		t.Errorf("fill must lower natively with the call before the element address; diagnostics:\n%s", joined)
	}
	_, code, abnormal := buildAndRunFrom(t, "native_record_element_call", comp)
	if abnormal || code != 17 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 17\n%s", code, abnormal, joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_record_element_call_c", New().WithSource("relem.oak", nativeRecordElementCallProgram)); abnormal || code != 17 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 17", code, abnormal)
	}
}
