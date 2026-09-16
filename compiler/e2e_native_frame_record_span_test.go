package compiler

// An owned frame array of records passed as a span or view — `span(&t)`
// over `t: [2]Table` — binds the callee's parameter to the elements read
// leaf by leaf from the frame at their offsets, and a writable span's
// final leaves are stored back the same way (docs/spec/94-assembler.md §8,
// span arguments over owned arrays); the caller is proven through its
// callees at their Oak bodies. Before, such a caller was trusted:
// "elements without a scalar model at the span's width".

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

const nativeFrameRecordSpanProgram = `Table: type = struct {
  pages: [4]u64
  free_count: u16
  entry_count: [2]u16
}

clear_pages: (s: [*]Table, dom: u32): u32 {
  j: u32 = u32(0)
  dom < len(s) ? {
    while j < u32(4) {
      s[dom].pages[j] = u64(0)
      j = j + u32(1)
    }
    j
  } | { u32(0) }
}

take: (s: [*]Table, dom: u32): u16 {
  dom < len(s) ? {
    s[dom].free_count = s[dom].free_count - u16(1)
    s[dom].entry_count[u32(1)] = u16(7)
    s[dom].free_count
  } | { u16(0) }
}

total: (s: []Table): u32 {
  acc: u32 = u32(0)
  i: u32 = u32(0)
  while i < len(s) {
    acc = acc + u32(s[i].free_count) + u32(s[i].entry_count[u32(0)]) + u32(s[i].entry_count[u32(1)]) + u32_trunc_u64(s[i].pages[u32(3)])
    i = i + u32(1)
  }
  acc
}

main: (): i32 {
  t: [2]Table = [Table { pages: [1, 2, 3, 4], free_count: 3, entry_count: [9, 9] }, Table { pages: [5, 6, 7, 8], free_count: 5, entry_count: [1, 1] }]
  n: u32 = clear_pages(span(&t), u32(0))
  f: u16 = take(span(&t), u32(1))
  s: u32 = total(view(&t))
  (n == u32(4) && f == u16(4) && s == u32(3 + 9 + 9 + 0 + 4 + 1 + 7 + 8) && t[0].pages[3] == u64(0) && t[1].entry_count[1] == u16(7)) ? 42 | 1
}
`

func TestE2ENativeFrameRecordSpanArguments(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("frame_record_span.oak", nativeFrameRecordSpanProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "frame_record_span", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 42 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 42\n%s", code, abnormal, joined)
	}
	for _, fn := range []string{"clear_pages", "take", "total"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven") {
			t.Errorf("%s was not proven; diagnostics:\n%s", fn, joined)
		}
	}
	// main's result reads the array after the callees wrote through their
	// spans: the write-back is what makes the checks decide.
	if !strings.Contains(joined, "asm unit main: proven equal to its Oak body at the bit level") || !strings.Contains(joined, "(callees taken at their Oak bodies: clear_pages, take, total)") {
		t.Errorf("main must be proven through its callees over the frame array; diagnostics:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "frame_record_span_c", New().WithSource("frame_record_span.oak", nativeFrameRecordSpanProgram)); abnormal || code != 42 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
