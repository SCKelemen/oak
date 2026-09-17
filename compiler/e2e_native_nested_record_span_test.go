package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/diagnostic"
)

// An array field whose elements are records, through a span of records
// (docs/spec/94-assembler.md §9 "Nested record spans"): `s[d].surfaces[i].x`.
// The leaves of such a field are one memory per leaf of the element type —
// `s.surfaces.x`, `s.surfaces.y` — each holding that field across every
// element of every record, at the linear index `d·N + i`. A scalar array
// field (`s[d].xs[i]`) and a scalar field (`s[d].count`) were already
// proven; this shape was trusted, and both the read and the store were
// refused.
const nativeNestedRecordSpanProgram = `
Surface: type = struct { x: u32, y: u32, w: u16, tag: u8 }
Dom: type = struct { surfaces: [4]Surface, count: u32 }

// An element bound to a local by value: the eight bytes the machine
// loads cover two four-byte leaves and match none of them, and the span
// is no aggregate local, so neither side had it. The value is the
// element's fields read from their own memories. The element must have
// no padding, since a byte no leaf covers is not a field and the two
// sides would not agree on it.
Box: type = struct { x: u32, y: u32 }
Room: type = struct { boxes: [4]Box, n: u32 }

by_value: (r: [*]Room, d: u32, i: u32): u32 {
  d < len(r) && i < u32(4) ? { b: Box = r[d].boxes[i]; b.x + b.y } | { u32(0) }
}

// The writer's counterpart: a whole element assigned, one write per leaf.
// The element of the span itself, and an element of its array field.
put_box: (r: [*]Room, d: u32, i: u32, x: u32, y: u32): () {
  d < len(r) && i < u32(4) ? { r[d].boxes[i] = Box { x: x, y: y } } | { }
}

put_room_n: (r: [*]Room, d: u32, v: u32): () {
  d < len(r) ? { r[d].n = v } | { }
}

get_x: (s: [*]Dom, d: u32, i: u32): u32 {
  d < len(s) && i < u32(4) ? { s[d].surfaces[i].x } | { u32(0) }
}

get_y: (s: [*]Dom, d: u32, i: u32): u32 {
  d < len(s) && i < u32(4) ? { s[d].surfaces[i].y } | { u32(0) }
}

get_w: (s: [*]Dom, d: u32, i: u32): u32 {
  d < len(s) && i < u32(4) ? { u32(s[d].surfaces[i].w) } | { u32(0) }
}

set_x: (s: [*]Dom, d: u32, i: u32, v: u32): () {
  d < len(s) && i < u32(4) ? { s[d].surfaces[i].x = v } | { }
}

// A write to one field then a read of another: distinct memories, so the
// read is the entry value and not the value just written.
set_x_get_y: (s: [*]Dom, d: u32, i: u32, v: u32): u32 {
  d < len(s) && i < u32(4) ? { s[d].surfaces[i].x = v; s[d].surfaces[i].y } | { u32(0) }
}

// A constant element index, and the record's own scalar field beside the
// array.
// Two elements of the same array field compared: neither operand is a
// parameter, so the comparison had no width and the body was trusted.
// It is the shape an overlap test takes.
overlaps: (s: [*]Dom, d: u32, i: u32, j: u32): u32 {
  d < len(s) && i < u32(4) && j < u32(4) ? {
    s[d].surfaces[i].x < s[d].surfaces[j].y ? u32(1) | u32(0)
  } | { u32(0) }
}

get_const: (s: [*]Dom, d: u32): u32 {
  d < len(s) ? { s[d].surfaces[2].x + s[d].count } | { u32(0) }
}

// A loop over the elements, storing through the nested field.
scale_x: (s: [*]Dom, d: u32, k: u32): () {
  d < len(s) ? {
    i: u32 = u32(0)
    while i < u32(4) {
      s[d].surfaces[i].x = s[d].surfaces[i].x * k
      i = i + u32(1)
    }
  } | { }
}

main: (): i32 {
  doms: [2]Dom
  d: u32 = 0
  while d < u32(2) {
    i: u32 = 0
    while i < u32(4) {
      doms[d].surfaces[i].x = d * u32(10) + i
      doms[d].surfaces[i].y = i + u32(100)
      doms[d].surfaces[i].w = u16_trunc_u32(i + u32(7))
      i = i + u32(1)
    }
    doms[d].count = d + u32(3)
    d = d + u32(1)
  }
  s: [*]Dom = span(&doms)
  // get_x(1,2) = 12, get_y(0,3) = 103, get_w(1,1) = 8.
  a: u32 = get_x(s, u32(1), u32(2)) + get_y(s, u32(0), u32(3)) + get_w(s, u32(1), u32(1))
  // set_x then read y: y is untouched, 101.
  b: u32 = set_x_get_y(s, u32(0), u32(1), u32(999))
  // x[0][1] is now 999; scale dom 0 by 2 makes it 1998, and x[0][0] = 0.
  scale_x(s, u32(0), u32(2))
  c: u32 = get_x(s, u32(0), u32(1))
  // get_const(1) = x[1][2] + count[1] = 12 + 4 = 16.
  e: u32 = get_const(s, u32(1))
  // x[0][2] = 2 and y[0][3] = 103, so 2 < 103 is 1.
  f: u32 = overlaps(s, u32(0), u32(2), u32(3))
  // x[0][1] is 1998 after the scale and y[0][1] is 101, so 2099; count[1] = 4.
  rooms: [1]Room
  rooms[u32(0)].boxes[u32(2)].x = u32(70)
  rooms[u32(0)].boxes[u32(2)].y = u32(5)
  // Assign a whole element, then read it back by value: 30 + 9 = 39.
  put_box(span(&rooms), u32(0), u32(3), u32(30), u32(9))
  g: u32 = by_value(span(&rooms), u32(0), u32(2)) + by_value(span(&rooms), u32(0), u32(3))
  // 12 + 103 + 8 = 123; + 101 = 224; + 1998 = 2222; + 16 = 2238; + 1 = 2239;
  // + 75 + 39 = 2353. 2353 & 255 = 49.
  i32_bits_u32((a + b + c + e + f + g) & u32(255))
}
`

func TestE2ENativeNestedRecordSpan(t *testing.T) {
	requireArm64Host(t)
	var infos []string
	comp := New().WithSource("nested_span.oak", nativeNestedRecordSpanProgram).WithNativeBodies().WithNativeAsm().WithDiagnosticSink(func(d *diagnostic.Diagnostic) {
		if d.Source == "native" {
			infos = append(infos, d.Message)
		}
	})
	_, code, abnormal := buildAndRunFrom(t, "native_nested_record_span", comp)
	joined := strings.Join(infos, "\n")
	if abnormal || code != 49 {
		t.Fatalf("native: exit = (%d, abnormal=%v), want 49\n%s", code, abnormal, joined)
	}
	// Every reader is proven at the bit level, and every writer in the leaf
	// memory it writes — named by the field path, not by the array.
	for _, fn := range []string{"get_x", "get_y", "get_w", "get_const", "set_x_get_y", "overlaps", "by_value"} {
		if !strings.Contains(joined, "asm unit "+fn+": proven equal to its Oak body") {
			t.Errorf("%s reads a nested record-span field and must be proven; diagnostics:\n%s", fn, joined)
		}
	}
	for _, want := range []string{
		"asm unit set_x: proven equal to its Oak body in the span memory it writes (s.surfaces.x)",
		"asm unit put_box: proven equal to its Oak body in the span memory it writes (r.boxes.x, r.boxes.y)",
		"asm unit scale_x: proven equal to its Oak body",
	} {
		if !strings.Contains(joined, want) {
			t.Errorf("diagnostics lack %q:\n%s", want, joined)
		}
	}
	if strings.Contains(joined, "disagrees") {
		t.Errorf("a false mismatch over a nested record span:\n%s", joined)
	}
	if _, code, abnormal := buildAndRunFrom(t, "native_nested_record_span_c", New().WithSource("nested_span.oak", nativeNestedRecordSpanProgram)); abnormal || code != 49 {
		t.Fatalf("C backend: exit = (%d, abnormal=%v), want 49", code, abnormal)
	}
}
