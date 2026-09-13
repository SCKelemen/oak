package compiler

import (
	"strings"
	"testing"
)

// Borrowed decoded views (docs/spec/71-codecs.md section 5, item 3, on top
// of docs/spec/50-borrowing.md section 8c): a record whose string fields are
// `View[u8, R]` decodes as views of the input — each field is the JSON
// string token, quotes included, validated but not copied — and the decoded
// record borrows the input's owner for as long as it lives. Unescaping is
// the caller's, on demand, with json_string_decode.
const jsonViewPrelude = `import(std)
Frame[R]: type = struct {
 kind: u32
 payload: View[u8, R]
 name: View[u8, R]
}
`

func TestE2EJsonDecodeViews(t *testing.T) {
	var source strings.Builder
	source.WriteString(jsonViewPrelude + "main: (): i32 {\n")
	writeTextView(&source, "input", `{"kind":7,"payload":"hello \"x\"","name":"n"}`)
	writeTextView(&source, "want_payload", `"hello \"x\""`)
	writeTextView(&source, "want_text", `hello "x"`)
	source.WriteString(`
 r: Result[Frame, JsonDecodeError] = decode[Frame, Json](input)
 r ?
 | .Err(e) => 1
 | .Ok(f) => {
  assert(f.kind == u32(7))
  assert(len(f.payload) == len(want_payload))
  i: u32 = 0
  while i < len(want_payload) { assert(f.payload[i] == want_payload[i])
   i = i + u32(1)
  }
  assert(len(f.name) == u32(3) && f.name[1] == u8(110))
  text: [16]u8
  dst: [*]u8 = span(&text)
  n: u32 = json_result_value(json_string_decode(dst, f.payload))
  assert(n == len(want_text))
  j: u32 = 0
  while j < n { assert(dst[j] == want_text[j])
   j = j + u32(1)
  }
  42
 }
}
`)
	code, abnormal := buildAndRun(t, "json_views", source.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if interpreted := interpretChecked(t, source.String()); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// A non-string value where a view field is expected is a type mismatch; a
// document with trailing content stays a syntax error; invalid UTF-8 inside
// a viewed string is still reported, since the view is handed back raw.
func TestE2EJsonDecodeViewErrors(t *testing.T) {
	var source strings.Builder
	source.WriteString(jsonViewPrelude + `
code_of[R]: (r: Result[Frame[R], JsonDecodeError]): u32 = r ? | .Ok(f) => u32(0) | .Err(e) => json_decode_error_code(e)
main: (): i32 {
`)
	writeTextView(&source, "mismatch", `{"kind":7,"payload":5,"name":"n"}`)
	writeTextView(&source, "trailing", `{"kind":7,"payload":"a","name":"n"} x`)
	writeTextView(&source, "encoding", "{\"kind\":7,\"payload\":\"\xff\",\"name\":\"n\"}")
	source.WriteString(`
 assert(code_of(decode[Frame, Json](mismatch)) == u32(3))
 assert(code_of(decode[Frame, Json](trailing)) == u32(2))
 assert(code_of(decode[Frame, Json](encoding)) == u32(1))
 42
}
`)
	code, abnormal := buildAndRun(t, "json_view_errors", source.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	if interpreted := interpretChecked(t, source.String()); interpreted != 42 {
		t.Fatalf("interpreter returned %d", interpreted)
	}
}

// The decoded record is a borrow of the input: writing the input while it
// lives is rejected, and encoding a borrowed record is not derived.
func TestJsonDecodeViewRejections(t *testing.T) {
	cases := []struct{ name, src, want string }{
		{"owner written while decoded record lives", jsonViewPrelude + `
main: (): i32 {
 data: [8]u8
 r: Result[Frame, JsonDecodeError] = decode[Frame, Json](view(&data))
 data[0] = u8(1)
 r ? | .Ok(f) => i32_bits_u32(f.kind) | .Err(e) => 1
}`, "OAK-B0103"},
		{"encoding a borrowed record", jsonViewPrelude + `
main: (): i32 {
 data: [8]u8
 dst: [*]u8 = span(&data)
 f: Frame = Frame { kind: u32(1), payload: subslice(dst, u32(0), u32(0)), name: subslice(dst, u32(0), u32(0)) }
 json_result_value(encode[Frame, Json](f, dst)) == u32(0) ? 42 | 1
}`, "encoding borrowed records is not derived"},
	}
	for _, c := range cases {
		_, err := New().WithSource("reject.oak", c.src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), c.want) {
			t.Fatalf("%s: err = %v, want %q", c.name, err, c.want)
		}
	}
}

// A borrowed record that also owns arrays — the event workload's shape —
// decodes and is returned from the region-indexed reader: the record is
// owned data whose view fields borrow the input, not a borrow of a local
// owner (a regression of the record-owner rule of 50-borrowing.md §2).
func TestE2EJsonDecodeViewsWithOwnedArrays(t *testing.T) {
	var source strings.Builder
	source.WriteString(`import(std)
Event[R]: type = struct { id: u64, kind: View[u8, R], message: View[u8, R], latencies: [4]u32, deltas: [2]i32 }
main: (): i32 {
`)
	writeTextView(&source, "input", `{"id":7,"kind":"k","message":"hello","latencies":[1,2,3,4],"deltas":[-1,2]}`)
	source.WriteString(`
 r: Result[Event, JsonDecodeError] = decode[Event, Json](input)
 r ?
  | .Err(_) => { assert(false) }
  | .Ok(value) => {
   assert(value.id == u64(7))
   assert(len(value.kind) == u32(3) && value.kind[1] == u8(107))
   assert(len(value.message) == u32(7))
   assert(value.latencies[3] == u32(4) && value.deltas[0] == i32(0) - i32(1))
  }
 42
}
`)
	code, abnormal := buildAndRun(t, "json_view_owned_arrays", source.String())
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
