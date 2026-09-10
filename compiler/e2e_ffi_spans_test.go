package compiler

// Spans at the C boundary, executed (docs/spec/92-ffi.md section 2.5): a
// read-only view crosses as a pointer and a length in one call, a writable
// span is filled by libc, and c.String hands libc a NUL-terminated literal.

import (
	"strings"
	"testing"
)

func TestE2EBoundarySpanReadsAndWrites(t *testing.T) {
	stdout, code, abnormal := buildAndRunOutput(t, "ffispans", `
write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern("write")
puts: (s: c.String): c.Int = c.extern("puts")
getcwd: (into: c.Ptr, size: c.Size): c.Ptr = c.extern("getcwd")

emit: (bytes: []u8): () {
  _ = write(c.Int(1), c.span_of(bytes))
}

cwd_first: (): u8 {
  path: [4096]u8
  filled: [*]u8 = span(&path)
  _ = getcwd(c.span_mut_of(filled))
  filled[0]
}

main: (): i32 {
  text: []u8 = str_bytes("OK\n")
  emit(text)
  head: [1]u8 = [1]u8{cwd_first()}
  first: []u8 = view(&head)
  emit(first)
  _ = puts(c.String(""))
  0
}
`)
	if abnormal || code != 0 {
		t.Fatalf("exit = (%d, abnormal=%v), want 0", code, abnormal)
	}
	// getcwd wrote the current directory into Oak-owned storage; every
	// absolute path starts with '/'. puts adds the final newline.
	if stdout != "OK\n/\n" {
		t.Fatalf("stdout = %q, want %q", stdout, "OK\n/\n")
	}
}

// The emitted C carries the pointer and element count of the view, nothing
// else: no copy, no thunk.
func TestBoundarySpanLowering(t *testing.T) {
	output, err := New().WithSource("spans.oak", `
write: (fd: c.Int, data: c.Ptr, count: c.Size): c.Long = c.extern("write")

emit: (bytes: []u8): () {
  _ = write(c.Int(1), c.span_of(bytes))
}

main: (): i32 { 0 }
`).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	if !strings.Contains(output, "write( ((int)( 1 )), (void *)( bytes ).base, (size_t)( bytes ).len )") {
		t.Fatalf("boundary span must lower to the base pointer and element count:\n%s", output)
	}
}

// Outside an extern call the form is rejected, not lowered.
func TestBoundarySpanRejectedOutsideExternCall(t *testing.T) {
	_, err := New().WithSource("escape.oak", `
take: (p: c.Ptr, n: c.Size): () { }
emit: (bytes: []u8): () { take(c.span_of(bytes)) }
main: (): i32 { 0 }
`).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-F0103") {
		t.Fatalf("boundary span passed to Oak code must be rejected with OAK-F0103, got %v", err)
	}
}
