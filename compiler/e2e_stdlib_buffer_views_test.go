package compiler

import (
	"strings"
	"testing"
)

const bufferViewsProgram = `package main
import("buffer")

main: (): i32 {
  state: [1]buffer.Cursor
  cursor: [*]buffer.Cursor = span(&state)
  data: [5]u8 = [5]u8{ 11, 22, 33, 44, 55 }
  cursor[0].start = 1
  cursor[0].end = 4
  true ? {
    live: []u8 = buffer.peek(cursor, view(&data))
    assert(len(live) == 3 && live[0] == 22 && live[2] == 44)
    // The view is a snapshot of the interval, not a borrow of cursor state.
    _ = buffer.consume(cursor, 5, 1)
    assert(len(live) == 3 && live[0] == 22)
  }
  true ? {
    live: []u8 = buffer.peek(cursor, view(&data))
    assert(len(live) == 2 && live[0] == 33 && live[1] == 44)
  }
  // Ending the observation permits writes and compaction.
  data[2] = 42
  true ? {
    live: []u8 = buffer.peek(cursor, view(&data))
    assert(live[0] == 42)
  }
  assert(buffer.compact(cursor, span(&data)) == 2)
  true ? {
    live: []u8 = buffer.peek(cursor, view(&data))
    assert(len(live) == 2 && live[0] == 42 && live[1] == 44)
  }
  cursor[0].start = 5
  cursor[0].end = 5
  true ? {
    empty: []u8 = buffer.peek(cursor, view(&data))
    assert(len(empty) == 0)
  }
  buffer.reset(cursor)
  true ? {
    empty: []u8 = buffer.peek(cursor, view(&data))
    assert(len(empty) == 0)
  }
  42
}
`

func bufferViewsModule(t *testing.T, source string) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"oak.mod":  "module example.com/buffer-views\noak 0.1.0\n",
		"main.oak": source,
	})
}

func TestE2EStdlibBufferViews(t *testing.T) {
	root := bufferViewsModule(t, bufferViewsProgram)
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreter = %d", got)
	}
	comp := New().WithPackageDir(root)
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "memcpy(", "memmove(", "OAK_UNSUPPORTED"} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("buffer views emitted %q", forbidden)
		}
	}
	code, abnormal := buildPackageAndRun(t, comp)
	if abnormal || code != 42 {
		t.Fatalf("compiled = (%d, %v)", code, abnormal)
	}
}

func TestStdlibBufferViewsRejectWrites(t *testing.T) {
	for _, tc := range []struct{ name, setup, write, code string }{
		{"owner", "live: []u8 = buffer.peek(cursor, view(&data))", "data[0] = 9", "OAK-B0103"},
		{"compact", "live: []u8 = buffer.peek(cursor, view(&data))", "_ = buffer.compact(cursor, span(&data))", "OAK-B0105"},
		{"append", "live: []u8 = buffer.peek(cursor, view(&data))", "_ = buffer.append(cursor, span(&data), view(&input))", "OAK-B0105"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			src := `package main
import("buffer")
main: (): i32 {
 state: [1]buffer.Cursor
 cursor: [*]buffer.Cursor = span(&state)
 data: [2]u8
 input: [1]u8
 cursor[0].end = 2
 ` + tc.setup + "\n" + tc.write + "\ni32(live[0])\n}"
			_, err := New().WithPackageDir(bufferViewsModule(t, src)).Check().Get()
			if err == nil || !strings.Contains(err.Error(), tc.code) {
				t.Fatalf("got %v, want %s", err, tc.code)
			}
		})
	}
}

func TestE2EStdlibBufferViewsRejectInvalidCursor(t *testing.T) {
	for _, state := range []string{"cursor[0].start = 2\ncursor[0].end = 1", "cursor[0].end = 3", "cursor[0].start = 4294967295\ncursor[0].end = 4294967295"} {
		t.Run(state, func(t *testing.T) {
			src := `package main
import("buffer")
main: (): i32 {
 state: [1]buffer.Cursor
 cursor: [*]buffer.Cursor = span(&state)
 data: [2]u8
 ` + state + "\nlive: []u8 = buffer.peek(cursor, view(&data))\ni32_bits_u32(len(live))\n}"
			_, abnormal := buildPackageAndRun(t, New().WithPackageDir(bufferViewsModule(t, src)))
			if !abnormal {
				t.Fatal("invalid cursor must trap")
			}
		})
	}
}

func TestStdlibBufferViewCannotEscapeLocalStorage(t *testing.T) {
	src := `package main
import("buffer")
bad[R]: (input: View[u8, R]): View[u8, R] {
 state: [1]buffer.Cursor
 data: [2]u8
 buffer.peek(span(&state), view(&data))
}
main: (): i32 { 0 }
`
	_, err := New().WithPackageDir(bufferViewsModule(t, src)).Check().Get()
	if err == nil || !strings.Contains(err.Error(), "OAK-B0113") {
		t.Fatalf("got %v, want OAK-B0113", err)
	}
}

func TestE2EStdlibBufferPeekCompatibility(t *testing.T) {
	src := `package main
import(std)
import("buffer")
peek: (): u32 = 7
main: (): i32 {
 _ = buffer.finish(buffer.builder())
 state: [1]ByteBufferCursor
 cursor: [*]ByteBufferCursor = span(&state)
 data: [1]u8 = [1]u8{42}
 cursor[0].end = 1
 true ? {
  live: []u8 = buffer_peek(cursor, view(&data))
  assert(len(live) == 1 && live[0] == 42 && peek() == 7)
 }
 buffer_reset(cursor)
 true ? {
  // A zero-capacity borrowed view is valid with the zero cursor.
  empty: []u8 = buffer_peek(cursor, view(&data)[0:0])
  assert(len(empty) == 0)
 }
 42
}
`
	root := bufferViewsModule(t, src)
	if got := interpretModule(t, root); got != 42 {
		t.Fatalf("interpreter = %d", got)
	}
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("compiled = (%d, %v)", code, abnormal)
	}
}
