package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

const bufferPackageProgram = `package main

import("buffer")

is_full: (reason: buffer.Error): Bool = reason ?
  | .Full => true
  | .InsufficientData => false

main: (): i32 {
  state: [1]buffer.Cursor
  queue: [*]buffer.Cursor = span(&state)
  data: [6]u8
  input: [3]u8
  input[0] = u8(10)
  input[1] = u8(20)
  input[2] = u8(30)

  true ? {
    storage: [*]u8 = span(&data)
    source: []u8 = view(&input)
    added: Result[u32, buffer.Error] = buffer.append(queue, storage, source)
    added_count: u32 = added ? | .Ok(n) => n | .Err(e) => u32(99)
    assert(added_count == u32(3))
    assert(buffer.live_len(queue, u32(6)) == u32(3))
    assert(buffer.tail_space(queue, u32(6)) == u32(3))

    too_large: [4]u8
    too_large[0] = u8(91)
    rejected: Result[u32, buffer.Error] = buffer.append(queue, storage, view(&too_large))
    rejected_full: Bool = rejected ? | .Ok(n) => false | .Err(reason) => is_full(reason)
    assert(rejected_full)
    assert(queue[0].start == u32(0) && queue[0].end == u32(3))
    assert(storage[0] == u8(10) && storage[1] == u8(20) && storage[2] == u8(30) && storage[3] == u8(0))
  }

  too_wide: [4]u8
  too_wide[0] = u8(77)
  too_wide[1] = u8(77)
  too_wide[2] = u8(77)
  too_wide[3] = u8(77)
  true ? {
    rejected_peek: Result[u32, buffer.Error] = buffer.peek_into(queue, view(&data), span(&too_wide))
    insufficient: Bool = rejected_peek ? | .Ok(n) => false | .Err(reason) => !is_full(reason)
    assert(insufficient)
  }
  assert(too_wide[0] == u8(77) && too_wide[1] == u8(77) && too_wide[2] == u8(77) && too_wide[3] == u8(77))

  peeked: [3]u8
  true ? {
    exact_peek: Result[u32, buffer.Error] = buffer.peek_into(queue, view(&data), span(&peeked))
    peek_count: u32 = exact_peek ? | .Ok(n) => n | .Err(e) => u32(99)
    assert(peek_count == u32(3))
  }
  assert(peeked[0] == u8(10) && peeked[1] == u8(20) && peeked[2] == u8(30))

  rejected_consume: Result[u32, buffer.Error] = buffer.consume(queue, u32(6), u32(4294967295))
  consume_short: Bool = rejected_consume ? | .Ok(n) => false | .Err(reason) => !is_full(reason)
  assert(consume_short && queue[0].start == u32(0) && queue[0].end == u32(3))

  consumed: Result[u32, buffer.Error] = buffer.consume(queue, u32(6), u32(1))
  consumed_count: u32 = consumed ? | .Ok(n) => n | .Err(e) => u32(99)
  assert(consumed_count == u32(1) && queue[0].start == u32(1) && queue[0].end == u32(3))
  moved: u32 = buffer.compact(queue, span(&data))
  assert(moved == u32(2) && queue[0].start == u32(0) && queue[0].end == u32(2))
  assert(data[0] == u8(20) && data[1] == u8(30))

  read: [2]u8
  true ? {
    read_result: Result[u32, buffer.Error] = buffer.read_into(queue, view(&data), span(&read))
    read_count: u32 = read_result ? | .Ok(n) => n | .Err(e) => u32(99)
    assert(read_count == u32(2))
  }
  assert(read[0] == u8(20) && read[1] == u8(30))
  assert(queue[0].start == u32(0) && queue[0].end == u32(0))

  queue[0].end = u32(1)
  buffer.reset(queue)
  assert(queue[0].start == u32(0) && queue[0].end == u32(0))

  built_data: [3]u8
  builder_source: [2]u8
  builder_source[0] = u8(8)
  builder_source[1] = u8(9)
  built0: buffer.Builder = buffer.builder()
  built1: buffer.Builder = buffer.append_byte(built0, span(&built_data), u8(7))
  built2: buffer.Builder = buffer.append_bytes(built1, span(&built_data), view(&builder_source))
  done: Result[u32, buffer.Error] = buffer.finish(built2)
  done_count: u32 = done ? | .Ok(n) => n | .Err(e) => u32(99)
  assert(done_count == u32(3) && !built2.failed && built2.length == u32(3))
  assert(built_data[0] == u8(7) && built_data[1] == u8(8) && built_data[2] == u8(9))

  failed: buffer.Builder = buffer.append_byte(built2, span(&built_data), u8(10))
  sticky: buffer.Builder = buffer.append_bytes(failed, span(&built_data), view(&builder_source))
  failed_result: Result[u32, buffer.Error] = buffer.finish(sticky)
  failed_full: Bool = failed_result ? | .Ok(n) => false | .Err(reason) => is_full(reason)
  assert(failed_full && sticky.failed && sticky.length == u32(3))
  assert(built_data[0] == u8(7) && built_data[1] == u8(8) && built_data[2] == u8(9))

  fluent_data: [2]u8
  fluent: buffer.Builder = buffer.builder().
    append_byte(span(&fluent_data), u8(4)).
    append_byte(span(&fluent_data), u8(2))
  fluent_result: Result[u32, buffer.Error] = fluent.finish()
  fluent_count: u32 = fluent_result ? | .Ok(n) => n | .Err(e) => u32(99)
  assert(fluent_count == u32(2) && fluent_data[0] == u8(4) && fluent_data[1] == u8(2))
  42
}
`

func TestE2EStdlibBufferPackage(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/buffer-test\noak 0.1.0\n",
		"main.oak": bufferPackageProgram,
	})
	comp := New().WithPackageDir(root)
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{
		"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED",
		"oak_strings__", "oak_json__", "oak_encoding__", "oak_endian__",
	} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("qualified buffer package emitted forbidden %q", forbidden)
		}
	}

	model, err := comp.Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if result := evaluator.Eval(model.Tree.Root, env); result != nil {
		if evalErr, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error evaluating buffer package: %s", evalErr.Message)
		}
	}
	call := parser.New(layout.New(scanner.New("main()"))).ParseProgram()
	result := evaluator.Eval(call, env)
	if evalErr, isErr := result.(*object.Error); isErr {
		t.Fatalf("interpreter error in main: %s", evalErr.Message)
	}
	integer, ok := result.(*object.Integer)
	if !ok || integer.Value != 42 {
		t.Fatalf("interpreter returned %s", result.Inspect())
	}

	code, abnormal := buildPackageAndRun(t, comp)
	if abnormal || code != 42 {
		t.Fatalf("compiled buffer package exited (%d, abnormal=%v)", code, abnormal)
	}
}

func TestE2EStdlibBufferPackageRejectsInvalidCursor(t *testing.T) {
	for _, mutation := range []string{
		"queue[0].start = u32(2)\nqueue[0].end = u32(1)",
		"queue[0].end = u32(3)",
	} {
		root := writeModule(t, map[string]string{
			"oak.mod": "module example.com/buffer-invalid\noak 0.1.0\n",
			"main.oak": `package main
import("buffer")
main: (): i32 {
  state: [1]buffer.Cursor
  queue: [*]buffer.Cursor = span(&state)
` + mutation + `
  _ = buffer.live_len(queue, u32(2))
  0
}
`,
		})
		_, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
		if !abnormal {
			t.Fatal("invalid qualified buffer cursor must trap")
		}
	}
}

func TestE2EStdlibBufferPackageAgreesWithFlatPrelude(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/buffer-flat\noak 0.1.0\n",
		"main.oak": `package main

import(std)
import("buffer")

Cursor: type = | LocalCursor
Error: type = | LocalError
Builder: type = | LocalBuilder
live_len: (): u32 = u32(1)
tail_space: (): u32 = u32(2)
append: (): u32 = u32(3)
peek_into: (): u32 = u32(4)
consume: (): u32 = u32(5)
read_into: (): u32 = u32(6)
compact: (): u32 = u32(7)
reset: (): u32 = u32(8)
builder: (): u32 = u32(9)
finish: (): u32 = u32(10)

main: (): i32 {
  source: [2]u8
  source[0] = u8(4)
  source[1] = u8(2)
  package_state: [1]buffer.Cursor
  flat_state: [1]ByteBufferCursor
  package_data: [2]u8
  flat_data: [2]u8
  package_result: Result[u32, buffer.Error] = buffer.append(span(&package_state), span(&package_data), view(&source))
  flat_result: Result[u32, BufferError] = buffer_append(span(&flat_state), span(&flat_data), view(&source))
  package_count: u32 = package_result ? | .Ok(n) => n | .Err(e) => u32(99)
  flat_count: u32 = flat_result ? | .Ok(n) => n | .Err(e) => u32(99)
  locals: u32 = live_len() + tail_space() + append() + peek_into() + consume() + read_into() + compact() + reset() + builder() + finish()
  same: Bool = package_count == flat_count && package_count == u32(2) && package_data[0] == flat_data[0] && package_data[1] == flat_data[1] && package_state[0].end == flat_state[0].end
  same && locals == u32(55) ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("flat and qualified buffer exited (%d, abnormal=%v)", code, abnormal)
	}
}
