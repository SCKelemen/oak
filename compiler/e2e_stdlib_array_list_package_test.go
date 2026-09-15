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

const arrayListPackageProgram = `package main

import("array_list")

error_code: (reason: array_list.Error): u32 = reason ?
  | .Full => u32(1)
  | .Empty => u32(2)
  | .OutOfBounds => u32(3)
ok_u32: (result: Result[u32, array_list.Error], expected: u32): Bool = result ?
  | .Ok(value) => value == expected
  | .Err(reason) => false
err_u32: (result: Result[u32, array_list.Error], expected: u32): Bool = result ?
  | .Ok(value) => false
  | .Err(reason) => error_code(reason) == expected
err_u8: (result: Result[u8, array_list.Error], expected: u32): Bool = result ?
  | .Ok(value) => false
  | .Err(reason) => error_code(reason) == expected

main: (): i32 {
  state: [1]array_list.Cursor
  data: [5]u32
  list: [*]array_list.Cursor = span(&state)

  true ? {
    storage: [*]u32 = span(&data)
    first: Result[u32, array_list.Error] = array_list.push(list, storage, u32(10))
    second: Result[u32, array_list.Error] = array_list.push(list, storage, u32(30))
    inserted: Result[u32, array_list.Error] = array_list.insert(list, storage, u32(1), u32(20))
    assert(ok_u32(first, u32(0)))
    assert(ok_u32(second, u32(1)))
    assert(ok_u32(inserted, u32(1)))
  }
  assert(list[0].length == u32(3))
  assert(data[0] == u32(10) && data[1] == u32(20) && data[2] == u32(30))

  read: Result[u32, array_list.Error] = array_list.get(list, view(&data), u32(1))
  assert(ok_u32(read, u32(20)))
  true ? {
    storage: [*]u32 = span(&data)
    replaced: Result[u32, array_list.Error] = array_list.set(list, storage, u32(1), u32(21))
    assert(ok_u32(replaced, u32(20)))
    removed: Result[u32, array_list.Error] = array_list.remove(list, storage, u32(0))
    assert(ok_u32(removed, u32(10)))
    _ = array_list.push(list, storage, u32(40))
    swapped: Result[u32, array_list.Error] = array_list.swap_remove(list, storage, u32(0))
    assert(ok_u32(swapped, u32(21)))
    popped: Result[u32, array_list.Error] = array_list.pop(list, storage)
    assert(ok_u32(popped, u32(30)))
  }
  assert(list[0].length == u32(1) && data[0] == u32(40))

  before: u32 = data[0]
  true ? {
    storage: [*]u32 = span(&data)
    rejected: Result[u32, array_list.Error] = array_list.set(list, storage, u32(4), u32(99))
    assert(err_u32(rejected, u32(3)))
    rejected_insert: Result[u32, array_list.Error] = array_list.insert(list, storage, u32(3), u32(99))
    assert(err_u32(rejected_insert, u32(3)))
  }
  assert(list[0].length == u32(1) && data[0] == before)

  tiny_state: [1]array_list.Cursor
  tiny_data: [1]u8
  tiny: [*]array_list.Cursor = span(&tiny_state)
  true ? {
    storage: [*]u8 = span(&tiny_data)
    _ = array_list.push(tiny, storage, u8(42))
    rejected: Result[u32, array_list.Error] = array_list.push(tiny, storage, u8(99))
    assert(err_u32(rejected, u32(1)))
  }
  assert(tiny[0].length == u32(1) && tiny_data[0] == u8(42))
  array_list.clear(tiny, u32(1))
  true ? {
    storage: [*]u8 = span(&tiny_data)
    empty: Result[u8, array_list.Error] = array_list.pop(tiny, storage)
    assert(err_u8(empty, u32(2)))
  }
  assert(tiny[0].length == u32(0) && tiny_data[0] == u8(42))
  42
}
`

func TestE2EStdlibArrayListPackage(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/array-list-test\noak 0.1.0\n",
		"main.oak": arrayListPackageProgram,
	})
	comp := New().WithPackageDir(root)
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{
		"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED",
		"oak_strings__", "oak_json__", "oak_encoding__", "oak_buffer__",
	} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("qualified array_list package emitted forbidden %q", forbidden)
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
			t.Fatalf("interpreter error evaluating array_list package: %s", evalErr.Message)
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
		t.Fatalf("compiled array_list package exited (%d, abnormal=%v)", code, abnormal)
	}
}

func TestE2EStdlibArrayListPackageRejectsInvalidCursor(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/array-list-invalid\noak 0.1.0\n",
		"main.oak": `package main
import("array_list")
main: (): i32 {
  state: [1]array_list.Cursor
  state[0].length = u32(2)
  data: [1]u8
  _ = array_list.get(span(&state), view(&data), u32(0))
  0
}
`,
	})
	_, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if !abnormal {
		t.Fatal("invalid qualified array_list cursor must trap")
	}
}

func TestE2EStdlibArrayListPackageAgreesWithFlatPrelude(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/array-list-flat\noak 0.1.0\n",
		"main.oak": `package main

import(std)
import("array_list")

Cursor: type = | LocalCursor
Error: type = | LocalError
push: (): u32 = u32(1)
get: (): u32 = u32(2)
set: (): u32 = u32(3)
pop: (): u32 = u32(4)
insert: (): u32 = u32(5)
remove: (): u32 = u32(6)
swap_remove: (): u32 = u32(7)
clear: (): u32 = u32(8)

main: (): i32 {
  package_state: [1]array_list.Cursor
  flat_state: [1]ArrayListCursor
  package_data: [2]u32
  flat_data: [2]u32
  package_result: Result[u32, array_list.Error] = array_list.push(span(&package_state), span(&package_data), u32(42))
  flat_result: Result[u32, CollectionError] = array_list_push(span(&flat_state), span(&flat_data), u32(42))
  package_index: u32 = package_result ? | .Ok(i) => i | .Err(e) => u32(99)
  flat_index: u32 = flat_result ? | .Ok(i) => i | .Err(e) => u32(99)
  locals: u32 = push() + get() + set() + pop() + insert() + remove() + swap_remove() + clear()
  same: Bool = package_index == flat_index && package_index == u32(0) && package_data[0] == flat_data[0] && package_state[0].length == flat_state[0].length
  same && locals == u32(36) ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("flat and qualified array_list exited (%d, abnormal=%v)", code, abnormal)
	}
}
