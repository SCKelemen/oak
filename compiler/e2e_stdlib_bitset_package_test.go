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

const bitsetPackageProgram = `package main

import("bitset")

is_storage_error: (reason: bitset.Error): Bool = reason ?
  | .StorageTooSmall => true
  | .BitOutOfRange => false

main: (): i32 {
  data: [2]u8
  data[0] = u8(129)
  data[1] = u8(254)
  true ? {
    bits: [*]u8 = span(&data)
    first: Result[Bool, bitset.Error] = bitset.set(bits, u32(9), u32(8), true)
    first_previous: Bool = first ? | .Ok(previous) => previous | .Err(e) => true
    assert(!first_previous && bits[1] == u8(255))

    second: Result[Bool, bitset.Error] = bitset.set(bits, u32(9), u32(8), false)
    second_previous: Bool = second ? | .Ok(previous) => previous | .Err(e) => false
    assert(second_previous && bits[1] == u8(254))
    _ = bitset.set(bits, u32(9), u32(8), true)
  }

  present: Result[Bool, bitset.Error] = bitset.contains(view(&data), u32(9), u32(7))
  has_seven: Bool = present ? | .Ok(value) => value | .Err(e) => false
  total: Result[u32, bitset.Error] = bitset.count_ones(view(&data), u32(9))
  logical_count: u32 = total ? | .Ok(value) => value | .Err(e) => u32(99)
  assert(has_seven && logical_count == u32(3))
  assert(bitset.storage_bytes(u32(0)) == u32(0))
  assert(bitset.storage_bytes(u32(9)) == u32(2))
  assert(bitset.storage_bytes(u32(4294967295)) == u32(536870912))

  short_data: [1]u8
  short_data[0] = u8(77)
  short: [*]u8 = span(&short_data)
  too_short: Result[Bool, bitset.Error] = bitset.set(short, u32(9), u32(4294967295), false)
  storage_error: Bool = too_short ? | .Ok(value) => false | .Err(reason) => is_storage_error(reason)
  assert(storage_error && short[0] == u8(77))

  true ? {
    bits: [*]u8 = span(&data)
    before: u8 = bits[0]
    outside: Result[Bool, bitset.Error] = bitset.set(bits, u32(8), u32(8), false)
    range_error: Bool = outside ? | .Ok(value) => false | .Err(reason) => !is_storage_error(reason)
    assert(range_error && bits[0] == before)
  }
  42
}
`

func TestE2EStdlibBitsetPackage(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/bitset-test\noak 0.1.0\n",
		"main.oak": bitsetPackageProgram,
	})
	comp := New().WithPackageDir(root)
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{
		"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED",
		"oak_strings__", "oak_json__", "oak_filters__", "oak_bitset_algebra__",
	} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("qualified bitset package emitted forbidden %q", forbidden)
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
			t.Fatalf("interpreter error evaluating bitset package: %s", evalErr.Message)
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
		t.Fatalf("compiled bitset package exited (%d, abnormal=%v)\n%s", code, abnormal, cFunctionBody(t, output, "oak_main"))
	}
}

func TestE2EStdlibBitsetPackageAgreesWithFlatPrelude(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/bitset-flat\noak 0.1.0\n",
		"main.oak": `package main

import(std)
import("bitset")

Error: type = | Local
storage_bytes: (): u32 = u32(11)
contains: (): u32 = u32(12)
set: (): u32 = u32(13)
count_ones: (): u32 = u32(14)

main: (): i32 {
  package_data: [1]u8
  flat_data: [1]u8
  package_bits: [*]u8 = span(&package_data)
  flat_bits: [*]u8 = span(&flat_data)
  package_result: Result[Bool, bitset.Error] = bitset.set(package_bits, u32(8), u32(2), true)
  flat_result: Result[Bool, BitSetError] = bitset_set(flat_bits, u32(8), u32(2), true)
  package_previous: Bool = package_result ? | .Ok(value) => value | .Err(e) => true
  flat_previous: Bool = flat_result ? | .Ok(value) => value | .Err(e) => true
  same_sizes: Bool = bitset.storage_bytes(u32(9)) == bitset_storage_bytes(u32(9))
  local_names: Bool = storage_bytes() == u32(11) && contains() == u32(12) && set() == u32(13) && count_ones() == u32(14)
  !package_previous && !flat_previous && package_bits[0] == flat_bits[0] && same_sizes && local_names ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("flat and qualified bitset exited (%d, abnormal=%v)", code, abnormal)
	}
}
