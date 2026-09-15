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

const bytesPackageProgram = `package main

import("bytes")

main: (): i32 {
  input: [3]u8
  other: [3]u8
  output: [4]u8
  tiny: [1]u8
  input[0] = u8(10)
  input[1] = u8(20)
  input[2] = u8(30)
  other[0] = u8(10)
  other[1] = u8(21)
  other[2] = u8(30)
  output[3] = u8(44)
  tiny[0] = u8(77)

  src: []u8 = view(&input)
  dst: [*]u8 = span(&output)
  small: [*]u8 = span(&tiny)

  copied: Result[u32, bytes.CopyError] = bytes.copy_into(dst, src)
  count: u32 = copied ? | .Ok(n) => n | .Err(e) => u32(99)
  assert(count == u32(3))
  assert(dst[0] == u8(10) && dst[1] == u8(20) && dst[2] == u8(30))
  assert(dst[3] == u8(44))

  failed: Result[u32, bytes.CopyError] = bytes.copy_into(small, src)
  rejected: Bool = failed ? | .Ok(n) => false | .Err(.DestinationTooSmall) => true
  assert(rejected && small[0] == u8(77))

  assert(bytes.equal(src, view(&input)))
  assert(!bytes.equal(src, view(&other)))
  assert(!bytes.equal(src, src[u32(0):u32(1)]))
  first: Option[u32] = bytes.find(src, u8(20))
  missing: Option[u32] = bytes.find(src, u8(99))
  first_index: u32 = first ? | .Some(i) => i | .None => u32(99)
  missing_present: Bool = missing ? | .Some(i) => true | .None => false
  assert(first_index == u32(1))
  assert(!missing_present)

  assert(bytes.range_fits(u32(3), u32(3), u32(0)))
  assert(!bytes.range_fits(u32(3), u32(4), u32(0)))
  assert(!bytes.range_fits(u32(3), u32(4294967295), u32(1)))

  filled: [3]u8
  bytes.fill(span(&filled), u8(9))
  assert(filled[0] == u8(9) && filled[1] == u8(9) && filled[2] == u8(9))

  placed: [5]u8
  placed[0] = u8(91)
  placed[4] = u8(92)
  true ? {
    target: [*]u8 = span(&placed)
    at: Result[u32, bytes.RangeError] = bytes.copy_at(target, u32(1), src)
    at_count: u32 = at ? | .Ok(n) => n | .Err(e) => u32(99)
    assert(at_count == u32(3))
    rejected_at: Result[u32, bytes.RangeError] = bytes.copy_at(target, u32(4294967295), src)
    rejected_range: Bool = rejected_at ? | .Ok(n) => false | .Err(.OutOfBounds) => true
    assert(rejected_range)
  }
  assert(placed[0] == u8(91) && placed[1] == u8(10) && placed[2] == u8(20) && placed[3] == u8(30) && placed[4] == u8(92))

  shift_right: [5]u8
  shift_left: [5]u8
  i: u32 = 0
  while i < u32(5) {
    shift_right[i] = u8_trunc_u32(i + u32(1))
    shift_left[i] = u8_trunc_u32(i + u32(1))
    i = i + u32(1)
  }
  right_result: Result[u32, bytes.RangeError] = bytes.move_within(span(&shift_right), u32(1), u32(0), u32(4))
  left_result: Result[u32, bytes.RangeError] = bytes.move_within(span(&shift_left), u32(0), u32(1), u32(4))
  right_count: u32 = right_result ? | .Ok(n) => n | .Err(e) => u32(99)
  left_count: u32 = left_result ? | .Ok(n) => n | .Err(e) => u32(99)
  assert(right_count == u32(4) && left_count == u32(4))
  assert(shift_right[0] == u8(1) && shift_right[1] == u8(1) && shift_right[2] == u8(2) && shift_right[3] == u8(3) && shift_right[4] == u8(4))
  assert(shift_left[0] == u8(2) && shift_left[1] == u8(3) && shift_left[2] == u8(4) && shift_left[3] == u8(5) && shift_left[4] == u8(5))

  prefix: [2]u8
  prefix[0] = u8(10)
  prefix[1] = u8(20)
  assert(bytes.compare(src, view(&other)) < 0)
  assert(bytes.compare(src, src) == 0)
  assert(bytes.compare(view(&prefix), src) < 0)
  42
}
`

func TestE2EStdlibBytesPackage(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/bytes-test\noak 0.1.0\n",
		"main.oak": bytesPackageProgram,
	})
	comp := New().WithPackageDir(root)
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{
		"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED",
		"oak_strings__", "oak_json__", "oak_encoding__",
	} {
		if strings.Contains(output, forbidden) {
			t.Fatalf("qualified bytes package emitted forbidden %q", forbidden)
		}
	}
	code, abnormal := buildPackageAndRun(t, comp)
	if abnormal || code != 42 {
		t.Fatalf("compiled bytes package exited (%d, abnormal=%v)", code, abnormal)
	}

	model, err := comp.Check().Get()
	if err != nil {
		t.Fatalf("check failed: %v", err)
	}
	env := object.NewEnvironment()
	env.SetArithmeticWidths(model.TypeChecker.ArithmeticType)
	if result := evaluator.Eval(model.Tree.Root, env); result != nil {
		if evalErr, isErr := result.(*object.Error); isErr {
			t.Fatalf("interpreter error evaluating bytes package: %s", evalErr.Message)
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
}

func TestE2EStdlibBytesPackageAgreesWithFlatPrelude(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/bytes-flat\noak 0.1.0\n",
		"main.oak": `package main

import(std)
import("bytes")

equal: (): Bool = true
find: (): u32 = u32(7)
copy_into: (): u32 = u32(9)
RangeError: type = | LocalRange
range_fits: (): Bool = true
fill: (): u32 = u32(10)
copy_at: (): u32 = u32(11)
move_within: (): u32 = u32(12)
compare: (): u32 = u32(13)

main: (): i32 {
  data: [2]u8
  data[0] = u8(4)
  data[1] = u8(2)
  src: []u8 = view(&data)
  assert(bytes.equal(src, src) == bytes_equal(src, src))
  package_index: Option[u32] = bytes.find(src, u8(2))
  flat_index: Option[u32] = bytes_find(src, u8(2))
  p: u32 = package_index ? | .Some(i) => i | .None => u32(99)
  f: u32 = flat_index ? | .Some(i) => i | .None => u32(99)
  ranges_agree: Bool = bytes.range_fits(u32(2), u32(1), u32(1)) == bytes_range_fits(u32(2), u32(1), u32(1))
  local_names: Bool = range_fits() && fill() == u32(10) && copy_at() == u32(11) && move_within() == u32(12) && compare() == u32(13)
  p == f && p == u32(1) && ranges_agree && local_names && equal() && find() == u32(7) && copy_into() == u32(9) ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("flat and qualified bytes exited (%d, abnormal=%v)", code, abnormal)
	}
}
