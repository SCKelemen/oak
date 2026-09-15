package compiler

import (
	"encoding/binary"
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/evaluator"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/object"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
)

func qualifiedEndianProgram() string {
	type example struct {
		width int
		order string
		value uint64
	}
	examples := []example{
		{width: 16, order: "le", value: 0x8123},
		{width: 16, order: "be", value: 0x8123},
		{width: 32, order: "le", value: 0x81234567},
		{width: 32, order: "be", value: 0x81234567},
		{width: 64, order: "le", value: 0x0123456789abcdef},
		{width: 64, order: "be", value: 0x0123456789abcdef},
	}

	var src strings.Builder
	src.WriteString(`package main

import("endian")

is_buffer_error: (reason: endian.Error): Bool = reason ? | .BufferTooSmall => true

main: (): i32 {
`)
	for k, example := range examples {
		n := example.width / 8
		encoded := make([]byte, n)
		var order binary.ByteOrder = binary.LittleEndian
		if example.order == "be" {
			order = binary.BigEndian
		}
		switch example.width {
		case 16:
			order.PutUint16(encoded, uint16(example.value))
		case 32:
			order.PutUint32(encoded, uint32(example.value))
		case 64:
			order.PutUint64(encoded, example.value)
		}

		fmt.Fprintf(&src, "  data%d: [%d]u8\n  data%d[0] = u8(91)\n  data%d[%d] = u8(92)\n", k, n+2, k, k, n+1)
		fmt.Fprintf(&src, "  true ? {\n    dst%d: [*]u8 = span(&data%d)\n", k, k)
		fmt.Fprintf(&src, "    written%d: Result[u32, endian.Error] = endian.write_u%d_%s(dst%d, u32(1), u%d(%d))\n", k, example.width, example.order, k, example.width, example.value)
		fmt.Fprintf(&src, "    count%d: u32 = written%d ? | .Ok(n) => n | .Err(e) => u32(99)\n    assert(count%d == u32(%d))\n", k, k, k, n)
		for i, value := range encoded {
			fmt.Fprintf(&src, "    assert(dst%d[u32(%d)] == u8(%d))\n", k, i+1, value)
		}
		fmt.Fprintf(&src, "    rejected%d: Result[u32, endian.Error] = endian.write_u%d_%s(dst%d, u32(4294967295), u%d(0))\n", k, example.width, example.order, k, example.width)
		fmt.Fprintf(&src, "    write_error%d: Bool = rejected%d ? | .Ok(n) => false | .Err(reason) => is_buffer_error(reason)\n    assert(write_error%d)\n", k, k, k)
		fmt.Fprintf(&src, "    assert(dst%d[0] == u8(91) && dst%d[%d] == u8(92))\n", k, k, n+1)
		for i, value := range encoded {
			fmt.Fprintf(&src, "    assert(dst%d[u32(%d)] == u8(%d))\n", k, i+1, value)
		}
		src.WriteString("  }\n")

		fmt.Fprintf(&src, "  input%d: [%d]u8\n", k, n+2)
		for i, value := range encoded {
			fmt.Fprintf(&src, "  input%d[u32(%d)] = u8(%d)\n", k, i+1, value)
		}
		fmt.Fprintf(&src, "  view%d: []u8 = view(&input%d)\n", k, k)
		fmt.Fprintf(&src, "  decoded%d: Result[u%d, endian.Error] = endian.read_u%d_%s(view%d, u32(1))\n", k, example.width, example.width, example.order, k)
		fmt.Fprintf(&src, "  value%d: u%d = decoded%d ? | .Ok(value) => value | .Err(e) => u%d(0)\n", k, example.width, k, example.width)
		fmt.Fprintf(&src, "  assert(value%d == u%d(%d))\n", k, example.width, example.value)
		fmt.Fprintf(&src, "  bad_read%d: Result[u%d, endian.Error] = endian.read_u%d_%s(view%d, u32(4294967295))\n", k, example.width, example.width, example.order, k)
		fmt.Fprintf(&src, "  read_error%d: Bool = bad_read%d ? | .Ok(value) => false | .Err(reason) => is_buffer_error(reason)\n  assert(read_error%d)\n", k, k, k)
	}
	src.WriteString("  42\n}\n")
	return src.String()
}

func TestE2EStdlibEndianPackage(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/endian-test\noak 0.1.0\n",
		"main.oak": qualifiedEndianProgram(),
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
			t.Fatalf("qualified endian package emitted forbidden %q", forbidden)
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
			t.Fatalf("interpreter error evaluating endian package: %s", evalErr.Message)
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
		t.Fatalf("compiled endian package exited (%d, abnormal=%v)", code, abnormal)
	}
}

func TestE2EStdlibEndianPackageAgreesWithFlatPrelude(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/endian-flat\noak 0.1.0\n",
		"main.oak": `package main

import(std)
import("endian")

Error: type = | Local
read_u16_le: (): u32 = u32(1)
write_u16_le: (): u32 = u32(2)
read_u16_be: (): u32 = u32(3)
write_u16_be: (): u32 = u32(4)
read_u32_le: (): u32 = u32(5)
write_u32_le: (): u32 = u32(6)
read_u32_be: (): u32 = u32(7)
write_u32_be: (): u32 = u32(8)
read_u64_le: (): u32 = u32(9)
write_u64_le: (): u32 = u32(10)
read_u64_be: (): u32 = u32(11)
write_u64_be: (): u32 = u32(12)

main: (): i32 {
  package_data: [4]u8
  flat_data: [4]u8
  package_write: Result[u32, endian.Error] = endian.write_u32_be(span(&package_data), u32(0), u32(305419896))
  flat_write: Result[u32, EndianError] = bytes_write_u32_be(span(&flat_data), u32(0), u32(305419896))
  package_count: u32 = package_write ? | .Ok(n) => n | .Err(e) => u32(99)
  flat_count: u32 = flat_write ? | .Ok(n) => n | .Err(e) => u32(99)
  package_read: Result[u32, endian.Error] = endian.read_u32_be(view(&package_data), u32(0))
  flat_read: Result[u32, EndianError] = bytes_read_u32_be(view(&flat_data), u32(0))
  package_value: u32 = package_read ? | .Ok(value) => value | .Err(e) => u32(0)
  flat_value: u32 = flat_read ? | .Ok(value) => value | .Err(e) => u32(0)
  locals: u32 = read_u16_le() + write_u16_le() + read_u16_be() + write_u16_be() + read_u32_le() + write_u32_le() + read_u32_be() + write_u32_be() + read_u64_le() + write_u64_le() + read_u64_be() + write_u64_be()
  package_count == flat_count && package_count == u32(4) && package_value == flat_value && package_value == u32(305419896) && locals == u32(78) ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("flat and qualified endian exited (%d, abnormal=%v)", code, abnormal)
	}
}
