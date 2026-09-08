package compiler

import (
	"os"
	"strings"
	"testing"
)

func TestE2EStringViewsBuilderExample(t *testing.T) {
	source, err := os.ReadFile("../examples/strings/runtime_utf8.oak")
	if err != nil {
		t.Fatal(err)
	}
	code, abnormal := buildAndRun(t, "runtime_utf8_builder", string(source))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EStringViews(t *testing.T) {
	source := `
literal: (): string = "hello"
count_bytes: (text: string): u32 {
 bytes: []u8 = str_bytes(text)
 len(bytes)
}
main: (): i32 {
 data: [6]u8
 data[0] = u8(65)
 data[1] = u8(0)
 data[2] = u8(240)
 data[3] = u8(159)
 data[4] = u8(152)
 data[5] = u8(128)
 true ? {
  input: []u8 = view(&data)
  assert(is_valid_utf8(input))
  text: Str[Utf8] = str_from_utf8(input)
  alias: string = text
  bytes: []u8 = str_bytes(alias)
  assert(len(text) == u32(6) && count_bytes(alias) == u32(6))
  assert(bytes[1] == u8(0) && bytes[5] == u8(128))
 }
 data[0] = u8(66)
 empty: [0]u8
 input_empty: []u8 = view(&empty)
 empty_text: string = str_from_utf8(input_empty)
 empty_bytes: []u8 = str_bytes(empty_text)
 assert(len(empty_bytes) == u32(0))
 greeting: string = literal()
 greeting_bytes: []u8 = str_bytes(greeting)
 literal_bytes: []u8 = str_bytes("hi")
 assert(len(greeting_bytes) == u32(5) && literal_bytes[1] == u8(105))
 42
}
`
	code, abnormal := buildAndRun(t, "string_views", source)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	emitted, err := New().WithSource("string_views.oak", source).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	for _, forbidden := range []string{"malloc(", "calloc(", "realloc(", "OAK_UNSUPPORTED"} {
		if strings.Contains(emitted, forbidden) {
			t.Fatalf("unexpected allocation or unsupported lowering: %s", forbidden)
		}
	}
}

func TestE2EStringViewsInvalidUTF8(t *testing.T) {
	code, abnormal := buildAndRun(t, "invalid_string_view", `
main: (): i32 {
 data: [1]u8
 data[0] = u8(255)
 bytes: []u8 = view(&data)
 assert(!is_valid_utf8(bytes))
 text: string = str_from_utf8(bytes)
 42
}
`)
	if !abnormal {
		t.Fatalf("invalid UTF-8 must trap, exit=%d", code)
	}
}

func TestStringViewsRejectUnsafeSourcesAndEscapes(t *testing.T) {
	for _, source := range []string{
		"leak: (bytes: []u8): string { text: string = str_from_utf8(bytes)\ntext }",
		"main: (): i32 { data: [1]u8\nbytes: []u8 = view(&data)\ntext: string = str_from_utf8(bytes)\ndata[0] = u8(1)\n0 }",
		"main: (): i32 { data: [1]u8\nbytes: []u8 = view(&data)\ntext: string = str_from_utf8(bytes)\nwrite: [*]u8 = span(&data)\n0 }",
		"main: (): i32 { data: [1]u8\nbytes: []u8 = view(&data)\ntext: string = str_from_utf8(bytes)\nalias: string = text\ntext = \"other\"\n0 }",
		"main: (): i32 { text: string = \"\"\ntrue ? { data: [1]u8\nbytes: []u8 = view(&data)\ntext = str_from_utf8(bytes) }\n0 }",
		"main: (): i32 { data: [1]u8\ntext: string = str_from_utf8(view(&data))\n0 }",
		"main: (): i32 { data: [1]u8\nwrite: [*]u8 = span(&data)\ntext: string = str_from_utf8(write)\n0 }",
		"main: (): i32 { text: string\n0 }",
		"Box[T]: type = Value: T\nleak: (text: string): Box[string] = .Value(text)",
		"Holder: type = struct { text: string }\nf: (text: string): u32 { h: Holder = Holder { text: text }\nu32(0) }",
		"main: (): i32 { data: [1]u16\nbytes: []u16 = view(&data)\ntext: string = str_from_utf8(bytes)\n0 }",
		"f: (text: Str[Utf16]): u32 { bytes: []u8 = str_bytes(text)\nlen(bytes) }",
		"main: (): i32 { text: string = str_from_utf8()\n0 }",
		"main: (): i32 { bytes: []u8 = str_bytes(u32(0))\n0 }",
	} {
		if _, err := New().WithSource("string_views.oak", source).Check().Get(); err == nil {
			t.Fatalf("unsafe string program accepted:\n%s", source)
		}
	}
}
