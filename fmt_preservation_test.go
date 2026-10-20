package main

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/token"
)

func TestFmtRefusesChangingFieldTagLiteral(t *testing.T) {
	source := "json: tag = { name: string }\nItem: type = struct { id(json: \"first  \nsecond\"): u64 }\n"
	before, err := compiler.New().WithSource("field_tag.oak", source).Parse().Get()
	if err != nil {
		t.Fatalf("fixture must parse: %v", err)
	}
	after, err := compiler.New().WithSource("field_tag.oak", string(canonicalWhitespace([]byte(source)))).Parse().Get()
	if err != nil {
		t.Fatalf("formatted fixture must parse: %v", err)
	}
	t.Logf("AST.String equal before/after: %v", before.Root.String() == after.Root.String())
	assertFmtRefusesRewrite(t, source)
}

func TestFmtRefusesChangingLiteralMetadata(t *testing.T) {
	for _, fixture := range []struct {
		name, source string
	}{
		{"record_tag", "json: tag = { name: string }\nItem: type = struct { id(json: { name: \"first\t\nsecond\" }): u64 }\n"},
		{"field_tag_crlf", "json: tag = { name: string }\nItem: type = struct { id(json: \"first\r\nsecond\"): u64 }\n"},
		{"field_tag_blank_lines", "json: tag = { name: string }\nItem: type = struct { id(json: \"first\n\n\nsecond\"): u64 }\n"},
		{"value_spaces", "message: string = \"first  \nsecond\"\n"},
		{"value_crlf", "message: string = \"first\r\nsecond\"\n"},
		{"value_blank_lines", "message: string = \"first\n\n\nsecond\"\n"},
		// The parser records these symbols; the type checker, not fmt,
		// checks whether they are valid C identifiers.
		{"export_symbol", "export(\"first  \nsecond\") pub f: (): u32 = 1\n"},
		{"extern_symbol", "f: (): c.Int = c.extern(\"first  \nsecond\")\n"},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			assertFmtRefusesRewrite(t, fixture.source)
		})
	}
}

func assertFmtRefusesRewrite(t *testing.T, source string) {
	t.Helper()
	if string(canonicalWhitespace([]byte(source))) == source {
		t.Fatal("fixture must exercise a rewrite")
	}
	for _, text := range []string{source, string(canonicalWhitespace([]byte(source)))} {
		if _, err := compiler.New().WithSource("fixture.oak", text).Parse().Get(); err != nil {
			t.Fatalf("both fixture versions must parse: %v", err)
		}
	}
	for _, mode := range []struct {
		name string
		args []string
	}{
		{"stdout", nil},
		{"list", []string{"-l"}},
		{"write", []string{"-w"}},
		{"list_write", []string{"-l", "-w"}},
	} {
		t.Run(mode.name, func(t *testing.T) {
			file := filepath.Join(t.TempDir(), "literal.oak")
			if err := os.WriteFile(file, []byte(source), 0600); err != nil {
				t.Fatal(err)
			}
			code, out := runCLI(t, fmtCommand, append(append([]string{}, mode.args...), file))
			want := "oak fmt: " + file + " left alone: formatting would change the syntax tree\n"
			if code != 1 || out != want {
				t.Errorf("must refuse a changed literal: code=%d output=%q", code, out)
			}
			data, err := os.ReadFile(file)
			if err != nil || string(data) != source {
				t.Errorf("source changed: %q, %v", data, err)
			}
		})
	}
}

func TestFmtPreservesMetadataAndFormatsTrivia(t *testing.T) {
	for _, fixture := range []struct {
		name, source, want string
	}{
		{
			"comments",
			"/* docs  \r\n \t\r\n\r\nnext */ \t\r\n// comment  \r\nvalue := \"// literal  \" \t\r\n\r\n\r\n",
			"/* docs\n\nnext */\n// comment\nvalue := \"// literal  \"\n",
		},
		{
			"field_metadata",
			"json: tag = { name: string }  \r\nItem: type = struct(align: 16) { id(align: 8, json: \"user  id\"): u64 }  \r\n\r\n",
			"json: tag = { name: string }\nItem: type = struct(align: 16) { id(align: 8, json: \"user  id\"): u64 }\n",
		},
		{
			"unchanged_multiline_tag",
			"json: tag = { name: string }  \nItem: type = struct { id(json: \"first\nsecond\"): u64 }  \n",
			"json: tag = { name: string }\nItem: type = struct { id(json: \"first\nsecond\"): u64 }\n",
		},
		{
			"unchanged_multiline_value",
			"message := \"first\nsecond\"  \n\n\n",
			"message := \"first\nsecond\"\n",
		},
		{
			"escaped_literals",
			"json: tag = { name: string } \r\nItem: type = struct { id(json: \"first\\r\\nsecond\\x20\"): u64 } \r\nmessage := \"quote \\\" \\\\ // /*  \" \r\n",
			"json: tag = { name: string }\nItem: type = struct { id(json: \"first\\r\\nsecond\\x20\"): u64 }\nmessage := \"quote \\\" \\\\ // /*  \"\n",
		},
		{
			"declaration_metadata",
			"export(\"oak_f\") pub f: (): u32 = 1  \r\ng: (): c.Int = c.extern(\"get_value\")  \r\nring: [8]u64 (section: \"shared\")  \r\nh: { Key: type = u64, hash: (Key) -> u64 } = import(\"example.com/hash\")  \r\n",
			"export(\"oak_f\") pub f: (): u32 = 1\ng: (): c.Int = c.extern(\"get_value\")\nring: [8]u64 (section: \"shared\")\nh: { Key: type = u64, hash: (Key) -> u64 } = import(\"example.com/hash\")\n",
		},
		{
			"layout",
			"main: (): i32  \r\n  x := 42  \r\n\r\n\r\n  x  \r\n",
			"main: (): i32\n  x := 42\n\n  x\n",
		},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			file := filepath.Join(t.TempDir(), "fixture.oak")
			if err := os.WriteFile(file, []byte(fixture.source), 0600); err != nil {
				t.Fatal(err)
			}
			if code, out := runCLI(t, fmtCommand, []string{file}); code != 0 || out != fixture.want {
				t.Fatalf("fmt stdout: code=%d output=%q, want %q", code, out, fixture.want)
			}
			if code, out := runCLI(t, fmtCommand, []string{"-l", file}); code != 0 || out != file+"\n" {
				t.Fatalf("fmt list: code=%d output=%q", code, out)
			}
			if data, err := os.ReadFile(file); err != nil || string(data) != fixture.source {
				t.Fatalf("stdout/list changed the source: %q, %v", data, err)
			}
			if code, out := runCLI(t, fmtCommand, []string{"-w", file}); code != 0 || out != "" {
				t.Fatalf("fmt write: code=%d output=%q", code, out)
			}
			if data, err := os.ReadFile(file); err != nil || string(data) != fixture.want {
				t.Fatalf("formatted source: %q, %v", data, err)
			}
			if code, out := runCLI(t, fmtCommand, []string{"-l", file}); code != 0 || out != "" {
				t.Fatalf("fmt not idempotent: code=%d output=%q", code, out)
			}
		})
	}
}

func TestSameSyntaxRejectsMetadataChanges(t *testing.T) {
	for _, fixture := range []struct {
		name, before, after string
	}{
		{"field_tag", "Item: type = struct { id(json: \"a\"): u64 }", "Item: type = struct { id(json: \"b\"): u64 }"},
		{"field_alignment", "Item: type = struct { id(align: 8): u64 }", "Item: type = struct { id(align: 16): u64 }"},
		{"record_layout", "Item: type = struct(packed) { id: u64 }", "Item: type = struct(align: 8) { id: u64 }"},
		{"manifest", "h: { Key: type = u64 } = import(\"example.com/hash\")", "h: { Key: type = u32 } = import(\"example.com/hash\")"},
		{"export_symbol", "export(\"oak_f\") pub f: (): u32 = 1", "export(\"oak_g\") pub f: (): u32 = 1"},
		{"extern_symbol", "f: (): c.Int = c.extern(\"f\")", "f: (): c.Int = c.extern(\"g\")"},
		{"visibility", "pub f: (): u32 = 1", "f: (): u32 = 1"},
		{"token_kind", "value := \"7\"", "value := 7"},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			for _, text := range []string{fixture.before, fixture.after} {
				if _, err := compiler.New().WithSource("fixture.oak", text).Parse().Get(); err != nil {
					t.Fatalf("both fixture versions must parse: %v", err)
				}
			}
			if err := sameSyntax("fixture.oak", []byte(fixture.before), []byte(fixture.after)); err == nil || !strings.Contains(err.Error(), "formatting would change the syntax tree") {
				t.Fatalf("must reject changed metadata: %v", err)
			}
		})
	}
}

func TestSameSyntaxRetainsParseValidation(t *testing.T) {
	for _, fixture := range []struct {
		name, before, after, want string
	}{
		{"original", "value := (", "value := 1", "does not parse:"},
		{"formatted", "value := 1", "value := (", "formatted text does not parse:"},
		{"invalid_utf8", "// \xff\nvalue := 1", "value := 1", "source is not valid UTF-8"},
	} {
		t.Run(fixture.name, func(t *testing.T) {
			if err := sameSyntax("fixture.oak", []byte(fixture.before), []byte(fixture.after)); err == nil || !strings.Contains(err.Error(), fixture.want) {
				t.Fatalf("must retain parse rejection %q: %v", fixture.want, err)
			}
		})
	}
}

func TestFmtScannerKeepsLiteralBytesAndSeparatesComments(t *testing.T) {
	src := scanner.New("// \"not a string\"\r\nvalue := \"first  \r\n\nsecond\\n\\x20\" /* \"also not\" */")
	stringsSeen, commentsSeen := 0, 0
	for {
		tok := src.NextToken()
		switch tok.TokenKind {
		case token.STRING:
			stringsSeen++
			if tok.Literal != "first  \r\n\nsecond\n " {
				t.Fatalf("scanner must retain literal bytes and decode escapes: %q", tok.Literal)
			}
		case token.COMMENT:
			commentsSeen++
		case token.ILLEGAL:
			t.Fatalf("unexpected illegal token: %+v", tok)
		case token.EOF:
			if stringsSeen != 1 || commentsSeen != 2 {
				t.Fatalf("strings=%d comments=%d", stringsSeen, commentsSeen)
			}
			return
		}
	}
}
