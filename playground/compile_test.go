package playground

import (
	"bytes"
	"encoding/json"
	"strings"
	"testing"
	"unicode/utf16"
	"unicode/utf8"

	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/lsp"
	"github.com/SCKelemen/oak/wasm"
	"github.com/SCKelemen/oak/wasm/check"
)

func TestCompile(t *testing.T) {
	r := Compile("main: (): i32 = 42")
	if r.Error != "" || !r.SourceChecked || r.Module == nil || r.Module.TranslationVerified || len(r.SourceSHA256) != 64 || len(r.ModuleSHA256) != 64 {
		t.Fatalf("unexpected result: %+v", r)
	}
	if r.Module.ByteValidation == nil || r.Module.ByteValidation.SHA256 != r.ModuleSHA256 {
		t.Fatal("byte validation not bound to downloaded module")
	}
	if r.Pipeline == nil || len(r.Pipeline.Steps) != 4 || r.Pipeline.Target.Environment != "core-import-free" {
		t.Fatal("missing emission provenance", r.Pipeline)
	}
	for _, s := range []string{"import \"https://example.invalid/evil\"", "data: u32 = 1", "main: (): i32 = missing()", strings.Repeat("x", MaxSourceBytes+1)} {
		if r := Compile(s); r.Error == "" || r.SourceChecked || r.Module != nil || r.Pipeline != nil {
			t.Fatalf("unsupported input accepted: %+v", r)
		}
	}
}

func TestCompileDivisionProfile(t *testing.T) {
	for _, source := range []string{
		"quot: (x: i64, y: i64): i64 = x / y\nmain: (): i64 = quot(-i64(127), -i64(3))",
		"main: (): u32 = u32(91) % u32(7)",
	} {
		r := Compile(source)
		if r.Error != "" || !r.SourceChecked || r.Module == nil || r.Module.TranslationVerified {
			t.Fatalf("division did not pass browser API: %+v", r)
		}
		if r.Module.Profile != wasm.Profile || r.Module.ByteValidation == nil ||
			r.Module.ByteValidation.Profile != wasm.Profile || r.Module.ByteValidation.Validator != check.Validator {
			t.Fatal("mismatched profile or validator revision", r.Module)
		}
	}
}

func TestCompileDiagnostics(t *testing.T) {
	for _, tc := range []struct{ source, prefix string }{
		{"main: (): i32 { 42 } }", "OAK-P"},
		{"/* 😀 */ main: (): i32 = missing()", "OAK-T"},
	} {
		r := Compile(tc.source)
		if r.Error == "" || len(r.Diagnostics) == 0 || r.Module != nil || r.SourceSHA256 == "" {
			t.Fatalf("missing source-bound refusal: %+v", r)
		}
		found := false
		for _, d := range r.Diagnostics {
			if !strings.HasPrefix(d.Code, tc.prefix) || d.Range == nil {
				continue
			}
			if tc.prefix == "OAK-T" && !strings.Contains(d.Message, "missing") {
				continue
			}
			found = true
			if tc.prefix == "OAK-T" {
				want := len(utf16.Encode([]rune(tc.source[:strings.Index(tc.source, "missing")])))
				if d.Range.Start.Line != 0 || d.Range.Start.Character != want {
					t.Fatalf("not the missing identifier's UTF-16 position: %+v, want %d", d, want)
				}
			}
		}
		if !found {
			t.Fatalf("missing structured %s diagnostic: %+v", tc.prefix, r.Diagnostics)
		}
		encoded, err := json.Marshal(r)
		if err != nil || !bytes.Contains(encoded, []byte(`"range":{"start":{"line":`)) {
			t.Fatalf("missing browser range schema: %s, %v", encoded, err)
		}
	}
	// A profile/backend refusal is not a parser range and must not pretend to be.
	for _, source := range []string{"data: u32 = 1", "main: (): f32 = 1.0"} {
		r := Compile(source)
		if r.Error == "" || len(r.Diagnostics) == 0 {
			t.Fatalf("expected profile refusal: %+v", r)
		}
		last := r.Diagnostics[len(r.Diagnostics)-1]
		if last.Source != "playground" || last.Range != nil {
			t.Fatalf("invented location for unstructured refusal: %+v", last)
		}
	}
}

func TestCompileDiagnosticsBounded(t *testing.T) {
	var r Response
	r.addDiagnostic(nil)
	for i := 0; i < MaxDiagnostics+3; i++ {
		r.addDiagnostic(&diagnostic.Diagnostic{
			Severity: diagnostic.SeverityError, Code: strings.Repeat("c", 200),
			Message: strings.Repeat("a", MaxDiagnosticBytes-1) + "😀",
			File:    "another.oak", Data: make(chan int),
		})
	}
	if len(r.Diagnostics) != MaxDiagnostics || !r.DiagnosticsTruncated {
		t.Fatal("diagnostic count not bounded")
	}
	d := r.Diagnostics[0]
	if len(d.Message) > MaxDiagnosticBytes || !utf8.ValidString(d.Message) || len(d.Code) != 128 || d.Range != nil {
		t.Fatalf("projection not bounded/UTF-8/own-file safe: %+v", d)
	}
	if _, err := json.Marshal(r); err != nil {
		t.Fatal("open-ended compiler payload escaped projection:", err)
	}
	r = Response{}
	r.addDiagnostic(&diagnostic.Diagnostic{Range: lsp.Range{Start: lsp.Position{Line: -1}}})
	if r.Diagnostics[0].Range != nil {
		t.Fatal("negative range retained")
	}
	r.refuse(strings.Repeat("e", MaxDiagnosticBytes+1))
	if len(r.Error) != MaxDiagnosticBytes {
		t.Fatal("compatibility error not bounded")
	}
}

func TestCompileRequestsAreIsolated(t *testing.T) {
	first := Compile("helper: (): i32 = 41\nmain: (): i32 = helper()")
	if first.Error != "" {
		t.Fatal(first.Error)
	}
	before := append([]byte(nil), first.Module.Bytes...)
	missing := Compile("main: (): i32 = helper()")
	if missing.Error == "" || missing.Module != nil {
		t.Fatal("symbols leaked between requests")
	}
	next := Compile("main: (): i32 = 42")
	if next.Error != "" || next.ModuleSHA256 == first.ModuleSHA256 || next.SourceSHA256 == first.SourceSHA256 {
		t.Fatalf("request reused prior result: %+v", next)
	}
	if !bytes.Equal(first.Module.Bytes, before) {
		t.Fatal("later compilation mutated an earlier artifact")
	}
	if len(next.Diagnostics) != 0 {
		t.Fatal("failed request's diagnostics leaked:", next.Diagnostics)
	}
}
