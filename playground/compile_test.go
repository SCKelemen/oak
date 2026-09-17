package playground

import (
	"strings"
	"testing"
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
