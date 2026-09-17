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
	for _, s := range []string{"import \"https://example.invalid/evil\"", "data: u32 = 1", "main: (): i32 = missing()", strings.Repeat("x", MaxSourceBytes+1)} {
		if r := Compile(s); r.Error == "" || r.SourceChecked || r.Module != nil {
			t.Fatalf("unsupported input accepted: %+v", r)
		}
	}
}
