package compiler

import (
	"os"
	"path/filepath"
	"reflect"
	"testing"

	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/stdlib"
)

func BenchmarkWalkSyntax(b *testing.B) {
	for _, name := range []string{"time", "json"} {
		b.Run(name, func(b *testing.B) {
			source, ok := stdlib.Packages[name]
			if !ok {
				b.Fatal("missing fixture", name)
			}
			p := parser.New(layout.New(scanner.New(source)))
			tree := p.ParseProgram()
			if errs := p.Errors(); len(errs) != 0 {
				b.Fatal(errs)
			}
			value := reflect.ValueOf(tree)
			count := 0
			visit := func(any) bool { count++; return true }
			walkSyntax(value, visit)
			b.ReportAllocs()
			b.ResetTimer()
			for b.Loop() {
				walkSyntax(value, visit)
			}
			if count == 0 {
				b.Fatal("empty traversal")
			}
		})
	}
}

// Include parsing, checking, lowering and C source emission. No external C
// compiler runs here. Warm up the existing prelude caches before timing.
func BenchmarkCompileWithSyntaxWalk(b *testing.B) {
	for _, fixture := range []struct{ name, source string }{
		{"json", "import(\"json\")\nmain: (): i32 { _ = json.json_encoder(); 42 }\n"},
		{"strings", "import(\"strings\")\nmain: (): i32 { i32(strings.ascii_lower(u8(65))) - 55 }\n"},
	} {
		b.Run(fixture.name, func(b *testing.B) {
			dir := b.TempDir()
			for name, source := range map[string]string{
				"oak.mod":  "module example.com/syntaxbench\noak 0.1.0\n",
				"main.oak": "package main\n" + fixture.source,
			} {
				if err := os.WriteFile(filepath.Join(dir, name), []byte(source), 0600); err != nil {
					b.Fatal(err)
				}
			}
			code, err := New().WithPackageDir(dir).EmitC().Get()
			if err != nil {
				b.Fatal(err)
			}
			b.ReportAllocs()
			for b.Loop() {
				var err error
				code, err = New().WithPackageDir(dir).EmitC().Get()
				if err != nil {
					b.Fatal(err)
				}
			}
			b.ReportMetric(float64(len(code)), "C-bytes")
		})
	}
}
