package lrat

import (
	"go/parser"
	"go/token"
	"os"
	"strconv"
	"strings"
	"testing"
)

// TestAcceptanceKernelDependencyBoundary protects the LRAT acceptance leaf
// against accidentally importing the prover, compiler, or any external
// implementation. New trusted dependencies require an explicit audit here.
func TestAcceptanceKernelDependencyBoundary(t *testing.T) {
	allowed := map[string]bool{
		"fmt":     true,
		"strconv": true,
		"strings": true,
	}
	entries, err := os.ReadDir(".")
	if err != nil {
		t.Fatal(err)
	}
	count := 0
	for _, entry := range entries {
		name := entry.Name()
		if entry.IsDir() || !strings.HasSuffix(name, ".go") || strings.HasSuffix(name, "_test.go") {
			continue
		}
		count++
		file, err := parser.ParseFile(token.NewFileSet(), name, nil, parser.ImportsOnly)
		if err != nil {
			t.Fatalf("parse acceptance-kernel source %s: %v", name, err)
		}
		if file.Name.Name != "lrat" {
			t.Errorf("acceptance-kernel file %s uses package %s", name, file.Name.Name)
		}
		for _, spec := range file.Imports {
			path, err := strconv.Unquote(spec.Path.Value)
			if err != nil || !allowed[path] {
				t.Errorf("acceptance-kernel file %s imports %s; review and explicitly allow any new trusted dependency", name, spec.Path.Value)
			}
		}
	}
	if count == 0 {
		t.Fatal("no production acceptance-kernel source files")
	}
}
