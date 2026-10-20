package main

import (
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"reflect"
	"sort"
	"strings"
	"testing"
)

func fixture(t *testing.T, files map[string]string) string {
	t.Helper()
	root := t.TempDir()
	files["go.mod"] = "module example.org/oak\n"
	for name, contents := range files {
		path := filepath.Join(root, name)
		if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(contents), 0644); err != nil {
			t.Fatal(err)
		}
	}
	return root
}

func TestInventorySourceAndTestBoundaries(t *testing.T) {
	root := fixture(t, map[string]string{
		"compiler/a.go":               "package compiler\nimport alias `example.org/oak/machine`\n// import \"example.org/oak/fake\"\nvar _ = `import \"example.org/oak/fake\"`\n",
		"compiler/a_test.go":          "package compiler_test\nimport . \"example.org/oak/compiler\"\n",
		"compiler/internal_test.go":   "package compiler\nimport _ \"example.org/oak/testhelper\"\n",
		"machine/a.go":                "package machine\nimport \"example.org/oak/asm\"\n",
		"machine/b_plan9.go":          "//go:build plan9\n\npackage machine\nimport \"example.org/oak/optir\"\n",
		"asm/a.go":                    "package asm\n",
		"optir/a.go":                  "package optir\n",
		"other/a.go":                  "package other\nimport \"example.org/oak/compiler\"\n",
		"nested/go.mod":               "module example.org/nested\n",
		"nested/a.go":                 "broken",
		"compiler/testdata/broken.go": "broken",
		"vendor/broken.go":            "broken",
	})
	got, err := scan(root)
	if err != nil {
		t.Fatal(err)
	}
	want := []string{"asm", "compiler", "machine", "optir"}
	if !reflect.DeepEqual(got.ProductionClosure, want) {
		t.Fatalf("closure = %v", got.ProductionClosure)
	}
	if !reflect.DeepEqual(got.DirectConsumers, []string{"other"}) {
		t.Fatalf("consumers = %v", got.DirectConsumers)
	}
	if len(got.TestEdges) != 2 || got.TestEdges[0].From != "compiler" || got.TestEdges[1].From != "compiler_test" {
		t.Fatalf("test edges = %v", got.TestEdges)
	}
	for _, edge := range got.ProductionEdges {
		if strings.Contains(edge.To, "fake") || strings.Contains(edge.To, "testhelper") {
			t.Fatalf("spurious edge %v", edge)
		}
	}
	again, err := scan(root)
	if err != nil {
		t.Fatal(err)
	}
	a, _ := json.Marshal(got)
	b, _ := json.Marshal(again)
	if string(a) != string(b) {
		t.Fatal("nondeterministic inventory")
	}
}

func TestCycles(t *testing.T) {
	graph := map[string][]string{"compiler": {"machine"}, "machine": {"asm"}, "asm": {"compiler"}, "optir": {"optir"}, "leaf": {}}
	want := [][]string{{"asm", "compiler", "machine"}, {"optir"}}
	if got := cycles(graph, []string{"compiler", "optir", "leaf"}); !reflect.DeepEqual(got, want) {
		t.Fatalf("cycles = %v", got)
	}
	if got := cycles(map[string][]string{"a": {"b"}}, []string{"a"}); len(got) != 0 {
		t.Fatalf("acyclic graph = %v", got)
	}
}

func TestExactBodiesAndParseFailure(t *testing.T) {
	body := "{\n" + strings.Repeat("println(1)\n", 20) + "}\n"
	root := fixture(t, map[string]string{"asm/a.go": "package asm\nfunc a() " + body, "machine/b.go": "package machine\nfunc b() " + body})
	got, err := scan(root)
	if err != nil {
		t.Fatal(err)
	}
	if len(got.ExactBodyCandidates) != 1 || len(got.ExactBodyCandidates[0].Sites) != 2 {
		t.Fatalf("duplicates = %v", got.ExactBodyCandidates)
	}
	if err := os.WriteFile(filepath.Join(root, "asm/a.go"), []byte("broken"), 0644); err != nil {
		t.Fatal(err)
	}
	if _, err := scan(root); err == nil {
		t.Fatal("silently accepted invalid Go")
	}
}

func TestRepositoryDependencyBoundaries(t *testing.T) {
	inv, err := scan(filepath.Join("..", ".."))
	if err != nil {
		t.Fatal(err)
	}
	if len(inv.Cycles) != 0 {
		t.Fatalf("production source-union cycles: %v", inv.Cycles)
	}
	for _, violation := range dependencyBoundaryViolations(inv) {
		t.Error(violation)
	}
}

func dependencyBoundaryViolations(inv Inventory) []string {
	// These are directional architecture constraints, not a freeze of the
	// dependency snapshot. Independent checker and IR layers must not acquire
	// dependencies on their producers, even through a new intermediary package.
	forbidden := map[string][]string{
		"asm":       {"compiler", "nativegen", "machine", "optir"},
		"optir":     {"compiler", "nativegen", "machine", "asm"},
		"machine":   {"compiler", "nativegen"},
		"nativegen": {"compiler"},
	}
	graph := map[string][]string{}
	for _, edge := range inv.ProductionEdges {
		graph[edge.From] = append(graph[edge.From], edge.To)
	}
	var violations []string
	for _, pkg := range inv.Packages {
		source := pkg.Path
		for prefix, denied := range forbidden {
			if source != prefix && !strings.HasPrefix(source, prefix+"/") {
				continue
			}
			seen := map[string]bool{}
			var visit func(string)
			visit = func(node string) {
				if seen[node] {
					return
				}
				seen[node] = true
				for _, next := range graph[node] {
					visit(next)
				}
			}
			visit(source)
			for node := range seen {
				for _, boundary := range denied {
					if node == boundary || strings.HasPrefix(node, boundary+"/") {
						violations = append(violations, fmt.Sprintf("%s transitively imports forbidden producer %s", source, node))
					}
				}
			}
		}
	}
	sort.Strings(violations)
	return violations
}

func TestDependencyBoundarySubpackages(t *testing.T) {
	for _, tc := range []struct {
		name          string
		source        string
		target        string
		indirect      bool
		wantViolation bool
	}{
		{"unimported subpackage", "optir/analysis", "asm", false, true},
		{"transitive unimported subpackage", "asm/checks", "compiler/lower", true, true},
		{"root transitive", "machine", "nativegen", true, true},
		{"allowed dependency", "machine/analysis", "optir", false, false},
		{"similar source prefix", "optirhelper", "asm", false, false},
		{"similar target prefix", "optir/analysis", "asmhelper", false, false},
	} {
		t.Run(tc.name, func(t *testing.T) {
			files := map[string]string{
				"optir/a.go": "package optir\n",
				"asm/a.go":   "package asm\n",
			}
			target := tc.target
			if tc.indirect {
				files["helper/a.go"] = "package helper\nimport _ \"example.org/oak/" + target + "\"\n"
				target = "helper"
			}
			files[tc.source+"/boundary.go"] = "package boundary\nimport _ \"example.org/oak/" + target + "\"\n"
			inv, err := scan(fixture(t, files))
			if err != nil {
				t.Fatal(err)
			}
			got := dependencyBoundaryViolations(inv)
			if tc.wantViolation {
				want := []string{tc.source + " transitively imports forbidden producer " + tc.target}
				if !reflect.DeepEqual(got, want) {
					t.Fatalf("violations = %v, want %v", got, want)
				}
			} else if len(got) != 0 {
				t.Fatalf("unexpected violations: %v", got)
			}
		})
	}
}
