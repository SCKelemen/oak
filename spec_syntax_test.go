package main

import (
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/compiler"
	"github.com/SCKelemen/oak/prove"
)

// TestOakSyntaxAgrees compares the syntax table the serializer written in
// Oak builds for every pending theorem of the corpus with the Go
// serializer's, word for word.
func TestOakSyntaxAgrees(t *testing.T) {
	files, err := filepath.Glob(filepath.Join("spec", "oak", "*.oak"))
	if err != nil || len(files) == 0 {
		t.Fatalf("spec/oak: %v (%d files)", err, len(files))
	}
	for _, file := range files {
		file := file
		if strings.HasSuffix(file, "_lean.oak") {
			continue
		}
		t.Run(filepath.Base(file), func(t *testing.T) {
			source, err := os.ReadFile(file)
			if err != nil {
				t.Fatal(err)
			}
			model, err := compiler.New().WithSyntaxRewrite(prove.Obligations).WithSource(file, string(source)).Check().Get()
			if err != nil {
				t.Fatal(err)
			}
			results, err := prove.TheoremsWith(model, prove.DefaultCases, true)
			if err != nil {
				t.Fatal(err)
			}
			var names []string
			for _, r := range results {
				if r.Status == prove.Pending {
					names = append(names, r.Name)
				}
			}
			dump := filepath.Join(t.TempDir(), "dump.txt")
			t.Setenv("OAK_SOLVER_DUMP", dump)
			code, out := runCLI(t, func(args []string) int { return proveCommand(args, os.Stdout, os.Stderr) }, []string{"-solver", "oak", "-cross", "none", file})
			if code != 0 {
				t.Fatalf("exit %d:\n%s", code, out)
			}
			data, _ := os.ReadFile(dump)
			seen := map[int]bool{}
			for _, line := range strings.Split(string(data), "\n") {
				fields := strings.Fields(line) // slot k S index n words...
				if len(fields) < 5 || fields[2] != "S" {
					continue
				}
				index, _ := strconv.Atoi(fields[3])
				n, _ := strconv.Atoi(fields[4])
				if seen[index] || index >= len(names) || len(fields) != 5+n {
					continue
				}
				seen[index] = true
				got := make([]uint32, n)
				for i := range got {
					x, _ := strconv.ParseUint(fields[5+i], 10, 32)
					got[i] = uint32(x)
				}
				want, ok := prove.GoSyntax(model, names[index])
				if !ok {
					t.Errorf("%s: serialized in Oak, refused by the Go serializer", names[index])
					continue
				}
				if len(got) != len(want) {
					t.Errorf("%s: %d words in Oak, %d in Go", names[index], len(got), len(want))
				}
				for i := range got {
					if i < len(want) && got[i] != want[i] {
						t.Errorf("%s: word %d is %d in Oak, %d in Go", names[index], i, got[i], want[i])
						break
					}
				}
			}
			for i, name := range names {
				if _, ok := prove.GoSyntax(model, name); ok && !seen[i] {
					t.Errorf("%s: serialized in Go, not in Oak", name)
				}
			}
			if len(seen) == 0 && len(names) > 0 {
				t.Fatalf("no syntax table dumped for %d pending theorems", len(names))
			}
			t.Logf("%d of %d pending theorems compared", len(seen), len(names))
		})
	}
}
