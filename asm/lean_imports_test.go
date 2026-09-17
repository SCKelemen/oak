package asm

import (
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// leanModuleName is the shape of a module a generated oracle may import:
// Oak's own modules, dotted identifiers only, so the names reach the
// build command as arguments and nothing else does.
var leanModuleName = regexp.MustCompile(`^Oak(\.[A-Za-z0-9_]+)*$`)

// buildLeanImports builds, in the Lean project, the Oak modules the
// generated oracle file at leanPath imports. `lake env lean` reads the
// modules' object files and builds nothing, so a library left stale by
// modules that landed since the last `lake build` fails the kernel check
// with "object file ... does not exist" (the formal workflow builds
// first; a checkout does not). Up to date, the build is a no-op.
func buildLeanImports(t *testing.T, lake, leanPath string) {
	t.Helper()
	source, err := os.ReadFile(leanPath)
	if err != nil {
		t.Fatal(err)
	}
	var modules []string
	for _, line := range strings.Split(string(source), "\n") {
		name, isImport := strings.CutPrefix(strings.TrimSpace(line), "import ")
		name = strings.TrimSpace(name)
		if isImport && leanModuleName.MatchString(name) {
			modules = append(modules, name)
		}
	}
	if len(modules) == 0 {
		return
	}
	command := exec.Command(lake, append([]string{"build"}, modules...)...)
	command.Dir = filepath.Join("..", "spec", "lean")
	if output, err := command.CombinedOutput(); err != nil {
		t.Fatalf("building the Lean modules the oracle imports (%s): %v\n%s", strings.Join(modules, ", "), err, output)
	}
}
