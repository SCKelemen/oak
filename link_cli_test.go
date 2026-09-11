package main

import (
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// archiveFixture compiles one C function into <root>/native/libhello.a for
// a manifest `link native/libhello.a` line (docs/spec/83-modules.md section
// 4.6). Skips when the host has no C toolchain.
func archiveFixture(t *testing.T, root, csrc string) {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	ar, err := exec.LookPath("ar")
	if err != nil {
		t.Skip("no archiver on PATH")
	}
	dir := filepath.Join(root, "native")
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(dir, "hello.c"), []byte(csrc), 0o644); err != nil {
		t.Fatal(err)
	}
	if out, err := exec.Command(cc, "-std=c99", "-c", "-o", filepath.Join(dir, "hello.o"), filepath.Join(dir, "hello.c")).CombinedOutput(); err != nil {
		t.Fatalf("cc -c: %v\n%s", err, out)
	}
	if out, err := exec.Command(ar, "rcs", filepath.Join(dir, "libhello.a"), filepath.Join(dir, "hello.o")).CombinedOutput(); err != nil {
		t.Fatalf("ar: %v\n%s", err, out)
	}
}

// `oak build` and `oak run` link the manifest's native inputs into the
// executable, and a rebuilt archive is not served from the build cache.
func TestBuildAndRunLinkManifestInputs(t *testing.T) {
	app := writeTree(t, map[string]string{
		"oak.mod": "module example.com/linked\nlink native/libhello.a\n",
		"main.oak": `package main

hello: (x: c.Int): c.Int = c.extern("oak_cli_hello")

main: (): i32 {
  answer: c.Int = hello(c.Int(40))
  i32(answer)
}
`,
	})
	archiveFixture(t, app, "int oak_cli_hello(int x) { return x + 2; }\n")
	bin := filepath.Join(t.TempDir(), "linked")
	if code, out := runCLI(t, buildPackage, []string{"-o", bin, app}); code != 0 || !strings.Contains(out, "Built") {
		t.Fatalf("build: %d\n%s", code, out)
	}
	if code := exitCode(t, exec.Command(bin).Run()); code != 42 {
		t.Fatalf("built executable exit = %d, want 42", code)
	}
	if code, out := runCLI(t, runPackage, []string{app}); code != 42 {
		t.Fatalf("run: %d\n%s", code, out)
	}
	// The archive's bytes are part of the cache identity: a changed library
	// yields a different executable, not the cached one.
	archiveFixture(t, app, "int oak_cli_hello(int x) { return x + 3; }\n")
	if code, out := runCLI(t, runPackage, []string{app}); code != 43 {
		t.Fatalf("run after relinking: %d\n%s", code, out)
	}
	// A missing archive fails the build naming the directive, before any C
	// compiler runs.
	if err := os.Remove(filepath.Join(app, "native", "libhello.a")); err != nil {
		t.Fatal(err)
	}
	if code, out := runCLI(t, buildPackage, []string{"-o", bin, app}); code == 0 || !strings.Contains(out, "OAK-M0112") || !strings.Contains(out, "link native/libhello.a") {
		t.Fatalf("missing archive: %d\n%s", code, out)
	}
}

func exitCode(t *testing.T, err error) int {
	t.Helper()
	if err == nil {
		return 0
	}
	var exitErr *exec.ExitError
	if errors.As(err, &exitErr) {
		return exitErr.ExitCode()
	}
	t.Fatalf("run failed: %v", err)
	return 0
}
