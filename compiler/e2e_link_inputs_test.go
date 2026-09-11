package compiler

import (
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

// nativeArchive compiles one C source into a static archive at
// <root>/<rel> (docs/spec/83-modules.md section 4.6 links it through the
// manifest). Skips when the host has no C compiler or archiver.
func nativeArchive(t *testing.T, root, rel, csrc string) {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	ar, err := exec.LookPath("ar")
	if err != nil {
		t.Skip("no archiver on PATH")
	}
	dir := filepath.Join(root, filepath.Dir(filepath.FromSlash(rel)))
	if err := os.MkdirAll(dir, 0o755); err != nil {
		t.Fatal(err)
	}
	cPath := filepath.Join(dir, "native.c")
	if err := os.WriteFile(cPath, []byte(csrc), 0o644); err != nil {
		t.Fatal(err)
	}
	object := filepath.Join(dir, "native.o")
	if out, err := exec.Command(cc, "-std=c99", "-O1", "-c", "-o", object, cPath).CombinedOutput(); err != nil {
		t.Fatalf("cc -c: %v\n%s", err, out)
	}
	if out, err := exec.Command(ar, "rcs", filepath.Join(root, filepath.FromSlash(rel)), object).CombinedOutput(); err != nil {
		t.Fatalf("ar: %v\n%s", err, out)
	}
}

// buildLinkedAndRun compiles a package to C and links it with the manifests'
// native inputs the way `oak build` does (argv, no shell), then runs it.
func buildLinkedAndRun(t *testing.T, comp Compilation) int {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	inputs, err := comp.LinkInputs()
	if err != nil {
		t.Fatalf("link inputs: %v", err)
	}
	dir := t.TempDir()
	cPath := filepath.Join(dir, "program.c")
	if err := os.WriteFile(cPath, []byte(output), 0o644); err != nil {
		t.Fatal(err)
	}
	binary := filepath.Join(dir, "program")
	args := []string{"-std=c99", "-O1", "-o", binary, cPath}
	for _, input := range inputs {
		switch input.Kind {
		case "object":
			args = append(args, input.Path)
		case "framework":
			if runtime.GOOS == "darwin" {
				args = append(args, "-framework", input.Path)
			}
		}
	}
	if out, err := exec.Command(cc, args...).CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s\n--- C ---\n%s", err, out, output)
	}
	err = exec.Command(binary).Run()
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

const linkedHelloC = "int oak_e2_hello(int x) { return x + 2; }\n"

// A module links a static archive from its manifest; the extern it declares
// resolves against that archive when the emitted C is compiled.
func TestE2ELinkArchiveFromManifest(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/linked\nlink native/libhello.a\n",
		"main.oak": `package main

hello: (x: c.Int): c.Int = c.extern("oak_e2_hello")

main: (): i32 {
  answer: c.Int = hello(c.Int(40))
  i32(answer)
}
`,
	})
	nativeArchive(t, root, "native/libhello.a", linkedHelloC)
	comp := New().WithPackageDir(root)
	inputs, err := comp.LinkInputs()
	if err != nil {
		t.Fatal(err)
	}
	if len(inputs) != 1 || inputs[0].Kind != "object" || inputs[0].Module != "example.com/linked" || !strings.HasSuffix(inputs[0].Path, filepath.FromSlash("native/libhello.a")) || !filepath.IsAbs(inputs[0].Path) {
		t.Fatalf("inputs = %+v", inputs)
	}
	if code := buildLinkedAndRun(t, comp); code != 42 {
		t.Fatalf("exit = %d, want 42", code)
	}
}

// A dependency module's `link` and `framework` lines join the build when
// the root reaches its packages: the root's inputs come first, then each
// dependency's in module-path order, objects before frameworks within a
// module.
func TestE2ELinkInputsFromDependencyInOrder(t *testing.T) {
	dep := writeModule(t, map[string]string{
		"oak.mod": "module example.com/dep\nlink native/libdep.a\nframework Foundation\n",
		"ops/ops.oak": `package ops

dep_twice: (x: c.Int): c.Int = c.extern("oak_e2_dep_twice")

pub twice: (x: i32): i32 {
  doubled: c.Int = dep_twice(c.Int(x))
  i32(doubled)
}
`,
	})
	nativeArchive(t, dep, "native/libdep.a", "int oak_e2_dep_twice(int x) { return 2 * x; }\n")
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/app\nrequire example.com/dep 1.0.0\nreplace example.com/dep => " + dep + "\nlink native/libhello.a\n",
		"main.oak": `package main

import("example.com/dep/ops")

hello: (x: c.Int): c.Int = c.extern("oak_e2_hello")

main: (): i32 {
  base: c.Int = hello(c.Int(19))
  ops.twice(i32(base))
}
`,
	})
	nativeArchive(t, root, "native/libhello.a", linkedHelloC)
	comp := New().WithPackageDir(root)
	inputs, err := comp.LinkInputs()
	if err != nil {
		t.Fatal(err)
	}
	if len(inputs) != 3 {
		t.Fatalf("inputs = %+v", inputs)
	}
	if inputs[0].Module != "example.com/app" || inputs[0].Kind != "object" || !strings.HasSuffix(inputs[0].Path, "libhello.a") {
		t.Fatalf("root first: %+v", inputs[0])
	}
	if inputs[1].Module != "example.com/dep" || inputs[1].Kind != "object" || !strings.HasSuffix(inputs[1].Path, "libdep.a") {
		t.Fatalf("dependency object second: %+v", inputs[1])
	}
	if inputs[2].Module != "example.com/dep" || inputs[2].Kind != "framework" || inputs[2].Path != "Foundation" {
		t.Fatalf("dependency framework last: %+v", inputs[2])
	}
	if code := buildLinkedAndRun(t, comp); code != 42 {
		t.Fatalf("exit = %d, want 42", code)
	}
}

// A `link` operand that leaves the module — by `..`, by an absolute path,
// or by a symlink — and a `link` that names a missing file fail the
// manifest (OAK-M0112) with a message naming the directive.
func TestE2ELinkInputsFailClosed(t *testing.T) {
	program := "package main\n\nmain: (): i32 = 42\n"
	for name, manifest := range map[string]string{
		"parent":   "module example.com/x\nlink ../escape.a\n",
		"absolute": "module example.com/x\nlink /tmp/escape.a\n",
		"missing":  "module example.com/x\nlink native/missing.a\n",
	} {
		root := writeModule(t, map[string]string{"oak.mod": manifest, "main.oak": program})
		_, err := New().WithPackageDir(root).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), CodeManifest) || !strings.Contains(err.Error(), "link ") {
			t.Fatalf("%s: expected an OAK-M0112 naming the link directive, got %v", name, err)
		}
	}
	// A symlink inside the module that resolves outside it is refused even
	// though its manifest path is well-formed.
	outside := t.TempDir()
	nativeArchive(t, outside, "libout.a", "int oak_e2_out(void) { return 1; }\n")
	root := writeModule(t, map[string]string{"oak.mod": "module example.com/x\nlink native/libout.a\n", "main.oak": program})
	if err := os.MkdirAll(filepath.Join(root, "native"), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.Symlink(filepath.Join(outside, "libout.a"), filepath.Join(root, "native", "libout.a")); err != nil {
		t.Skipf("symlinks unavailable: %v", err)
	}
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "resolves outside the module root") {
		t.Fatalf("symlink escape: %v", err)
	}
}

// A package outside any module has no link inputs, and a module without
// link lines has none either.
func TestE2ELinkInputsAbsent(t *testing.T) {
	inputs, err := New().WithSource("plain.oak", "main: (): i32 = 42\n").LinkInputs()
	if err != nil || len(inputs) != 0 {
		t.Fatalf("single source: %v %v", inputs, err)
	}
	root := writeModule(t, map[string]string{"oak.mod": "module example.com/plain\n", "main.oak": "package main\n\nmain: (): i32 = 42\n"})
	inputs, err = New().WithPackageDir(root).LinkInputs()
	if err != nil || len(inputs) != 0 {
		t.Fatalf("module without links: %v %v", inputs, err)
	}
}
