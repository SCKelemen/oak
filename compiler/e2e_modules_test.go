package compiler

// End-to-end tests for the module system (docs/spec/83-modules.md): real
// module directories with oak.mod, multi-package builds compiled through the
// C backend and executed, and the rejection rules with their stable codes.

import (
	"errors"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
)

// writeModule materializes files (relative paths) under a fresh module
// directory and returns its root.
func writeModule(t *testing.T, files map[string]string) string {
	t.Helper()
	root := t.TempDir()
	for name, text := range files {
		path := filepath.Join(root, filepath.FromSlash(name))
		if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	return root
}

// buildPackageAndRun compiles a package directory to C, compiles and runs it.
func buildPackageAndRun(t *testing.T, comp Compilation) (int, bool) {
	t.Helper()
	cc, err := exec.LookPath("cc")
	if err != nil {
		t.Skip("no C compiler on PATH")
	}
	output, err := comp.EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	dir := t.TempDir()
	cPath := filepath.Join(dir, "program.c")
	if err := os.WriteFile(cPath, []byte(output), 0o644); err != nil {
		t.Fatal(err)
	}
	binary := filepath.Join(dir, "program")
	build := exec.Command(cc, "-std=c99", "-O1", "-o", binary, cPath)
	if out, err := build.CombinedOutput(); err != nil {
		t.Fatalf("cc failed: %v\n%s\n--- C ---\n%s", err, out, output)
	}
	run := exec.Command(binary)
	err = run.Run()
	if err == nil {
		return 0, false
	}
	var exitErr *exec.ExitError
	if errors.As(err, &exitErr) {
		if exitErr.ExitCode() < 0 {
			return -1, true
		}
		return exitErr.ExitCode(), false
	}
	t.Fatalf("run failed: %v", err)
	return 0, false
}

// expectModuleError compiles a package directory and asserts the given code
// appears in the modules/typecheck rejection.
func expectModuleError(t *testing.T, root, pkg, code string) *DiagnosticError {
	t.Helper()
	_, err := New().WithPackageDir(filepath.Join(root, pkg)).EmitC().Get()
	if err == nil {
		t.Fatalf("expected %s, but the package compiled", code)
	}
	var diag *DiagnosticError
	if !errors.As(err, &diag) {
		t.Fatalf("expected a DiagnosticError carrying %s, got: %v", code, err)
	}
	for _, d := range diag.Diagnostics {
		if d.Code == code {
			if err := d.Validate(); err != nil {
				t.Fatalf("invalid diagnostic: %v", err)
			}
			return diag
		}
	}
	t.Fatalf("expected %s, got: %v", code, err)
	return nil
}

const helloManifest = "module example.com/hello\noak 0.1.0\n"

// A three-package program: geometry (opaque record + generic function),
// counter (mutable global through pub functions), main importing both.
func TestE2EModulesMultiPackageProgram(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"geometry/point.oak": `package geometry

pub(opaque) Point: type = struct { x: i32, y: i32 }

pub origin: (): Point = Point { x: 0, y: 0 }

pub make: (x: i32, y: i32): Point = Point { x: x, y: y }

pub manhattan: (p: Point): i32 = abs(p.x) + abs(p.y)

abs: (v: i32): i32 = v < 0 ? 0 - v | v

pub larger[T]: (a: T, b: T): T = a < b ? b | a
`,
		"geometry/shape.oak": `package geometry

pub Shape: type = Dot | Line: i32

pub length: (s: Shape): i32 = s ? .Dot => 0 | .Line(n) => n
`,
		"counter/counter.oak": `package counter

import("example.com/hello/geometry")

value: i32 = 0

pub bump: (by: i32): i32 = {
  value = value + by
  value
}

pub scaled_length: (s: geometry.Shape): i32 = geometry.length(s) * 2
`,
		"main.oak": `package main

geo := import("example.com/hello/geometry")
import("example.com/hello/counter")

main: (): i32 = {
  p: geo.Point = geo.make(-20, 15)
  a := geo.manhattan(p)
  b := counter.scaled_length(.Line(3))
  c := counter.bump(1)
  d := geo.larger[i32](a, 1)
  a + b + c + d - 35
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EModulesGeneratedCNamesAreDemanglable(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"util/util.oak": `package util

pub twice: (v: i32): i32 = v * 2
`,
		"main.oak": `package main

import("example.com/hello/util")

main: (): i32 = util.twice(21)
`,
	})
	output, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if !strings.Contains(output, "oak_example_dcom_shello_sutil__twice") {
		t.Fatalf("expected the mangled package function name in C output:\n%s", output)
	}
}

func TestE2EModulesUnexportedMemberRejected(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"util/util.oak": `package util

hidden: (v: i32): i32 = v
pub shown: (v: i32): i32 = hidden(v)
`,
		"main.oak": `package main

import("example.com/hello/util")

main: (): i32 = util.hidden(42)
`,
	})
	expectModuleError(t, root, ".", CodeMemberNotExported)
}

func TestE2EModulesNoSuchMemberRejected(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub shown: (v: i32): i32 = v\n",
		"main.oak":      "package main\n\nimport(\"example.com/hello/util\")\n\nmain: (): i32 = util.missing(42)\n",
	})
	expectModuleError(t, root, ".", CodeNoSuchMember)
}

func TestE2EModulesOpaqueProjectionRejected(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"geometry/point.oak": `package geometry

pub(opaque) Point: type = struct { x: i32, y: i32 }
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
`,
		"main.oak": `package main

import("example.com/hello/geometry")

main: (): i32 = {
  p := geometry.make(1, 2)
  p.x
}
`,
	})
	expectModuleError(t, root, ".", "OAK-M0110")
}

func TestE2EModulesOpaqueConstructionRejected(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"geometry/point.oak": `package geometry

pub(opaque) Point: type = struct { x: i32, y: i32 }
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
`,
		"main.oak": `package main

import("example.com/hello/geometry")

main: (): i32 = {
  p := geometry.Point { x: 1, y: 2 }
  1
}
`,
	})
	expectModuleError(t, root, ".", "OAK-M0110")
}

func TestE2EModulesImportCycleRejected(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  helloManifest,
		"a/a.oak":  "package a\n\nimport(\"example.com/hello/b\")\n\npub fa: (): i32 = b.fb()\n",
		"b/b.oak":  "package b\n\nimport(\"example.com/hello/a\")\n\npub fb: (): i32 = a.fa()\n",
		"main.oak": "package main\n\nimport(\"example.com/hello/a\")\n\nmain: (): i32 = a.fa()\n",
	})
	diag := expectModuleError(t, root, ".", CodeImportCycle)
	if !strings.Contains(diag.Error(), "example.com/hello/a -> example.com/hello/b -> example.com/hello/a") {
		t.Fatalf("cycle not named: %v", diag)
	}
}

func TestE2EModulesPackageClauseRules(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package utils\n\npub f: (): i32 = 1\n",
		"main.oak":      "package main\n\nimport(\"example.com/hello/util\")\n\nmain: (): i32 = util.f()\n",
	})
	expectModuleError(t, root, ".", CodePackageClause)

	root = writeModule(t, map[string]string{
		"oak.mod":  helloManifest,
		"u/a.oak":  "package u\n\npub f: (): i32 = 1\n",
		"u/b.oak":  "package v\n\npub g: (): i32 = 2\n",
		"main.oak": "package main\n\nimport(\"example.com/hello/u\")\n\nmain: (): i32 = u.f()\n",
	})
	expectModuleError(t, root, ".", CodePackageClause)

	// An imported package must declare its clause; the root may omit it
	// (single-file rule: package main).
	root = writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "pub f: (): i32 = 1\n",
		"main.oak":      "package main\n\nimport(\"example.com/hello/util\")\n\nmain: (): i32 = util.f()\n",
	})
	expectModuleError(t, root, ".", CodePackageClause)

	root = writeModule(t, map[string]string{
		"oak.mod":  helloManifest,
		"main.oak": "main: (): i32 = 42\n",
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("clause-less root: exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EModulesImportPathAndResolution(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":  helloManifest,
		"main.oak": "package main\n\nimport(\"example.com/hello/../etc\")\n\nmain: (): i32 = 42\n",
	})
	expectModuleError(t, root, ".", CodeImportPathInvalid)

	root = writeModule(t, map[string]string{
		"oak.mod":  helloManifest,
		"main.oak": "package main\n\nimport(\"example.com/hello/nowhere\")\n\nmain: (): i32 = nowhere.f()\n",
	})
	expectModuleError(t, root, ".", CodeImportUnresolvable)

	// Standard library views resolve their file's declarations; an
	// unknown member is a member error, an unknown library an import error.
	root = writeModule(t, map[string]string{
		"oak.mod":  helloManifest,
		"main.oak": "package main\n\nimport(\"strings\")\n\nmain: (): i32 = strings.f()\n",
	})
	expectModuleError(t, root, ".", CodeNoSuchMember)
	root = writeModule(t, map[string]string{
		"oak.mod":  helloManifest,
		"main.oak": "package main\n\nimport(\"encoding/utf8\")\n\nmain: (): i32 = utf8.f()\n",
	})
	expectModuleError(t, root, ".", CodeImportUnresolvable)

	// No module root: only bootstrap imports are legal.
	root = writeModule(t, map[string]string{
		"main.oak": "package main\n\nimport(\"example.com/other/pkg\")\n\nmain: (): i32 = pkg.f()\n",
	})
	expectModuleError(t, root, ".", CodeImportUnresolvable)
}

func TestE2EModulesAliasRules(t *testing.T) {
	// Unused import.
	root := writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub f: (): i32 = 1\n",
		"main.oak":      "package main\n\nimport(\"example.com/hello/util\")\n\nmain: (): i32 = 42\n",
	})
	expectModuleError(t, root, ".", CodeImportAlias)

	// Alias used as a value.
	root = writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub f: (): i32 = 1\n",
		"main.oak":      "package main\n\nimport(\"example.com/hello/util\")\n\nmain: (): i32 = {\n  x := util\n  util.f()\n}\n",
	})
	expectModuleError(t, root, ".", CodeImportAlias)

	// Alias collides with a declaration.
	root = writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub f: (): i32 = 1\n",
		"main.oak":      "package main\n\nimport(\"example.com/hello/util\")\n\nutil: (): i32 = 2\n\nmain: (): i32 = util.f()\n",
	})
	expectModuleError(t, root, ".", CodeImportAlias)

	// Reserved identifier.
	root = writeModule(t, map[string]string{
		"oak.mod":  helloManifest,
		"main.oak": "package main\n\nbad__name: (): i32 = 1\n\nmain: (): i32 = bad__name()\n",
	})
	expectModuleError(t, root, ".", CodeReservedIdentifier)

	// Imports after declarations.
	root = writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub f: (): i32 = 1\n",
		"main.oak":      "package main\n\nhelper: (): i32 = 2\n\nimport(\"example.com/hello/util\")\n\nmain: (): i32 = util.f()\n",
	})
	expectModuleError(t, root, ".", CodeImportPlacement)
}

// Sealing: a signature narrows the visible members and is checked exactly.
func TestE2EModulesSealedImport(t *testing.T) {
	files := map[string]string{
		"oak.mod": helloManifest,
		"fnv/fnv.oak": `package fnv

pub(opaque) Key: type = struct { bits: u64 }

pub key: (v: u64): Key = Key { bits: v }

pub hash: (k: Key): u64 = k.bits * 1099511628211

pub debug_bits: (k: Key): u64 = k.bits
`,
		"main.oak": `package main

h: { Key: type, key: (u64) -> Key, hash: (Key) -> u64 } = import("example.com/hello/fnv")

main: (): i32 = {
  k: h.Key = h.key(2)
  v: u64 = h.hash(k)
  v == 2199023256422 ? 42 | 1
}
`,
	}
	root := writeModule(t, files)
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}

	// A member outside the signature is unreachable through the sealed alias.
	files["main.oak"] = `package main

h: { Key: type, key: (u64) -> Key } = import("example.com/hello/fnv")

main: (): i32 = {
  k: h.Key = h.key(2)
  h.debug_bits(k) == 2 ? 42 | 1
}
`
	root = writeModule(t, files)
	expectModuleError(t, root, ".", CodeSignatureMismatch)

	// A signature member the package lacks.
	files["main.oak"] = `package main

h: { Key: type, key: (u64) -> Key, missing: (u64) -> Key } = import("example.com/hello/fnv")

main: (): i32 = {
  k: h.Key = h.key(2)
  42
}
`
	root = writeModule(t, files)
	expectModuleError(t, root, ".", CodeSignatureMismatch)

	// A signature member with the wrong type.
	files["main.oak"] = `package main

h: { Key: type, key: (u64) -> Key, hash: (Key) -> u32 } = import("example.com/hello/fnv")

main: (): i32 = {
  k: h.Key = h.key(2)
  42
}
`
	root = writeModule(t, files)
	expectModuleError(t, root, ".", "OAK-M0113")
}

// Dependencies: a required module located through a replace directive, with
// its own oak.mod and a nested package; the root's manifest selects it.
func TestE2EModulesRequireReplace(t *testing.T) {
	base := t.TempDir()
	dep := filepath.Join(base, "dep")
	app := filepath.Join(base, "app")
	for path, text := range map[string]string{
		"dep/oak.mod":       "module example.com/dep\noak 0.1.0\n",
		"dep/math/math.oak": "package math\n\npub square: (v: i32): i32 = v * v\n",
		"app/oak.mod":       "module example.com/app\noak 0.1.0\nrequire example.com/dep 1.0.0\nreplace example.com/dep => ../dep\n",
		"app/main.oak":      "package main\n\nimport(\"example.com/dep/math\")\n\nmain: (): i32 = math.square(6) + 6\n",
	} {
		full := filepath.Join(base, filepath.FromSlash(path))
		if err := os.MkdirAll(filepath.Dir(full), 0o755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(full, []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	_ = dep
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(app))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}

	// A required module with no replace and no cache fails closed.
	if err := os.WriteFile(filepath.Join(app, "oak.mod"), []byte("module example.com/app\nrequire example.com/dep 1.0.0\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	_, err := New().WithPackageDir(app).WithModuleCache(filepath.Join(base, "empty-cache")).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), CodeManifest) {
		t.Fatalf("expected %s, got %v", CodeManifest, err)
	}

	// The same module served from a module cache directory.
	cache := filepath.Join(base, "cache", "example.com", "dep@v1.0.0")
	if err := os.MkdirAll(filepath.Join(cache, "math"), 0o755); err != nil {
		t.Fatal(err)
	}
	for _, name := range []string{"oak.mod", "math/math.oak"} {
		data, err := os.ReadFile(filepath.Join(dep, filepath.FromSlash(name)))
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(cache, filepath.FromSlash(name)), data, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	code, abnormal = buildPackageAndRun(t, New().WithPackageDir(app).WithModuleCache(filepath.Join(base, "cache")))
	if abnormal || code != 42 {
		t.Fatalf("cache exit=(%d,%v)", code, abnormal)
	}
}

// Single-file compilation is unchanged: no package clause required, and the
// bootstrap import still works.
func TestE2EModulesSingleFileUnchanged(t *testing.T) {
	code, abnormal := buildAndRun(t, "single", "import(std)\n\nmain: (): i32 = 42\n")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// pub on the root package is accepted (it only affects the API snapshot).
func TestE2EModulesPubInRootPackage(t *testing.T) {
	code, abnormal := buildAndRun(t, "pubroot", "package main\n\npub Point: type = struct { x: i32 }\n\npub main: (): i32 = Point { x: 42 }.x\n")
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// The checked-in example module builds and runs.
func TestE2EModulesExampleDirectory(t *testing.T) {
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir("../examples/modules"))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Standard library package views: qualified access to a bootstrap file.
func TestE2EModulesStdlibView(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"main.oak": `package main

import("strings")

main: (): i32 = {
  upper := strings.ascii_upper(u8(97))
  lower := strings.ascii_lower(u8(65))
  upper == u8(65) && lower == u8(97) ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Type-qualified variant construction in call position, across packages and
// within one; and untyped locals initialized by record-returning calls.
func TestE2EModulesQualifiedVariantsAndInference(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"geometry/shape.oak": `package geometry

pub Shape: type = Dot | Line: i32
pub(opaque) Point: type = struct { x: i32, y: i32 }
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
pub sum: (p: Point): i32 = p.x + p.y
pub length: (s: Shape): i32 = s ? .Dot => 0 | .Line(n) => n
`,
		"main.oak": `package main

geo := import("example.com/hello/geometry")

Local: type = A | B: i32

pick: (v: Local): i32 = v ? .A => 1 | .B(n) => n

main: (): i32 = {
  p := geo.make(20, 15)
  line := geo.Shape.Line(4)
  dot := geo.Shape.Dot
  geo.sum(p) + geo.length(line) + geo.length(dot) + pick(Local.B(2)) + pick(Local.A)
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Named signatures: a shape declared in the root package and one exported by
// another package both seal an import; a sealed `Name: type` member is
// opaque for the importing package even though the package exported it
// transparently.
func TestE2EModulesNamedSignatureAndSealedOpacity(t *testing.T) {
	files := map[string]string{
		"oak.mod": helloManifest,
		"fnv/fnv.oak": `package fnv

pub Key: type = struct { bits: u64 }
pub key: (v: u64): Key = Key { bits: v }
pub hash: (k: Key): u64 = k.bits * 3
`,
		"hashing/hashing.oak": `package hashing

pub Hasher: type = { Key: type, key: (u64) -> Key, hash: (Key) -> u64 }
`,
		"main.oak": `package main

import("example.com/hello/hashing")
h: hashing.Hasher = import("example.com/hello/fnv")
l: Local = import("example.com/hello/fnv")

Local: type = { Key: type, key: (u64) -> Key }

main: (): i32 = {
  k: h.Key = h.key(14)
  m: l.Key = l.key(1)
  h.hash(k) == 42 ? 42 | 1
}
`,
	}
	root := writeModule(t, files)
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}

	// Key is transparent in fnv but sealed abstract here: no field access.
	files["main.oak"] = `package main

import("example.com/hello/hashing")

h: hashing.Hasher = import("example.com/hello/fnv")

main: (): i32 = {
  k: h.Key = h.key(14)
  k.bits == 14 ? 42 | 1
}
`
	root = writeModule(t, files)
	expectModuleError(t, root, ".", "OAK-M0110")
}

// Methods are declared with their receiver type.
func TestE2EModulesMethodOrphanRejected(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub Box: type = struct { v: i32 }\npub make: (v: i32): Box = Box { v: v }\n",
		"main.oak":      "package main\n\nimport(\"example.com/hello/util\")\n\nfn (b: util.Box) twice(): i32 = 2\n\nmain: (): i32 = util.make(1).twice()\n",
	})
	expectModuleError(t, root, ".", CodeMethodOrphan)
}

// Derived equality and hashing over records (nested) and ADTs, executed.
func TestE2EModulesDeriveEqualAndHash(t *testing.T) {
	src := `package main

Inner: type = struct { a: u8, flag: Bool }
Outer: type = struct { id: u32, inner: Inner }
Kind: type = Plain | Tagged: u16

outer_eq: (a: Outer, b: Outer): Bool = derive.equal
outer_hash: (v: Outer): u64 = derive.hash
kind_eq: (a: Kind, b: Kind): Bool = derive.equal
kind_hash: (v: Kind): u64 = derive.hash

main: (): i32 = {
  x := Outer { id: 7, inner: Inner { a: 1, flag: true } }
  y := Outer { id: 7, inner: Inner { a: 1, flag: true } }
  z := Outer { id: 7, inner: Inner { a: 2, flag: true } }
  w := Outer { id: 7, inner: Inner { a: 1, flag: false } }
  same := outer_eq(x, y) && !outer_eq(x, z) && !outer_eq(x, w)
  kinds := kind_eq(Kind.Plain, Kind.Plain) && kind_eq(Kind.Tagged(3), Kind.Tagged(3)) && !kind_eq(Kind.Plain, Kind.Tagged(1)) && !kind_eq(Kind.Tagged(1), Kind.Tagged(2))
  hashes := outer_hash(x) == outer_hash(y) && outer_hash(x) != outer_hash(z) && outer_hash(x) != outer_hash(w) && kind_hash(Kind.Plain) != kind_hash(Kind.Tagged(1))
  same && kinds && hashes ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "derive", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

func TestE2EModulesDeriveRules(t *testing.T) {
	// Orphan: deriving for another package's type.
	root := writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub Box: type = struct { v: i32 }\n",
		"main.oak":      "package main\n\nimport(\"example.com/hello/util\")\n\nbox_eq: (a: util.Box, b: util.Box): Bool = derive.equal\n\nmain: (): i32 = 42\n",
	})
	expectModuleError(t, root, ".", CodeDeriveOrphan)

	for name, src := range map[string]string{
		CodeDeriveUnknown:     "P: type = struct { v: i32 }\np_show: (v: P): u64 = derive.show\nmain: (): i32 = 42\n",
		CodeDeriveSignature:   "P: type = struct { v: i32 }\np_eq: (a: P, b: u32): Bool = derive.equal\nmain: (): i32 = 42\n",
		CodeDeriveUnsupported: "P: type = struct { v: []u8 }\np_hash: (v: P): u64 = derive.hash\nmain: (): i32 = 42\n",
	} {
		_, err := New().WithSource("derive.oak", src).EmitC().Get()
		if err == nil || !strings.Contains(err.Error(), name) {
			t.Fatalf("%s: got %v", name, err)
		}
	}
}

// Fresh abstract types: two sealed imports of one package yield distinct
// Key types; values cross only through each sealed alias; sharing
// (`Key: type = ...`) keeps a member transparent.
func TestE2EModulesFreshAbstractTypes(t *testing.T) {
	files := map[string]string{
		"oak.mod": helloManifest,
		"fnv/fnv.oak": `package fnv

pub Key: type = struct { bits: u64 }
pub key: (v: u64): Key = Key { bits: v }
pub hash: (k: Key): u64 = k.bits * 3
pub zero: Key = Key { bits: 0 }
`,
		"main.oak": `package main

h: { Key: type, key: (u64) -> Key, hash: (Key) -> u64, zero: Key } = import("example.com/hello/fnv")
g: { Key: type, key: (u64) -> Key, hash: (Key) -> u64 } = import("example.com/hello/fnv")
s: { Key: type = fnv.Key, key: (u64) -> Key } = import("example.com/hello/fnv")
import("example.com/hello/fnv")

main: (): i32 = {
  k: h.Key = h.key(14)
  z: h.Key = h.zero
  m: g.Key = g.key(14)
  shared: fnv.Key = s.key(1)
  h.hash(k) + h.hash(z) + g.hash(m) + fnv.hash(shared) == 87 ? 42 | 1
}
`,
	}
	root := writeModule(t, files)
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}

	// h.Key and g.Key are distinct: a value of one cannot cross the other's
	// boundary, nor be used where the underlying fnv.Key is expected.
	files["main.oak"] = `package main

h: { Key: type, key: (u64) -> Key, hash: (Key) -> u64 } = import("example.com/hello/fnv")
g: { Key: type, key: (u64) -> Key, hash: (Key) -> u64 } = import("example.com/hello/fnv")

main: (): i32 = {
  k: h.Key = h.key(14)
  g.hash(k) == 42 ? 42 | 1
}
`
	root = writeModule(t, files)
	expectModuleError(t, root, ".", "OAK-M0113")

	files["main.oak"] = `package main

h: { Key: type, key: (u64) -> Key } = import("example.com/hello/fnv")
import("example.com/hello/fnv")

main: (): i32 = {
  k: h.Key = h.key(14)
  fnv.hash(k) == 42 ? 42 | 1
}
`
	root = writeModule(t, files)
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil {
		t.Fatal("an abstract value must not be accepted as the underlying type")
	}

	// A shared type member must be the package's type exactly.
	files["main.oak"] = `package main

s: { Key: type = u64, key: (u64) -> Key } = import("example.com/hello/fnv")

main: (): i32 = {
  k: s.Key = s.key(1)
  42
}
`
	root = writeModule(t, files)
	expectModuleError(t, root, ".", "OAK-M0113")
}

// Generic packages: one template instantiated twice with different
// arguments, each instance a distinct package.
func TestE2EModulesGenericPackage(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"pair/pair.oak": `package pair[T, N: u32]

pub Pair: type = struct { first: T, second: T }
pub make: (a: T, b: T): Pair = Pair { first: a, second: b }
pub scaled_first: (p: Pair): T = p.first * T(N)
pub capacity: (): u32 = N
`,
		"main.oak": `package main

bytes := import("example.com/hello/pair")[u8, 3]
words := import("example.com/hello/pair")[u32, 10]

main: (): i32 = {
  b := bytes.make(u8(2), u8(1))
  w := words.make(u32(4), u32(1))
  total := u32(bytes.scaled_first(b)) + words.scaled_first(w) + bytes.capacity() + words.capacity()
  total == u32(59) ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}

	// Arity mismatches fail closed.
	for name, main := range map[string]string{
		"no arguments": "package main\n\nimport(\"example.com/hello/pair\")\n\nmain: (): i32 = pair.capacity()\n",
		"too many":     "package main\n\np := import(\"example.com/hello/pair\")[u8, 3, 4]\n\nmain: (): i32 = p.capacity()\n",
	} {
		root := writeModule(t, map[string]string{
			"oak.mod":       helloManifest,
			"pair/pair.oak": "package pair[T, N: u32]\n\npub capacity: (): u32 = N\n",
			"main.oak":      main,
		})
		diag := expectModuleError(t, root, ".", CodeGenericPackageArity)
		_ = name
		_ = diag
	}
	root = writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub f: (): i32 = 1\n",
		"main.oak":      "package main\n\nu := import(\"example.com/hello/util\")[u8]\n\nmain: (): i32 = u.f()\n",
	})
	expectModuleError(t, root, ".", CodeGenericPackageArity)
}

// Selective imports bind unqualified names through the visibility rule.
func TestE2EModulesSelectiveImport(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"util/util.oak": `package util

pub twice: (v: i32): i32 = v * 2
pub Box: type = struct { v: i32 }
pub boxed: (v: i32): Box = Box { v: v }
hidden: (v: i32): i32 = v
`,
		"main.oak": `package main

{ twice, Box, boxed } := import("example.com/hello/util")

open_box: (b: Box): i32 = b.v

main: (): i32 = {
  b := boxed(twice(10))
  open_box(b) + 22
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	root = writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub twice: (v: i32): i32 = v * 2\nhidden: (v: i32): i32 = v\n",
		"main.oak":      "package main\n\n{ hidden } := import(\"example.com/hello/util\")\n\nmain: (): i32 = hidden(42)\n",
	})
	expectModuleError(t, root, ".", CodeMemberNotExported)
	root = writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"util/util.oak": "package util\n\npub twice: (v: i32): i32 = v * 2\n",
		"main.oak":      "package main\n\n{ twice } := import(\"example.com/hello/util\")\n\nmain: (): i32 = 42\n",
	})
	expectModuleError(t, root, ".", CodeImportAlias)
}

// Diagnostics from checked code name the file they come from.
func TestE2EModulesDiagnosticsNameFiles(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod":            helloManifest,
		"geometry/point.oak": "package geometry\n\npub make: (x: i32): i32 = x\n",
		"geometry/bad.oak":   "package geometry\n\npub broken: (x: i32): i32 = x + true\n",
		"main.oak":           "package main\n\nimport(\"example.com/hello/geometry\")\n\nmain: (): i32 = geometry.make(42)\n",
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), "bad.oak:3:") {
		t.Fatalf("expected the diagnostic to name geometry/bad.oak with a position, got: %v", err)
	}
}

// derive.compare orders records lexicographically and ADTs by variant then
// payload.
func TestE2EModulesDeriveCompare(t *testing.T) {
	src := `package main

Ordering: type = Less | Equal | Greater

Version: type = struct { major: u32, minor: u32 }
Kind: type = Plain | Tagged: u16

version_cmp: (a: Version, b: Version): Ordering = derive.compare
kind_cmp: (a: Kind, b: Kind): Ordering = derive.compare

is_less: (o: Ordering): Bool = o ? .Less => true | .Equal => false | .Greater => false
is_equal: (o: Ordering): Bool = o ? .Less => false | .Equal => true | .Greater => false

main: (): i32 = {
  a := Version { major: 1, minor: 9 }
  b := Version { major: 2, minor: 0 }
  c := Version { major: 1, minor: 9 }
  ok := is_less(version_cmp(a, b)) && is_equal(version_cmp(a, c)) && !is_less(version_cmp(b, a))
  kinds := is_less(kind_cmp(Kind.Plain, Kind.Tagged(1))) && is_less(kind_cmp(Kind.Tagged(1), Kind.Tagged(2))) && is_equal(kind_cmp(Kind.Tagged(5), Kind.Tagged(5)))
  ok && kinds ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "derive_compare", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Standard library packages are real packages: importing one loads only it,
// its library dependencies, and the core prelude; mixing with the legacy
// flat prelude stays consistent.
func TestE2EModulesStdlibRealPackages(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"main.oak": `package main

import("json")
import("strings")

main: (): i32 = {
  upper := strings.ascii_upper(u8(97))
  bytes: [2]u8 = [2]u8{92, 110}
  esc: strings.TextScalar = json.json_escape(view(&bytes), 0)
  upper == u8(65) && esc.value == u32(10) ? 42 | 1
}
`,
	})
	output, err := New().WithPackageDir(root).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	if strings.Contains(output, "oak_hash_table_") || strings.Contains(output, "oak_filter_") {
		t.Fatalf("unrelated library packages were linked into a program importing json and strings")
	}
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}

	// The legacy flat prelude and a real package coexist and agree on the
	// prelude's core types.
	root = writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"main.oak": `package main

import(std)
import("strings")

main: (): i32 = strings.ascii_upper(u8(97)) == ascii_upper(u8(97)) ? 42 | 1
`,
	})
	code, abnormal = buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("mixed exit=(%d,%v)", code, abnormal)
	}
}

// A generic package's declared parameter contract is checked where it is
// instantiated.
func TestE2EModulesGenericPackageConstraint(t *testing.T) {
	files := map[string]string{
		"oak.mod": helloManifest,
		"pair/pair.oak": `package pair[T: Keyed]

pub Keyed: type = { key: u32 }
pub first_key: (v: T): u32 = v.key
`,
		"main.oak": `package main

items := import("example.com/hello/pair")[Item]

Item: type = struct { key: u32, weight: u8 }
Other: type = struct { weight: u8 }

main: (): i32 = items.first_key(Item { key: 42, weight: 1 }) == u32(42) ? 42 | 1
`,
	}
	root := writeModule(t, files)
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	files["main.oak"] = `package main

others := import("example.com/hello/pair")[Other]

Other: type = struct { weight: u8 }

main: (): i32 = others.first_key(Other { weight: 1 }) == u32(1) ? 42 | 1
`
	root = writeModule(t, files)
	expectModuleError(t, root, ".", "OAK-M0303")
}

// Library sugar on package spellings: derived codecs, text literals and
// fluent calls resolve to the imported packages' internal names, and a
// missing package fails closed naming the import to add.
func TestE2EModulesLibrarySugarOnPackages(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"main.oak": `package main

import("json")
import("strings")

Point: type = struct { x: u32, y: u32 }

main: (): i32 = {
  out: [64]u8
  dst: [*]u8 = span(&out)
  written: Result[u32, json.JsonError] = encode[Point, Json](Point { x: 4, y: 2 }, dst)
  b: strings.TextBuilder = strings.text_builder()
  b = b.append_text(dst, text_literal("ok"))
  json.json_result_ok(written) && json.json_result_value(written) == u32(13) && b.length == u32(2) ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	root = writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"main.oak": `package main

import("strings")

Point: type = struct { x: u32 }

main: (): i32 = {
  out: [64]u8
  dst: [*]u8 = span(&out)
  b: strings.TextBuilder = strings.text_builder()
  written: Result[u32, u8] = encode[Point, Json](Point { x: 4 }, dst)
  b.length == u32(0) ? 42 | 1
}
`,
	})
	_, err := New().WithPackageDir(root).EmitC().Get()
	if err == nil || !strings.Contains(err.Error(), `import("json")`) {
		t.Fatalf("expected a fail-closed hint to import json, got %v", err)
	}
}

// derive.format renders records and ADTs into a caller-owned span.
func TestE2EModulesDeriveFormat(t *testing.T) {
	src := `import(std)

Point: type = struct { x: i32, y: u8, on: Bool }
Shape: type = Dot | Line: i32 | At: Point

point_format: (v: Point, dst: [*]u8): Result[u32, TextError] = derive.format
shape_format: (v: Shape, dst: [*]u8): Result[u32, TextError] = derive.format

check: (dst: [*]u8, written: Result[u32, TextError], expected: []u8): Bool = {
  ok: Bool = text_result_ok(written) && text_result_value(written) == len(expected)
  i: u32 = 0
  while i < len(expected) && ok {
    ok = dst[i] == expected[i]
    i = i + 1
  }
  ok
}

main: (): i32 = {
  out: [96]u8
  dst: [*]u8 = span(&out)
  first: Bool = check(dst, point_format(Point { x: -3, y: 42, on: true }, dst), text_literal("Point { x: -3, y: 42, on: true }"))
  second: Bool = check(dst, shape_format(Shape.At(Point { x: 7, y: 1, on: false }), dst), text_literal("At(Point { x: 7, y: 1, on: false })"))
  third: Bool = check(dst, shape_format(Shape.Dot, dst), text_literal("Dot"))
  first && second && third ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "derive_format", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}

// Tag schemas are package-scoped: two packages declare a json schema, an
// importer names another package's schema as alias.schema, and codec
// derivation still finds the json schema under its internal name.
func TestE2EModulesPackageScopedTags(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": helloManifest,
		"wire/wire.oak": `package wire

pub json: tag = { name: string }
pub pb: tag = { field: u32 }
pub Header: type = struct { id(json: "header_id", pb: 1): u32 }
pub header_id: (h: Header): u32 = h.id
`,
		"main.oak": `package main

import("json")
import("example.com/hello/wire")

json_tag_local: tag = { name: string }
Point: type = struct { x(wire.json: "px"): u32, y(json_tag_local: "py"): u32 }

main: (): i32 = {
  out: [64]u8
  dst: [*]u8 = span(&out)
  written: Result[u32, json.JsonError] = encode[Point, Json](Point { x: 4, y: 2 }, dst)
  h := wire.Header { id: 40 }
  json.json_result_ok(written) && json.json_result_value(written) == u32(14) && wire.header_id(h) == u32(40) ? 42 | 1
}
`,
	})
	code, abnormal := buildPackageAndRun(t, New().WithPackageDir(root))
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	// A private tag schema of another package is not reachable.
	root = writeModule(t, map[string]string{
		"oak.mod":       helloManifest,
		"wire/wire.oak": "package wire\n\nsecret: tag = { name: string }\npub f: (): i32 = 1\n",
		"main.oak":      "package main\n\nimport(\"example.com/hello/wire\")\n\nP: type = struct { x(wire.secret: \"px\"): u32 }\n\nmain: (): i32 = wire.f()\n",
	})
	expectModuleError(t, root, ".", CodeMemberNotExported)
}

// Derivation over generic instantiations: the template's shape is
// substituted per instantiation and each instance gets its own helpers.
func TestE2EModulesDeriveOverInstantiations(t *testing.T) {
	src := `Pair[T]: type = struct { first: T, second: T }
Wrap[T]: type = Empty | Full: T

pair_eq: (a: Pair[u8], b: Pair[u8]): Bool = derive.equal
wide_eq: (a: Pair[u32], b: Pair[u32]): Bool = derive.equal
pair_hash: (v: Pair[u8]): u64 = derive.hash
wrap_eq: (a: Wrap[u16], b: Wrap[u16]): Bool = derive.equal

left: Pair[u8]
right: Pair[u8]
third: Pair[u8]
w: Pair[u32]

main: (): i32 = {
  left.first = u8(1)
  left.second = u8(2)
  right.first = u8(1)
  right.second = u8(2)
  third.first = u8(2)
  third.second = u8(2)
  w.first = u32(70000)
  w.second = u32(1)
  full: Wrap[u16] = .Full(5)
  other: Wrap[u16] = .Full(5)
  empty: Wrap[u16] = .Empty
  same := pair_eq(left, right) && !pair_eq(left, third) && wide_eq(w, w) && pair_hash(left) == pair_hash(right) && pair_hash(left) != pair_hash(third)
  wraps := wrap_eq(full, other) && !wrap_eq(empty, full)
  same && wraps ? 42 | 1
}
`
	code, abnormal := buildAndRun(t, "derive_generic", src)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
}
