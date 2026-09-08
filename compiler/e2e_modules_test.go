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
