package main

import (
	"bytes"
	"io"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/modules"
)

func writeTree(t *testing.T, files map[string]string) string {
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

// run invokes `oak mod` with args, capturing stdout and stderr.
func run(t *testing.T, args ...string) (int, string) {
	t.Helper()
	savedOut, savedErr := os.Stdout, os.Stderr
	reader, writer, err := os.Pipe()
	if err != nil {
		t.Fatal(err)
	}
	os.Stdout, os.Stderr = writer, writer
	done := make(chan string)
	go func() {
		var buf bytes.Buffer
		_, _ = io.Copy(&buf, reader)
		done <- buf.String()
	}()
	code := modCommand(args)
	writer.Close()
	os.Stdout, os.Stderr = savedOut, savedErr
	return code, <-done
}

const libV1 = "package geometry\n\npub(opaque) Point: type = struct { x: i32, y: i32 }\npub make: (x: i32, y: i32): Point = Point { x: x, y: y }\npub sum: (p: Point): i32 = p.x + p.y\n"

func TestModCommandsEndToEnd(t *testing.T) {
	lib := writeTree(t, map[string]string{"oak.mod": "module example.com/lib\nversion 1.0.0\n", "geometry/point.oak": libV1})
	app := writeTree(t, map[string]string{
		"oak.mod":  "module example.com/app\nrequire example.com/lib 1.0.0\nreplace example.com/lib => " + lib + "\n",
		"main.oak": "package main\n\ngeo: { Point: type, make: (i32, i32) -> Point, sum: (Point) -> i32 } = import(\"example.com/lib/geometry\")\n\nmain: (): i32 = geo.sum(geo.make(20, 22))\n",
	})
	work := t.TempDir()
	v1 := filepath.Join(work, "v1.json")

	if code, _ := run(t, "nonsense"); code != 2 {
		t.Fatalf("unknown subcommand exit = %d", code)
	}
	code, out := run(t, "api", lib)
	if code != 0 || !strings.Contains(out, `"example.com/lib/geometry"`) {
		t.Fatalf("api: %d\n%s", code, out)
	}
	if err := os.WriteFile(v1, []byte(out), 0o644); err != nil {
		t.Fatal(err)
	}
	// Add an export: minor.
	if err := os.WriteFile(filepath.Join(lib, "geometry", "point.oak"), []byte(libV1+"pub zero: (): Point = make(0, 0)\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "diff", v1, lib); code != 0 || !strings.Contains(out, "required version: 1.1.0") {
		t.Fatalf("diff: %d\n%s", code, out)
	}
	if code, out := run(t, "bump", v1, lib); code != 1 || !strings.Contains(out, "requires version 1.1.0") {
		t.Fatalf("bump with the old version must fail: %d\n%s", code, out)
	}
	if err := os.WriteFile(filepath.Join(lib, "oak.mod"), []byte("module example.com/lib\nversion 1.1.0\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "bump", v1, lib); code != 0 || !strings.Contains(out, "exact required bump") {
		t.Fatalf("bump: %d\n%s", code, out)
	}
	code, out = run(t, "api", lib)
	if code != 0 {
		t.Fatalf("api v1.1: %s", out)
	}
	v11 := filepath.Join(work, "v11.json")
	if err := os.WriteFile(v11, []byte(out), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "compat", v11, app); code != 0 || !strings.Contains(out, "satisfied") {
		t.Fatalf("compat: %d\n%s", code, out)
	}
	archive := filepath.Join(work, "lib.tar.gz")
	if code, out := run(t, "pack", "-previous", v1, "-o", archive, "-url", "https://example.com/lib-1.1.0.tar.gz", lib); code != 0 || !strings.Contains(out, "require example.com/lib 1.1.0 https://example.com/lib-1.1.0.tar.gz sha256:") {
		t.Fatalf("pack: %d\n%s", code, out)
	}
	if code, _ := run(t, "pack", "-url", "http://example.com/x.tar.gz", lib); code != 1 {
		t.Fatalf("pack must refuse a non-HTTPS location: %d", code)
	}
	// A breaking 2.0.0 snapshot: upgrade picks 1.1.0, compat rejects 2.0.0.
	v2 := filepath.Join(work, "v2.json")
	broken := strings.Replace(out, "", "", 1)
	_ = broken
	text, _ := os.ReadFile(v11)
	twoText := strings.ReplaceAll(strings.ReplaceAll(string(text), `"1.1.0"`, `"2.0.0"`), `"fn(Point)->i32"`, `"fn(Point)->i64"`)
	if err := os.WriteFile(v2, []byte(twoText), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "compat", v2, app); code != 1 || !strings.Contains(out, "incompatible") {
		t.Fatalf("compat 2.0.0: %d\n%s", code, out)
	}
	if code, out := run(t, "upgrade", "-dir", app, v2, v1, v11); code != 0 || !strings.Contains(out, "require example.com/lib 1.1.0") {
		t.Fatalf("upgrade: %d\n%s", code, out)
	}
	// try: the current lib builds; a breaking candidate does not.
	if code, out := run(t, "try", "-dir", app, "example.com/lib", lib); code != 0 || !strings.Contains(out, "compatible") {
		t.Fatalf("try: %d\n%s", code, out)
	}
	breaking := writeTree(t, map[string]string{"oak.mod": "module example.com/lib\nversion 2.0.0\n", "geometry/point.oak": strings.Replace(libV1, "pub sum: (p: Point): i32 = p.x + p.y", "pub sum: (p: Point): i64 = i64(p.x + p.y)", 1)})
	if code, out := run(t, "try", "-dir", app, "example.com/lib", breaking); code != 1 || !strings.Contains(out, "incompatible") {
		t.Fatalf("try breaking: %d\n%s", code, out)
	}
	// tidy: clean module, then a stale require.
	if code, out := run(t, "tidy", app); code != 0 || !strings.Contains(out, "is tidy") {
		t.Fatalf("tidy clean: %d\n%s", code, out)
	}
	manifest, _ := os.ReadFile(filepath.Join(app, "oak.mod"))
	if err := os.WriteFile(filepath.Join(app, "oak.mod"), append(manifest, []byte("require example.com/stale 1.0.0\n")...), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "tidy", app); code != 1 || !strings.Contains(out, "unused: require example.com/stale") {
		t.Fatalf("tidy report: %d\n%s", code, out)
	}
	if code, out := run(t, "tidy", "-w", app); code != 0 || !strings.Contains(out, "rewrote") {
		t.Fatalf("tidy -w: %d\n%s", code, out)
	}
	after, _ := os.ReadFile(filepath.Join(app, "oak.mod"))
	if string(after) != string(manifest) {
		t.Fatalf("tidy -w must restore the manifest exactly:\n%s", after)
	}
}

// The former oak-api and oak-semver tools: single-package snapshots and
// diffs between two snapshot files.
func TestModAPIPackageAndSnapshotFileDiff(t *testing.T) {
	lib := writeTree(t, map[string]string{"oak.mod": "module example.com/lib\nversion 1.0.0\n", "geometry/point.oak": libV1})
	work := t.TempDir()
	code, out := run(t, "api", "-package", "example.com/lib/geometry", "-version", "1.0.0", filepath.Join(lib, "geometry"))
	if code != 0 || !strings.Contains(out, `"package": "example.com/lib/geometry"`) || strings.Contains(out, `"packages"`) {
		t.Fatalf("api -package: %d\n%s", code, out)
	}
	prev := filepath.Join(work, "prev.json")
	if err := os.WriteFile(prev, []byte(out), 0o644); err != nil {
		t.Fatal(err)
	}
	// A single source file, no module at all.
	single := filepath.Join(work, "net.oak")
	if err := os.WriteFile(single, []byte("pub twice: (v: i32): i32 = v * 2\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "api", "-package", "example/net", "-version", "0.1.0", single); code != 0 || !strings.Contains(out, `"twice"`) {
		t.Fatalf("api -package on a file: %d\n%s", code, out)
	}
	// Add an export, snapshot at 1.1.0, and enforce between the two files.
	if err := os.WriteFile(filepath.Join(lib, "geometry", "point.oak"), []byte(libV1+"pub zero: (): Point = make(0, 0)\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	code, out = run(t, "api", "-package", "example.com/lib/geometry", "-version", "1.1.0", filepath.Join(lib, "geometry"))
	if code != 0 {
		t.Fatal(out)
	}
	current := filepath.Join(work, "current.json")
	if err := os.WriteFile(current, []byte(out), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "diff", prev, current); code != 0 || !strings.Contains(out, "zero: public export added (minor)") {
		t.Fatalf("diff files: %d\n%s", code, out)
	}
	if code, out := run(t, "bump", prev, current); code != 0 || !strings.Contains(out, "version 1.1.0 is the exact required bump") {
		t.Fatalf("bump files: %d\n%s", code, out)
	}
	wrong := strings.Replace(out, "", "", 1)
	_ = wrong
	text, _ := os.ReadFile(current)
	if err := os.WriteFile(current, []byte(strings.ReplaceAll(string(text), `"1.1.0"`, `"2.0.0"`)), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "bump", prev, current); code != 1 || !strings.Contains(out, "requires version 1.1.0; declared 2.0.0") {
		t.Fatalf("bump over-versioned: %d\n%s", code, out)
	}
}

// Round A of go-tool parity: dispatcher-level commands.
func TestCLIParityCommands(t *testing.T) {
	// help / version / env
	if code, out := runCLI(t, helpCommand, nil); code != 0 || !strings.Contains(out, "oak <command> [arguments]") || !strings.Contains(out, "install") {
		t.Fatalf("help: %d\n%s", code, out)
	}
	if code, out := runCLI(t, helpCommand, []string{"mod"}); code != 0 || !strings.Contains(out, "graph [dir]") {
		t.Fatalf("help mod: %d\n%s", code, out)
	}
	if code, out := runCLI(t, versionCommand, nil); code != 0 || !strings.HasPrefix(out, "oak version ") {
		t.Fatalf("version: %d\n%s", code, out)
	}
	t.Setenv("OAKMODCACHE", "/tmp/oak-cache-test")
	if code, out := runCLI(t, envCommand, []string{"OAKMODCACHE"}); code != 0 || strings.TrimSpace(out) != "/tmp/oak-cache-test" {
		t.Fatalf("env NAME: %d\n%s", code, out)
	}
	if code, out := runCLI(t, envCommand, nil); code != 0 || !strings.Contains(out, `OAKMODCACHE="/tmp/oak-cache-test"`) || !strings.Contains(out, "OAKBIN=") {
		t.Fatalf("env: %d\n%s", code, out)
	}

	// A module with a dependency, for list, vet, why, graph, edit, init.
	lib := writeTree(t, map[string]string{"oak.mod": "module example.com/lib\nversion 1.0.0\n", "geometry/point.oak": libV1})
	app := writeTree(t, map[string]string{
		"oak.mod":       "module example.com/app\nrequire example.com/lib 1.0.0\nreplace example.com/lib => " + lib + "\n",
		"main.oak":      "package main\n\ngeo := import(\"example.com/lib/geometry\")\nu := import(\"example.com/app/util\")\n\nmain: (): i32 = geo.sum(geo.make(20, 22)) + u.zero()\n",
		"util/util.oak": "package util\n\npub zero: (): i32 = { i: u32 = 0\n  running: Bool = true\n  while running { i = i + 1\n    running = i < 3 }\n  0 }\n",
	})
	code, out := runCLI(t, listPackages, []string{app})
	if code != 0 || !strings.Contains(out, "example.com/app\n\texample.com/app/util\n\texample.com/lib/geometry") || strings.Contains(out, "example.com/lib/geometry\n") && strings.HasPrefix(out, "example.com/lib") {
		t.Fatalf("list: %d\n%s", code, out)
	}
	code, out = runCLI(t, listPackages, []string{"-json", "-deps", app})
	if code != 0 || !strings.Contains(out, `"path": "example.com/lib/geometry"`) || !strings.Contains(out, `"module": "example.com/lib"`) {
		t.Fatalf("list -json -deps: %d\n%s", code, out)
	}
	code, out = runCLI(t, vetPackage, []string{filepath.Join(app, "util")})
	if code != 0 || !strings.Contains(out, "OAK-D0103") || !strings.Contains(out, "1 recorded assumption") {
		t.Fatalf("vet: %d\n%s", code, out)
	}
	if code, out := runCLI(t, vetPackage, []string{filepath.Join(lib, "geometry")}); code != 0 || !strings.Contains(out, "no recorded assumptions") {
		t.Fatalf("vet clean: %d\n%s", code, out)
	}
	code, out = run(t, "why", "example.com/lib/geometry", app)
	if code != 0 || !strings.Contains(out, "# example.com/app\nexample.com/app\nexample.com/lib/geometry") {
		t.Fatalf("why: %d\n%s", code, out)
	}
	if code, out := run(t, "why", "example.com/absent", app); code != 1 || !strings.Contains(out, "no package of example.com/app imports") {
		t.Fatalf("why absent: %d\n%s", code, out)
	}
	if code, out := run(t, "graph", app); code != 0 || strings.TrimSpace(out) != "example.com/app example.com/lib@1.0.0" {
		t.Fatalf("graph: %d\n%s", code, out)
	}
	// edit: require, replace, version, profile; then drops.
	if code, out := run(t, "edit", "-require", "example.com/extra@2.1.0", "-version", "0.3.0", "-profile", "strict", app); code != 0 || !strings.Contains(out, "rewrote") {
		t.Fatalf("edit: %d\n%s", code, out)
	}
	text, _ := os.ReadFile(filepath.Join(app, "oak.mod"))
	for _, want := range []string{"require example.com/extra 2.1.0", "version 0.3.0", "profile strict", "require example.com/lib 1.0.0"} {
		if !strings.Contains(string(text), want) {
			t.Fatalf("edit missing %q:\n%s", want, text)
		}
	}
	if code, out := run(t, "edit", "-require", "example.com/lib@1.2.0", "-droprequire", "example.com/extra", "-version", "0.4.0", app); code != 0 {
		t.Fatalf("edit 2: %d\n%s", code, out)
	}
	text, _ = os.ReadFile(filepath.Join(app, "oak.mod"))
	if strings.Contains(string(text), "extra") || !strings.Contains(string(text), "require example.com/lib 1.2.0") || strings.Count(string(text), "version ") != 1 || !strings.Contains(string(text), "version 0.4.0") {
		t.Fatalf("edit 2 result:\n%s", text)
	}
	if code, _ := run(t, "edit", "-require", "example.com/lib@nonsense", app); code != 1 {
		t.Fatalf("edit must reject a bad version: %d", code)
	}
	if code, _ := run(t, "edit", "-replace", "example.com/nowhere=>../x", app); code != 1 {
		t.Fatal("edit must refuse a manifest that does not parse (replace without require)")
	}
	// init: creates once, refuses twice, rejects library paths.
	fresh := t.TempDir()
	if code, out := run(t, "init", "example.com/new", fresh); code != 0 || !strings.Contains(out, "created") {
		t.Fatalf("init: %d\n%s", code, out)
	}
	if code, _ := run(t, "init", "example.com/new", fresh); code != 1 {
		t.Fatal("init must not overwrite")
	}
	if code, _ := run(t, "init", "strings", t.TempDir()); code != 1 {
		t.Fatal("init must reject a standard-library path")
	}
	// clean: refuses an unset cache, removes an explicit one.
	t.Setenv("OAKMODCACHE", "")
	if code, _ := runCLI(t, cleanCommand, []string{"-modcache"}); code != 1 {
		t.Fatal("clean must refuse without OAKMODCACHE")
	}
	cache := t.TempDir()
	if err := os.MkdirAll(filepath.Join(cache, "example.com", "dep@v1.0.0"), 0o755); err != nil {
		t.Fatal(err)
	}
	t.Setenv("OAKMODCACHE", cache)
	if code, out := runCLI(t, cleanCommand, []string{"-modcache"}); code != 0 || !strings.Contains(out, "removed 1 entry") {
		t.Fatalf("clean: %d\n%s", code, out)
	}
	if entries, _ := os.ReadDir(cache); len(entries) != 0 {
		t.Fatal("clean must empty the cache directory")
	}
	// build: executable by default, C with -o x.c, from a single file too.
	// (The edit above made the module strict, which rejects util's loop;
	// go back to the default profile first.)
	if code, _ := run(t, "edit", "-profile", "default", app); code != 0 {
		t.Fatal("edit -profile default")
	}
	if _, err := exec.LookPath("cc"); err == nil {
		bin := filepath.Join(t.TempDir(), "app")
		if code, out := runCLI(t, buildPackage, []string{"-o", bin, app}); code != 0 || !strings.Contains(out, "Built") {
			t.Fatalf("build binary: %d\n%s", code, out)
		}
		if info, err := os.Stat(bin); err != nil || info.Mode()&0o111 == 0 {
			t.Fatalf("build must produce an executable: %v", err)
		}
		t.Setenv("OAKBIN", filepath.Join(t.TempDir(), "bin"))
		if code, out := runCLI(t, installPackage, []string{app}); code != 0 || !strings.Contains(out, "installed") {
			t.Fatalf("install: %d\n%s", code, out)
		}
		// Named after the module (the root package is the clause-less main).
		if _, err := os.Stat(filepath.Join(os.Getenv("OAKBIN"), "app")); err != nil {
			t.Fatalf("install target missing: %v", err)
		}
	}
	cfile := filepath.Join(t.TempDir(), "app.c")
	if code, out := runCLI(t, buildPackage, []string{"-o", cfile, app}); code != 0 || !strings.Contains(out, "Built") {
		t.Fatalf("build -o x.c: %d\n%s", code, out)
	}
	if text, err := os.ReadFile(cfile); err != nil || !strings.Contains(string(text), "int main") {
		t.Fatalf("build -o x.c must write C: %v", err)
	}
	single := filepath.Join(t.TempDir(), "one.oak")
	if err := os.WriteFile(single, []byte("main: (): i32 = 42\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := runCLI(t, buildPackage, []string{"-emit-c", "-o", filepath.Join(filepath.Dir(single), "one.c"), single}); code != 0 {
		t.Fatalf("build file: %d\n%s", code, out)
	}
}

// runCLI invokes a top-level command function capturing its output.
func runCLI(t *testing.T, fn func([]string) int, args []string) (int, string) {
	t.Helper()
	savedOut, savedErr := os.Stdout, os.Stderr
	reader, writer, err := os.Pipe()
	if err != nil {
		t.Fatal(err)
	}
	os.Stdout, os.Stderr = writer, writer
	done := make(chan string)
	go func() {
		var buf bytes.Buffer
		_, _ = io.Copy(&buf, reader)
		done <- buf.String()
	}()
	code := fn(args)
	writer.Close()
	os.Stdout, os.Stderr = savedOut, savedErr
	return code, <-done
}

// Round B: doc, fmt, mod vendor, mod verify.
func TestCLIParityRoundB(t *testing.T) {
	lib := writeTree(t, map[string]string{"oak.mod": "module example.com/lib\nversion 1.0.0\n", "geometry/point.oak": libV1, "geometry/.hidden.oak": "package geometry\n", "geometry/notes.txt": "x"})
	app := writeTree(t, map[string]string{
		"oak.mod":  "module example.com/app\nrequire example.com/lib 1.0.0\nreplace example.com/lib => " + lib + "\n",
		"main.oak": "package main\n\ngeo := import(\"example.com/lib/geometry\")\n\nmain: (): i32 = geo.sum(geo.make(20, 22))\n",
	})
	// doc: module listing, name filter, opaque rendering, -package form.
	code, out := runCLI(t, docCommand, []string{lib})
	if code != 0 || !strings.Contains(out, "package example.com/lib/geometry") || !strings.Contains(out, "pub(opaque) Point: type") || !strings.Contains(out, "pub sum: fn(Point)->i32") {
		t.Fatalf("doc: %d\n%s", code, out)
	}
	if code, out := runCLI(t, docCommand, []string{lib, "make"}); code != 0 || strings.Contains(out, "sum") || !strings.Contains(out, "pub make: fn(i32,i32)->Point") {
		t.Fatalf("doc name: %d\n%s", code, out)
	}
	if code, _ := runCLI(t, docCommand, []string{lib, "absent"}); code != 1 {
		t.Fatal("doc must fail for an unknown name")
	}
	if code, out := runCLI(t, docCommand, []string{"-package", "example.com/lib/geometry", filepath.Join(lib, "geometry")}); code != 0 || !strings.Contains(out, "pub make") {
		t.Fatalf("doc -package: %d\n%s", code, out)
	}
	// fmt: whitespace canonicalized only when the tree is unchanged.
	messy := filepath.Join(t.TempDir(), "messy.oak")
	if err := os.WriteFile(messy, []byte("package main\r\n\r\n\r\n\r\nmain: (): i32 = 42   \r\n\r\n\r\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := runCLI(t, fmtCommand, []string{"-l", messy}); code != 0 || strings.TrimSpace(out) != messy {
		t.Fatalf("fmt -l: %d\n%s", code, out)
	}
	if code, out := runCLI(t, fmtCommand, []string{messy}); code != 0 || out != "package main\n\nmain: (): i32 = 42\n" {
		t.Fatalf("fmt stdout: %d\n%q", code, out)
	}
	if code, _ := runCLI(t, fmtCommand, []string{"-w", messy}); code != 0 {
		t.Fatal("fmt -w")
	}
	if text, _ := os.ReadFile(messy); string(text) != "package main\n\nmain: (): i32 = 42\n" {
		t.Fatalf("fmt -w result %q", text)
	}
	if code, out := runCLI(t, fmtCommand, []string{"-l", messy}); code != 0 || strings.TrimSpace(out) != "" {
		t.Fatalf("fmt -l on a formatted file must list nothing: %d\n%s", code, out)
	}
	broken := filepath.Join(t.TempDir(), "broken.oak")
	if err := os.WriteFile(broken, []byte("main: (): i32 = ((( 1 +   \n\n\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := runCLI(t, fmtCommand, []string{"-w", broken}); code != 1 || !strings.Contains(out, "left alone") {
		t.Fatalf("fmt must not rewrite a file that does not parse: %d\n%s", code, out)
	}
	// vendor: the app builds from vendor/ with no replace and no cache.
	if code, out := run(t, "vendor", app); code != 0 || !strings.Contains(out, "vendored example.com/lib 1.0.0 (2 files)") {
		t.Fatalf("vendor: %d\n%s", code, out)
	}
	if _, err := os.Stat(filepath.Join(app, "vendor", "example.com", "lib", "geometry", "point.oak")); err != nil {
		t.Fatalf("vendored source missing: %v", err)
	}
	for _, absent := range []string{filepath.Join(app, "vendor", "example.com", "lib", "geometry", ".hidden.oak"), filepath.Join(app, "vendor", "example.com", "lib", "geometry", "notes.txt")} {
		if _, err := os.Stat(absent); !os.IsNotExist(err) {
			t.Fatalf("%s must not be vendored", absent)
		}
	}
	list, _ := os.ReadFile(filepath.Join(app, "vendor", "modules.txt"))
	if strings.TrimSpace(string(list)) != "# example.com/lib 1.0.0" {
		t.Fatalf("modules.txt = %q", list)
	}
	if err := os.WriteFile(filepath.Join(app, "oak.mod"), []byte("module example.com/app\nrequire example.com/lib 1.0.0\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	t.Setenv("OAKMODCACHE", "")
	if code, out := runCLI(t, vetPackage, []string{app}); code != 0 {
		t.Fatalf("build from vendor: %d\n%s", code, out)
	}
	if code, out := runCLI(t, listPackages, []string{"-deps", app}); code != 0 || !strings.Contains(out, "example.com/lib/geometry") {
		t.Fatalf("list from vendor: %d\n%s", code, out)
	}
	// verify: unset cache refused; a recorded entry verifies; an edit is caught.
	if code, _ := run(t, "verify", app); code != 1 {
		t.Fatal("verify must refuse without OAKMODCACHE")
	}
	cache := t.TempDir()
	entry := filepath.Join(cache, "example.com", "lib@v1.0.0")
	if err := os.MkdirAll(filepath.Join(entry, "geometry"), 0o755); err != nil {
		t.Fatal(err)
	}
	for name, text := range map[string]string{"oak.mod": "module example.com/lib\nversion 1.0.0\n", "geometry/point.oak": libV1} {
		if err := os.WriteFile(filepath.Join(entry, name), []byte(text), 0o644); err != nil {
			t.Fatal(err)
		}
	}
	t.Setenv("OAKMODCACHE", cache)
	if code, out := run(t, "verify", app); code != 1 || !strings.Contains(out, "unrecorded") {
		t.Fatalf("verify unrecorded: %d\n%s", code, out)
	}
	if err := modules.WriteRecord(entry, "sha256:0"); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "verify", app); code != 0 || !strings.Contains(out, "all 1 cached module(s) verified") {
		t.Fatalf("verify ok: %d\n%s", code, out)
	}
	if err := os.WriteFile(filepath.Join(entry, "geometry", "point.oak"), []byte(libV1+"// edited\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := run(t, "verify", app); code != 1 || !strings.Contains(out, "modified") {
		t.Fatalf("verify modified: %d\n%s", code, out)
	}
}

// Round C: patterns, uniform -h, program arguments after --, completion.
func TestCLIParityRoundC(t *testing.T) {
	lib := writeTree(t, map[string]string{"oak.mod": "module example.com/lib\nversion 1.0.0\n", "geometry/point.oak": libV1})
	app := writeTree(t, map[string]string{
		"oak.mod":       "module example.com/app\nrequire example.com/lib 1.0.0\nreplace example.com/lib => " + lib + "\n",
		"main.oak":      "package main\n\ngeo := import(\"example.com/lib/geometry\")\n\nmain: (): i32 = geo.sum(geo.make(20, 22))\n",
		"util/util.oak": "package util\n\npub zero: (): i32 = 0\n",
	})
	// Patterns expand through the module's packages.
	dirs, err := expandPackagePatterns([]string{filepath.Join(app, "...")})
	if err != nil || len(dirs) != 2 {
		t.Fatalf("expand = %v %v", dirs, err)
	}
	if code, out := runCLI(t, vetPackage, []string{filepath.Join(app, "...")}); code != 0 || strings.Count(out, "no recorded assumptions") != 2 {
		t.Fatalf("vet pattern: %d\n%s", code, out)
	}
	if code, out := runCLI(t, listPackages, []string{filepath.Join(app, "util", "...")}); code != 0 || !strings.Contains(out, "example.com/app/util") || strings.Contains(out, "example.com/app\n") {
		t.Fatalf("list pattern: %d\n%s", code, out)
	}
	if code, out := runCLI(t, buildPackage, []string{"-emit-c", filepath.Join(app, "...")}); code != 0 || strings.Count(out, "Built") != 2 {
		t.Fatalf("build pattern: %d\n%s", code, out)
	}
	for _, name := range []string{"app.c", "util.c"} {
		os.Remove(name)
	}
	if code, _ := runCLI(t, buildPackage, []string{"-o", "x", filepath.Join(app, "...")}); code != 2 {
		t.Fatal("build must refuse -o with several packages")
	}
	// -h on every flag-bearing command prints usage and exits 0.
	for _, c := range []struct {
		fn   func([]string) int
		want string
	}{
		{buildPackage, "usage: oak build"}, {runPackage, "usage: oak run"}, {installPackage, "usage: oak install"},
		{vetPackage, "usage: oak vet"}, {listPackages, "usage: oak list"}, {docCommand, "usage: oak doc"},
		{fmtCommand, "usage: oak fmt"}, {cleanCommand, "usage: oak clean"}, {modTidy, "usage: oak mod tidy"},
		{modEdit, "usage: oak mod edit"}, {modPack, "usage: oak mod pack"}, {modAPI, "usage: oak mod api"},
		{modUpgrade, "usage: oak mod upgrade"}, {modTry, "usage: oak mod try"},
	} {
		if code, out := runCLI(t, c.fn, []string{"-h"}); code != 0 || !strings.Contains(out, c.want) {
			t.Fatalf("-h for %s: %d\n%s", c.want, code, out)
		}
	}
	if code, out := runCLI(t, vetPackage, []string{"-bogus"}); code != 2 || !strings.Contains(out, "run 'oak vet -h'") {
		t.Fatalf("unknown flag: %d\n%s", code, out)
	}
	// Program arguments after -- reach the program (the build must still
	// succeed and the exit status propagate).
	if _, err := exec.LookPath("cc"); err == nil {
		if code, _ := runCLI(t, runPackage, []string{app, "--", "alpha", "-beta"}); code != 42 {
			t.Fatalf("run with program arguments exit = %d", code)
		}
	}
	own, program := splitProgramArgs([]string{"-profile", "strict", "dir", "--", "-x", "y"})
	if len(own) != 3 || len(program) != 2 || program[0] != "-x" {
		t.Fatalf("split = %v %v", own, program)
	}
	// Completion scripts name every command and mod subcommand.
	for _, shell := range []string{"bash", "zsh", "fish"} {
		code, out := runCLI(t, completionCommand, []string{shell})
		if code != 0 || !strings.Contains(out, "vendor") || !strings.Contains(out, "install") {
			t.Fatalf("completion %s: %d\n%s", shell, code, out)
		}
	}
	if code, _ := runCLI(t, completionCommand, []string{"tcsh"}); code != 2 {
		t.Fatal("completion must reject an unknown shell")
	}
}

// Round D: the build cache.
func TestBuildCache(t *testing.T) {
	if _, err := exec.LookPath("cc"); err != nil {
		t.Skip("no C compiler")
	}
	t.Setenv("OAKCACHE", t.TempDir())
	app := writeTree(t, map[string]string{"oak.mod": "module example.com/app\n", "main.oak": "package main\n\nmain: (): i32 = 42\n"})
	bin := filepath.Join(t.TempDir(), "app")
	code, out := runCLI(t, buildPackage, []string{"-o", bin, app})
	if code != 0 || strings.Contains(out, "(cached)") {
		t.Fatalf("first build: %d\n%s", code, out)
	}
	if code, out := runCLI(t, buildPackage, []string{"-o", bin + "2", app}); code != 0 || !strings.Contains(out, "(cached)") {
		t.Fatalf("second build must hit the cache: %d\n%s", code, out)
	}
	if info, err := os.Stat(bin + "2"); err != nil || info.Mode()&0o111 == 0 {
		t.Fatalf("cached copy must be executable: %v", err)
	}
	if code, _ := runCLI(t, runPackage, []string{app}); code != 42 {
		t.Fatalf("run from cache exit = %d", code)
	}
	// A source change is a miss.
	if err := os.WriteFile(filepath.Join(app, "main.oak"), []byte("package main\n\nmain: (): i32 = 41\n"), 0o644); err != nil {
		t.Fatal(err)
	}
	if code, out := runCLI(t, buildPackage, []string{"-o", bin + "3", app}); code != 0 || strings.Contains(out, "(cached)") {
		t.Fatalf("changed source must miss: %d\n%s", code, out)
	}
	if code, out := runCLI(t, cleanCommand, []string{"-cache"}); code != 0 || !strings.Contains(out, "removed build cache") {
		t.Fatalf("clean -cache: %d\n%s", code, out)
	}
	if code, out := runCLI(t, buildPackage, []string{"-o", bin + "4", app}); code != 0 || strings.Contains(out, "(cached)") {
		t.Fatalf("after clean the build must miss: %d\n%s", code, out)
	}
	t.Setenv("OAKCACHE", "off")
	if code, out := runCLI(t, buildPackage, []string{"-o", bin + "5", app}); code != 0 || strings.Contains(out, "(cached)") {
		t.Fatalf("disabled cache must miss: %d\n%s", code, out)
	}
	if code, out := runCLI(t, envCommand, []string{"OAKCACHE"}); code != 0 || strings.TrimSpace(out) != "off" {
		t.Fatalf("env OAKCACHE: %d\n%s", code, out)
	}
}
