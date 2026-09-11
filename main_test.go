package main

import (
	"bytes"
	"io"
	"os"
	"path/filepath"
	"strings"
	"testing"
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
	if code, out := run(t, "try", "example.com/lib", lib, "-dir", app); code != 0 || !strings.Contains(out, "compatible") {
		t.Fatalf("try: %d\n%s", code, out)
	}
	breaking := writeTree(t, map[string]string{"oak.mod": "module example.com/lib\nversion 2.0.0\n", "geometry/point.oak": strings.Replace(libV1, "pub sum: (p: Point): i32 = p.x + p.y", "pub sum: (p: Point): i64 = i64(p.x + p.y)", 1)})
	if code, out := run(t, "try", "example.com/lib", breaking, "-dir", app); code != 1 || !strings.Contains(out, "incompatible") {
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
