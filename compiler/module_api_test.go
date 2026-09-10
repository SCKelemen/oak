package compiler

import (
	"context"
	"encoding/json"
	"net/http"
	"net/http/httptest"
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
)

const semverManifest = "module example.com/lib\noak 0.1.0\nversion 1.0.0\n"

// A module snapshot covers every package; opaque types contribute no
// definition or ABI, so their representation is patch-level.
func TestModuleAPISnapshotAndOpaqueTypes(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": semverManifest,
		"geometry/point.oak": `package geometry

pub(opaque) Point: type = struct { x: i32, y: i32 }
pub Shape: type = Dot | Line: i32
pub make: (x: i32, y: i32): Point = Point { x: x, y: y }
hidden: (v: i32): i32 = v
`,
		"util/util.oak": "package util\n\npub twice: (v: i32): i32 = v * 2\n",
	})
	before, err := ModuleAPISnapshot(root, "1.0.0")
	if err != nil {
		t.Fatal(err)
	}
	if before.Module != "example.com/lib" || len(before.Packages) != 2 {
		t.Fatalf("snapshot = %+v", before)
	}
	geometry := before.Packages["example.com/lib/geometry"]
	if geometry.Exports["Point"].Kind != "opaque type" || geometry.Exports["Point"].ABI != "" || geometry.Exports["Point"].Type != "opaque" {
		t.Fatalf("opaque export = %+v", geometry.Exports["Point"])
	}
	if _, leaked := geometry.Exports["hidden"]; leaked {
		t.Fatal("private declaration leaked into the snapshot")
	}

	// Changing the opaque representation is a patch; adding a variant to a
	// transparent ADT is major; adding an export is minor.
	changed := writeModule(t, map[string]string{
		"oak.mod": semverManifest,
		"geometry/point.oak": `package geometry

pub(opaque) Point: type = struct { x: i64, y: i64, tag: u8 }
pub Shape: type = Dot | Line: i32
pub make: (x: i32, y: i32): Point = Point { x: i64(x), y: i64(y), tag: 0 }
`,
		"util/util.oak": "package util\n\npub twice: (v: i32): i32 = v * 2\npub thrice: (v: i32): i32 = v * 3\n",
	})
	after, err := ModuleAPISnapshot(changed, "1.1.0")
	if err != nil {
		t.Fatal(err)
	}
	report, err := packageapi.EnforceModule(before, after)
	if err != nil || report.Required != packageapi.Minor {
		t.Fatalf("opaque representation change + added export must be minor: %v %+v", err, report)
	}
	broken := writeModule(t, map[string]string{
		"oak.mod":            semverManifest,
		"geometry/point.oak": "package geometry\n\npub(opaque) Point: type = struct { x: i32, y: i32 }\npub Shape: type = Dot | Line: i32 | Arc: u8\npub make: (x: i32, y: i32): Point = Point { x: x, y: y }\n",
		"util/util.oak":      "package util\n\npub twice: (v: i32): i32 = v * 2\n",
	})
	major, err := ModuleAPISnapshot(broken, "2.0.0")
	if err != nil {
		t.Fatal(err)
	}
	if _, err := packageapi.EnforceModule(before, major); err != nil {
		t.Fatalf("variant addition to a transparent ADT must be an exact major bump: %v", err)
	}
	required, _, err := packageapi.RequiredVersion(before, major)
	if err != nil || required != (packageapi.Version{Major: 2}) {
		t.Fatalf("required = %v %v", required, err)
	}
}

// Sealed compatibility: a client's sealed signatures are checked against a
// dependency snapshot without the dependency's source.
func TestCheckSealedCompatibility(t *testing.T) {
	dep := writeModule(t, map[string]string{
		"oak.mod": "module example.com/dep\nversion 1.0.0\n",
		"fnv/fnv.oak": `package fnv

pub Key: type = struct { bits: u64 }
pub key: (v: u64): Key = Key { bits: v }
pub hash: (k: Key): u64 = k.bits * 3
pub extra: (k: Key): u64 = k.bits
`,
	})
	client := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\nrequire example.com/dep 1.0.0\nreplace example.com/dep => " + dep + "\n",
		"main.oak": "package main\n\nh: { Key: type, key: (u64) -> Key, hash: (Key) -> u64 } = import(\"example.com/dep/fnv\")\n\nmain: (): i32 = {\n  k: h.Key = h.key(2)\n  h.hash(k) == 6 ? 42 | 1\n}\n",
	})
	current, err := ModuleAPISnapshot(dep, "1.0.0")
	if err != nil {
		t.Fatal(err)
	}
	problems, err := CheckSealedCompatibility(client, current)
	if err != nil || len(problems) != 0 {
		t.Fatalf("current version must satisfy the sealed import: %v %+v", err, problems)
	}
	// A hypothetical next version drops extra (unused by the client: fine)
	// and changes hash's type (breaks the client).
	next := current
	next.Version = "2.0.0"
	fnv := next.Packages["example.com/dep/fnv"]
	exports := map[string]packageapi.Export{}
	for name, export := range fnv.Exports {
		if name != "extra" {
			exports[name] = export
		}
	}
	exports["hash"] = packageapi.Export{Kind: "function", Type: "fn(Key)->u32"}
	fnv.Exports = exports
	next.Packages = map[string]packageapi.Snapshot{"example.com/dep/fnv": fnv}
	problems, err = CheckSealedCompatibility(client, next)
	if err != nil || len(problems) != 1 || problems[0].Member != "hash" {
		t.Fatalf("changed hash must be the only incompatibility: %v %+v", err, problems)
	}
}

// An archive-carried api.json must be honest: it names the required version
// and matches the API the source exposes.
func TestVerifyArchiveAPI(t *testing.T) {
	files := map[string]string{
		"oak.mod":       "module example.com/dep\nversion 1.0.0\n",
		"math/math.oak": "package math\n\npub square: (v: i32): i32 = v * v\n",
	}
	honest := writeModule(t, files)
	if err := VerifyArchiveAPI(honest, packageapi.Version{Major: 1}); err != nil {
		t.Fatalf("an archive without api.json is accepted: %v", err)
	}
	snapshot, err := ModuleAPISnapshot(honest, "1.0.0")
	if err != nil {
		t.Fatal(err)
	}
	write := func(dir string, snapshot packageapi.ModuleSnapshot) {
		data, err := json.Marshal(snapshot)
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(filepath.Join(dir, "api.json"), data, 0o644); err != nil {
			t.Fatal(err)
		}
	}
	write(honest, snapshot)
	if err := VerifyArchiveAPI(honest, packageapi.Version{Major: 1}); err != nil {
		t.Fatalf("honest api.json rejected: %v", err)
	}
	if err := VerifyArchiveAPI(honest, packageapi.Version{Major: 1, Minor: 1}); err == nil || !strings.Contains(err.Error(), "declares version") {
		t.Fatalf("version mismatch must be rejected: %v", err)
	}
	// The source claims one API, the carried snapshot another.
	dishonest := writeModule(t, map[string]string{
		"oak.mod":       files["oak.mod"],
		"math/math.oak": "package math\n\npub square: (v: i32): i64 = i64(v) * i64(v)\n",
	})
	write(dishonest, snapshot)
	if err := VerifyArchiveAPI(dishonest, packageapi.Version{Major: 1}); err == nil || !strings.Contains(err.Error(), "does not match") {
		t.Fatalf("dishonest api.json must be rejected: %v", err)
	}
	if err := os.WriteFile(filepath.Join(dishonest, "api.json"), []byte("{"), 0o644); err != nil {
		t.Fatal(err)
	}
	if err := VerifyArchiveAPI(dishonest, packageapi.Version{Major: 1}); err == nil {
		t.Fatal("malformed api.json must be rejected")
	}
}

// Pack produces exactly what download consumes: the archive round-trips
// through the fetcher with the honesty check on, is deterministic, and a
// dishonest api.json inside it is refused before installation.
func TestPackRoundTripsThroughDownload(t *testing.T) {
	dep := writeModule(t, map[string]string{
		"oak.mod":       "module example.com/dep\nversion 1.2.0\n",
		"math/math.oak": "package math\n\npub square: (v: i32): i32 = v * v\n",
		".hidden/x.oak": "package hidden\n",
	})
	snapshot, err := ModuleAPISnapshot(dep, "1.2.0")
	if err != nil {
		t.Fatal(err)
	}
	api, _ := json.Marshal(snapshot)
	archive, digest, err := modules.Pack(dep, "dep-1.2.0", api)
	if err != nil {
		t.Fatal(err)
	}
	again, digestAgain, err := modules.Pack(dep, "dep-1.2.0", api)
	if err != nil || digest != digestAgain || string(archive) != string(again) {
		t.Fatalf("pack is not deterministic: %v %s %s", err, digest, digestAgain)
	}
	serveArchive := func(data []byte) *httptest.Server {
		server := httptest.NewTLSServer(http.HandlerFunc(func(w http.ResponseWriter, r *http.Request) { _, _ = w.Write(data) }))
		t.Cleanup(server.Close)
		return server
	}
	server := serveArchive(archive)
	cache := t.TempDir()
	fetcher := &modules.Fetcher{Client: server.Client(), Cache: cache, Verify: VerifyArchiveAPI}
	manifest := modules.Manifest{Path: "example.com/app", Requires: []modules.Requirement{{
		Path: "example.com/dep", Version: packageapi.Version{Major: 1, Minor: 2},
		Location: server.URL + "/dep-1.2.0.tar.gz", Digest: digest,
	}}}
	if err := fetcher.Download(context.Background(), manifest); err != nil {
		t.Fatalf("honest archive rejected: %v", err)
	}
	installed := modules.CacheDir(cache, "example.com/dep", packageapi.Version{Major: 1, Minor: 2})
	if _, err := os.Stat(filepath.Join(installed, "math", "math.oak")); err != nil {
		t.Fatalf("source not installed: %v", err)
	}
	if _, err := os.Stat(filepath.Join(installed, ".hidden")); !os.IsNotExist(err) {
		t.Fatal("hidden entries must not be packed")
	}
	if _, err := os.Stat(filepath.Join(installed, modules.APIFile)); err != nil {
		t.Fatal("api.json must travel with the archive")
	}
	// The installed module still resolves as a dependency.
	app := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\nrequire example.com/dep 1.2.0\n",
		"main.oak": "package main\n\nm := import(\"example.com/dep/math\")\n\nmain: (): i32 = m.square(6) + 6\n",
	})
	if got, crashed := buildPackageAndRun(t, New().WithPackageDir(app).WithModuleCache(cache)); crashed || got != 42 {
		t.Fatalf("program exited %d", got)
	}
	// A dishonest api.json (claims an export the source lacks) is refused.
	lying := snapshot
	lying.Packages = map[string]packageapi.Snapshot{"example.com/dep/math": {Package: "example.com/dep/math", Version: "1.2.0", Exports: map[string]packageapi.Export{
		"square": snapshot.Packages["example.com/dep/math"].Exports["square"],
		"cube":   {Kind: "function", Type: "fn(i32)->i32"},
	}}}
	lyingAPI, _ := json.Marshal(lying)
	bad, badDigest, err := modules.Pack(dep, "dep-1.2.0", lyingAPI)
	if err != nil {
		t.Fatal(err)
	}
	badServer := serveArchive(bad)
	badFetcher := &modules.Fetcher{Client: badServer.Client(), Cache: t.TempDir(), Verify: VerifyArchiveAPI}
	manifest.Requires[0].Location, manifest.Requires[0].Digest = badServer.URL+"/dep.tar.gz", badDigest
	if err := badFetcher.Download(context.Background(), manifest); err == nil || !strings.Contains(err.Error(), "does not match") {
		t.Fatalf("dishonest archive must be refused: %v", err)
	}
}

// Upgrade selection: the highest candidate that satisfies every sealed import.
func TestHighestCompatible(t *testing.T) {
	dep := writeModule(t, map[string]string{
		"oak.mod":     "module example.com/dep\nversion 1.0.0\n",
		"fnv/fnv.oak": "package fnv\n\npub Key: type = struct { bits: u64 }\npub key: (v: u64): Key = Key { bits: v }\npub hash: (k: Key): u64 = k.bits\n",
	})
	client := writeModule(t, map[string]string{
		"oak.mod":  "module example.com/app\nrequire example.com/dep 1.0.0\nreplace example.com/dep => " + dep + "\n",
		"main.oak": "package main\n\nh: { Key: type, key: (u64) -> Key, hash: (Key) -> u64 } = import(\"example.com/dep/fnv\")\n\nmain: (): i32 = h.hash(h.key(2)) == 2 ? 42 | 1\n",
	})
	v1, err := ModuleAPISnapshot(dep, "1.0.0")
	if err != nil {
		t.Fatal(err)
	}
	v11 := v1
	v11.Version = "1.1.0"
	v2 := v1
	v2.Version = "2.0.0"
	v2.Packages = map[string]packageapi.Snapshot{"example.com/dep/fnv": {Package: "example.com/dep/fnv", Version: "2.0.0", Exports: map[string]packageapi.Export{
		"Key":  v1.Packages["example.com/dep/fnv"].Exports["Key"],
		"key":  v1.Packages["example.com/dep/fnv"].Exports["key"],
		"hash": {Kind: "function", Type: "fn(Key)->u32"},
	}}}
	best, results, err := HighestCompatible(client, []packageapi.ModuleSnapshot{v2, v1, v11})
	if err != nil || best == nil || best.Version != "1.1.0" {
		t.Fatalf("best = %v %v", best, err)
	}
	if len(results) != 3 || results[0].Version.Minor != 0 || len(results[2].Problems) != 1 {
		t.Fatalf("results = %+v", results)
	}
	other := v1
	other.Module = "example.com/other"
	if _, _, err := HighestCompatible(client, []packageapi.ModuleSnapshot{v1, other}); err == nil {
		t.Fatal("candidates for different modules must be rejected")
	}
}

// Nested modules are packages of the module: each is snapshotted under its
// own path, spelled as a directory package would spell itself.
func TestModuleAPISnapshotCoversNestedModules(t *testing.T) {
	root := writeModule(t, map[string]string{
		"oak.mod": semverManifest,
		"util/util.oak": `package util

module inner {
  pub(opaque) Box: type = struct { v: i32 }
  pub box: (v: i32): Box = Box { v: v }
  pub open_box: (b: Box): i32 = b.v
  hidden: (v: i32): i32 = v
}

pub quad: (v: i32): i32 = inner.open_box(inner.box(v)) * 4
pub wrap: (v: i32): inner.Box = inner.box(v)
`,
	})
	snapshot, err := ModuleAPISnapshot(root, "1.0.0")
	if err != nil {
		t.Fatal(err)
	}
	inner, ok := snapshot.Packages["example.com/lib/util/inner"]
	if !ok {
		t.Fatalf("nested module missing from the snapshot: %v", snapshot.Packages)
	}
	if inner.Exports["Box"].Kind != "opaque type" || inner.Exports["box"].Type != "fn(i32)->Box" || inner.Exports["open_box"].Type != "fn(Box)->i32" {
		t.Fatalf("nested exports = %+v", inner.Exports)
	}
	if _, leaked := inner.Exports["hidden"]; leaked {
		t.Fatal("private nested member leaked")
	}
	util := snapshot.Packages["example.com/lib/util"]
	if util.Exports["wrap"].Type != "fn(i32)->example.com/lib/util/inner.Box" {
		t.Fatalf("enclosing package must spell the nested type by path: %+v", util.Exports["wrap"])
	}
	// Removing a nested export is a breaking change of the module.
	changed := writeModule(t, map[string]string{
		"oak.mod":       semverManifest,
		"util/util.oak": "package util\n\nmodule inner {\n  pub(opaque) Box: type = struct { v: i32 }\n  pub box: (v: i32): Box = Box { v: v }\n}\n\npub quad: (v: i32): i32 = v * 4\n",
	})
	after, err := ModuleAPISnapshot(changed, "2.0.0")
	if err != nil {
		t.Fatal(err)
	}
	if _, err := packageapi.EnforceModule(snapshot, after); err != nil {
		t.Fatalf("dropping a nested export must be an exact major bump: %v", err)
	}
	if _, err := New().WithPackageName("example.com/lib/util").WithPackageDir(filepath.Join(root, "util")).APISnapshot("1.0.0").Get(); err == nil {
		t.Fatal("a single-package snapshot of a package with nested modules must still fail closed")
	}
}
