package compiler

import (
	"encoding/json"
	"os"
	"path/filepath"
	"strings"
	"testing"

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
