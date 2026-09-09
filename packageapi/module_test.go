package packageapi

import "testing"

func TestCompareModulesTakesTheMaximumOverPackages(t *testing.T) {
	previous := ModuleSnapshot{Module: "example.com/m", Version: "1.2.0", Packages: map[string]Snapshot{
		"example.com/m/a": {Package: "example.com/m/a", Exports: map[string]Export{"f": {Kind: "function", Type: "fn() -> u32"}}},
		"example.com/m/b": {Package: "example.com/m/b", Exports: map[string]Export{"g": {Kind: "function", Type: "fn() -> u32"}}},
	}}
	current := ModuleSnapshot{Module: "example.com/m", Version: "1.3.0", Packages: map[string]Snapshot{
		"example.com/m/a": {Package: "example.com/m/a", Exports: map[string]Export{"f": {Kind: "function", Type: "fn() -> u32"}, "h": {Kind: "function", Type: "fn() -> u8"}}},
		"example.com/m/b": {Package: "example.com/m/b", Exports: map[string]Export{"g": {Kind: "function", Type: "fn() -> u32"}}},
		"example.com/m/c": {Package: "example.com/m/c", Exports: map[string]Export{}},
	}}
	report, err := EnforceModule(previous, current)
	if err != nil || report.Required != Minor {
		t.Fatalf("additive change: %v %+v", err, report)
	}
	current.Version = "2.0.0"
	if _, err := EnforceModule(previous, current); err == nil {
		t.Fatal("over-versioning must be rejected")
	}
	delete(current.Packages, "example.com/m/b")
	required, report, err := RequiredVersion(previous, current)
	if err != nil || report.Required != Major || required != (Version{Major: 2}) {
		t.Fatalf("removal must be major: %v %+v %v", err, report, required)
	}
	if !SameAPI(previous, previous) || SameAPI(previous, current) {
		t.Fatal("SameAPI broken")
	}
}
