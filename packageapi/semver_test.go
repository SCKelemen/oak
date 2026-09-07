package packageapi

import (
	"strings"
	"testing"
)

func snap(version string, exports map[string]Export) Snapshot {
	return Snapshot{Package: "example/net", Version: version, Exports: exports}
}

func TestCompareClassifiesPublicChanges(t *testing.T) {
	base := snap("1.2.3", map[string]Export{
		"read": {Kind: "function", Type: "fn([]u8)->u32"},
		"Pair": {Kind: "struct", Type: "{a:u8,b:u8}", ABI: "size=2;align=1;a@0;b@1"},
	})
	tests := []struct {
		name string
		next Snapshot
		want ChangeLevel
	}{
		{"body-only", snap("1.2.4", base.Exports), Patch},
		{"addition", snap("1.3.0", map[string]Export{
			"read": base.Exports["read"], "Pair": base.Exports["Pair"],
			"write": {Kind: "function", Type: "fn([]u8)->u32"},
		}), Minor},
		{"removal", snap("2.0.0", map[string]Export{"read": base.Exports["read"]}), Major},
		{"semantic type", snap("2.0.0", map[string]Export{
			"read": {Kind: "function", Type: "fn([*]u8)->u32"}, "Pair": base.Exports["Pair"],
		}), Major},
		{"layout", snap("2.0.0", map[string]Export{
			"read": base.Exports["read"],
			"Pair": {Kind: "struct", Type: "{a:u8,b:u8}", ABI: "size=2;align=1;b@0;a@1"},
		}), Major},
	}
	for _, tt := range tests {
		t.Run(tt.name, func(t *testing.T) {
			if got := Compare(base, tt.next).Required; got != tt.want {
				t.Fatalf("level = %s, want %s", got, tt.want)
			}
		})
	}
}

func TestEnforceRequiresExactAutomaticBump(t *testing.T) {
	old := snap("1.2.3", map[string]Export{"read": {Kind: "function", Type: "fn()->u8"}})
	added := snap("1.3.0", map[string]Export{
		"read": old.Exports["read"],
		"write": {Kind: "function", Type: "fn(u8)->()"},
	})
	if _, err := Enforce(old, added); err != nil {
		t.Fatal(err)
	}
	added.Version = "1.2.4"
	if _, err := Enforce(old, added); err == nil || !strings.Contains(err.Error(), "requires version 1.3.0") {
		t.Fatalf("wanted required-version diagnostic, got %v", err)
	}
}

func TestPreOneBreakingChangeAdvancesMinor(t *testing.T) {
	old := snap("0.4.2", map[string]Export{"read": {Kind: "function", Type: "fn()->u8"}})
	next := snap("0.5.0", map[string]Export{})
	if _, err := Enforce(old, next); err != nil {
		t.Fatal(err)
	}
}

func TestVersionParserRejectsNonCanonicalVersions(t *testing.T) {
	for _, input := range []string{"1.2", "1.02.3", "1.2.-1", "1.2.3-alpha"} {
		if _, err := ParseVersion(input); err == nil {
			t.Fatalf("ParseVersion(%q) succeeded", input)
		}
	}
}
