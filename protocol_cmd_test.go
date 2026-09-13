package main

import (
	"errors"
	"testing"
)

// -map takes renames and TLA+ expressions alike (docs/spec/112-protocols.md
// §4a; the dbs pilot's round-five item 9): commas inside brackets belong to
// the expression, `<-` reads as `=`, and @file loads the pairs from a file.
func TestParseRefinementMapping(t *testing.T) {
	got, err := parseRefinementMapping("state=st, count <- Cardinality({k \\in 0..1 : acked[k]}), pair=f[a, b]", nil)
	if err != nil {
		t.Fatal(err)
	}
	want := map[string]string{"state": "st", "count": "Cardinality({k \\in 0..1 : acked[k]})", "pair": "f[a, b]"}
	for name, value := range want {
		if got[name] != value {
			t.Fatalf("%s = %q, want %q (all: %v)", name, got[name], value, got)
		}
	}
	if len(got) != len(want) {
		t.Fatalf("mapping has %d entries, want %d: %v", len(got), len(want), got)
	}
	file := "\\* the refinement mapping of MC_Refine\nstate <- st\ncount <- Cardinality({k \\in 0..1 : acked[k]}) \\* quorum\n"
	got, err = parseRefinementMapping("@mapping.tla", func(path string) ([]byte, error) {
		if path != "mapping.tla" {
			return nil, errors.New("wrong path " + path)
		}
		return []byte(file), nil
	})
	if err != nil {
		t.Fatal(err)
	}
	if got["state"] != "st" || got["count"] != "Cardinality({k \\in 0..1 : acked[k]})" || len(got) != 2 {
		t.Fatalf("file mapping: %v", got)
	}
	for _, bad := range []string{"state", "=st", "state=", "a.b=c", "state=st,state=x"} {
		if _, err := parseRefinementMapping(bad, nil); err == nil {
			t.Fatalf("%q accepted", bad)
		}
	}
}
