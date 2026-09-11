package packageapi

// The Go classifier tested against the laws of spec/lean/Oak/Semver.lean:
// classification is the maximum (classify_ge, classify_le_bound,
// classify_mono, classify_patch_iff), the per-export rule
// (exportChange_none_iff, exportChange_cases), the exact bump (next_gt,
// enforce_unique, next_pre1_major_eq_minor, next_injective_level,
// next_resets), and the module level (moduleLevel_ge, moduleLevel_patch_iff,
// moduleLevel_removed).

import (
	"fmt"
	"math/rand"
	"testing"
)

func randomExport(rng *rand.Rand) Export {
	return Export{Kind: fmt.Sprint("k", rng.Intn(2)), Type: fmt.Sprint("t", rng.Intn(3)), ABI: fmt.Sprint("a", rng.Intn(2))}
}

func randomSnapshot(rng *rand.Rand, names int) Snapshot {
	s := Snapshot{Package: "p", Version: "1.0.0", Exports: map[string]Export{}}
	for i := 0; i < names; i++ {
		if rng.Intn(2) == 0 {
			s.Exports[fmt.Sprint("e", i)] = randomExport(rng)
		}
	}
	return s
}

func TestLawsClassificationIsTheMaximum(t *testing.T) {
	rng := rand.New(rand.NewSource(7))
	for round := 0; round < 500; round++ {
		previous, current := randomSnapshot(rng, 6), randomSnapshot(rng, 6)
		report := Compare(previous, current)
		// classify_ge: every change is at most the classification.
		for _, change := range report.Changes {
			if change.Level > report.Required {
				t.Fatalf("change %+v exceeds required %s", change, report.Required)
			}
		}
		// classify_le_bound / classify_patch_iff: patch exactly when no change.
		if (report.Required == Patch) != (len(report.Changes) == 0) {
			t.Fatalf("patch iff no changes violated: %+v", report)
		}
		if len(report.Changes) != 0 {
			max := Patch
			for _, change := range report.Changes {
				if change.Level > max {
					max = change.Level
				}
			}
			if max != report.Required {
				t.Fatalf("required %s is not the maximum %s", report.Required, max)
			}
		}
		// classify_mono: adding an unrelated change never lowers the level.
		wider := Snapshot{Package: "p", Version: "1.0.0", Exports: map[string]Export{}}
		for name, export := range current.Exports {
			wider.Exports[name] = export
		}
		wider.Exports["extra"] = Export{Kind: "function", Type: "fn()->()"}
		if Compare(previous, wider).Required < report.Required {
			t.Fatalf("superset of changes classified lower: %+v vs %+v", Compare(previous, wider), report)
		}
	}
}

func TestLawsPerExportRule(t *testing.T) {
	rng := rand.New(rand.NewSource(11))
	for round := 0; round < 500; round++ {
		var previous, current Snapshot
		previous.Package, current.Package = "p", "p"
		previous.Exports, current.Exports = map[string]Export{}, map[string]Export{}
		var old, now *Export
		if rng.Intn(2) == 0 {
			e := randomExport(rng)
			old = &e
			previous.Exports["x"] = e
		}
		if rng.Intn(2) == 0 {
			e := randomExport(rng)
			now = &e
			current.Exports["x"] = e
		}
		report := Compare(previous, current)
		switch {
		case old == nil && now == nil:
			if len(report.Changes) != 0 {
				t.Fatalf("absent on both sides must be no change: %+v", report)
			}
		case old != nil && now == nil:
			if len(report.Changes) != 1 || report.Changes[0].Level != Major {
				t.Fatalf("removal must be major: %+v", report)
			}
		case old == nil && now != nil:
			if len(report.Changes) != 1 || report.Changes[0].Level != Minor {
				t.Fatalf("addition must be minor: %+v", report)
			}
		default:
			// exportChange_none_iff: no change iff identical identity.
			if (*old == *now) != (len(report.Changes) == 0) {
				t.Fatalf("identity rule violated for %+v -> %+v: %+v", *old, *now, report)
			}
			if *old != *now && report.Changes[0].Level != Major {
				t.Fatalf("mutation must be major: %+v", report)
			}
		}
	}
}

func less(a, b Version) bool {
	if a.Major != b.Major {
		return a.Major < b.Major
	}
	if a.Minor != b.Minor {
		return a.Minor < b.Minor
	}
	return a.Patch < b.Patch
}

func TestLawsExactBump(t *testing.T) {
	rng := rand.New(rand.NewSource(13))
	levels := []ChangeLevel{Patch, Minor, Major}
	for round := 0; round < 2000; round++ {
		v := Version{Major: rng.Intn(3), Minor: rng.Intn(4), Patch: rng.Intn(4)}
		for _, level := range levels {
			next := NextVersion(v, level)
			// next_gt: strictly greater.
			if !less(v, next) {
				t.Fatalf("NextVersion(%s, %s) = %s is not greater", v, level, next)
			}
			// enforce_unique / enforce_next: exactly the computed version passes.
			previous := Snapshot{Package: "p", Version: v.String(), Exports: map[string]Export{}}
			current := Snapshot{Package: "p", Version: next.String(), Exports: map[string]Export{}}
			if level != Patch {
				previous.Exports["a"] = Export{Kind: "value", Type: "u8"}
				if level == Minor {
					current.Exports["a"] = previous.Exports["a"]
					current.Exports["b"] = Export{Kind: "value", Type: "u8"}
				}
			}
			if _, err := Enforce(previous, current); err != nil {
				t.Fatalf("exact bump rejected: %v", err)
			}
			for _, other := range levels {
				if wrong := NextVersion(v, other); wrong != next {
					current.Version = wrong.String()
					if _, err := Enforce(previous, current); err == nil {
						t.Fatalf("Enforce accepted %s for a %s change from %s", wrong, level, v)
					}
				}
			}
		}
		if v.Major == 0 {
			// next_pre1_major_eq_minor.
			if NextVersion(v, Major) != NextVersion(v, Minor) {
				t.Fatalf("pre-1.0 major and minor differ at %s", v)
			}
		} else {
			// next_injective_level and next_resets.
			seen := map[Version]ChangeLevel{}
			for _, level := range levels {
				next := NextVersion(v, level)
				if prior, dup := seen[next]; dup {
					t.Fatalf("levels %s and %s both bump %s to %s", prior, level, v, next)
				}
				seen[next] = level
			}
			if m := NextVersion(v, Major); m.Minor != 0 || m.Patch != 0 {
				t.Fatalf("major bump did not reset: %s", m)
			}
			if m := NextVersion(v, Minor); m.Patch != 0 {
				t.Fatalf("minor bump did not reset patch: %s", m)
			}
		}
	}
}

func TestLawsModuleLevel(t *testing.T) {
	rng := rand.New(rand.NewSource(17))
	for round := 0; round < 300; round++ {
		previous := ModuleSnapshot{Module: "m", Version: "1.0.0", Packages: map[string]Snapshot{}}
		current := ModuleSnapshot{Module: "m", Version: "1.1.0", Packages: map[string]Snapshot{}}
		for i := 0; i < 4; i++ {
			path := fmt.Sprint("m/p", i)
			if rng.Intn(3) != 0 {
				s := randomSnapshot(rng, 3)
				s.Package = path
				previous.Packages[path] = s
			}
			if rng.Intn(3) != 0 {
				s := randomSnapshot(rng, 3)
				s.Package = path
				current.Packages[path] = s
			}
		}
		report := CompareModules(previous, current)
		max := Patch
		removed := false
		for _, pkg := range report.Packages {
			// moduleLevel_ge.
			if pkg.Level > report.Required {
				t.Fatalf("package level %s exceeds module level %s", pkg.Level, report.Required)
			}
			if pkg.Level > max {
				max = pkg.Level
			}
			_, existed := previous.Packages[pkg.Package]
			_, present := current.Packages[pkg.Package]
			switch {
			case existed && !present:
				removed = true
				if pkg.Level != Major {
					t.Fatalf("removed package must be major: %+v", pkg)
				}
			case !existed && present:
				if pkg.Level != Minor {
					t.Fatalf("added package must be minor: %+v", pkg)
				}
			default:
				if pkg.Level != Compare(previous.Packages[pkg.Package], current.Packages[pkg.Package]).Required {
					t.Fatalf("surviving package level is not its own classification: %+v", pkg)
				}
			}
		}
		if max != report.Required {
			t.Fatalf("module level %s is not the maximum %s", report.Required, max)
		}
		// moduleLevel_removed.
		if removed && report.Required != Major {
			t.Fatalf("a removed package must make the module major: %+v", report)
		}
		// moduleLevel_patch_iff.
		allPatch := true
		for _, pkg := range report.Packages {
			if pkg.Level != Patch {
				allPatch = false
			}
		}
		if allPatch != (report.Required == Patch) {
			t.Fatalf("patch iff every package patch violated: %+v", report)
		}
	}
}
