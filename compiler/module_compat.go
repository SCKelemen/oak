package compiler

// Sealed-signature compatibility (docs/spec/82-package-semver.md section 8):
// a client that sealed an import depends only on the members its signature
// lists, so whether a new version of the dependency is safe for the client is
// decidable from the dependency's API snapshot alone — no source, no build of
// the dependency. This is the client-side counterpart of the exact-bump rule.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/packageapi"
)

// Incompatibility is one sealed member the snapshot cannot satisfy.
type Incompatibility struct {
	Importer string
	Alias    string
	Package  string
	Member   string
	Reason   string
}

func (i Incompatibility) String() string {
	return fmt.Sprintf("%s: %s.%s (package %s): %s", i.Importer, i.Alias, i.Member, i.Package, i.Reason)
}

// CheckSealedCompatibility builds every package of the module at moduleDir,
// collects the sealed imports of packages provided by snapshot.Module, and
// reports each signature member the snapshot fails to provide with the
// demanded kind and type. An empty result means every sealed client of the
// dependency compiles against that version's API.
func CheckSealedCompatibility(moduleDir string, snapshot packageapi.ModuleSnapshot) ([]Incompatibility, error) {
	_, packages, err := ModulePackages(moduleDir)
	if err != nil {
		return nil, err
	}
	paths := make([]string, 0, len(packages))
	for path := range packages {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	var problems []Incompatibility
	for _, path := range paths {
		tree, err := New().WithPackageDir(packages[path]).Parse().Get()
		if err != nil {
			return nil, fmt.Errorf("package %s: %w", path, err)
		}
		if tree.Modules == nil {
			continue
		}
		for _, sealed := range tree.Modules.Sealed {
			if !modules.HasPathPrefix(sealed.Package, snapshot.Module) {
				continue
			}
			provided, present := snapshot.Packages[sealed.Package]
			if !present {
				problems = append(problems, Incompatibility{sealed.Importer, sealed.Alias, sealed.Package, "*", "package absent from the snapshot"})
				continue
			}
			for _, member := range sealed.Members {
				export, exported := provided.Exports[member.Name]
				if !exported {
					problems = append(problems, Incompatibility{sealed.Importer, sealed.Alias, sealed.Package, member.Name, "not exported"})
					continue
				}
				switch member.Kind {
				case "type":
					if !isTypeKind(export.Kind) {
						problems = append(problems, Incompatibility{sealed.Importer, sealed.Alias, sealed.Package, member.Name, "signature needs a type, snapshot exports a " + export.Kind})
					}
				default:
					if export.Kind != "function" && export.Kind != "value" {
						problems = append(problems, Incompatibility{sealed.Importer, sealed.Alias, sealed.Package, member.Name, "signature needs a value, snapshot exports a " + export.Kind})
						continue
					}
					if member.Type != "" && !sameCanonicalType(member.Type, export.Type) {
						problems = append(problems, Incompatibility{sealed.Importer, sealed.Alias, sealed.Package, member.Name, fmt.Sprintf("signature requires %s, snapshot exports %s", member.Type, export.Type)})
					}
				}
			}
		}
	}
	return problems, nil
}

func isTypeKind(kind string) bool {
	switch kind {
	case "record", "struct", "alias", "sum", "opaque type", "interface":
		return true
	}
	return strings.HasPrefix(kind, "sum")
}

// sameCanonicalType compares a signature's canonical type text with a
// snapshot export's, tolerating the checked/expression spelling difference
// of whitespace only.
func sameCanonicalType(want, got string) bool {
	normalize := func(text string) string { return strings.ReplaceAll(text, " ", "") }
	return normalize(want) == normalize(got)
}

// CandidateResult is one candidate snapshot's verdict for a module.
type CandidateResult struct {
	Snapshot packageapi.ModuleSnapshot
	Version  packageapi.Version
	Problems []Incompatibility
}

// HighestCompatible checks each candidate snapshot of one dependency against
// the sealed imports of the module at moduleDir and returns the compatible
// candidate with the highest version (nil when none is), with every
// candidate's verdict in ascending version order. Candidates must agree on
// the module they describe and carry parseable versions.
func HighestCompatible(moduleDir string, candidates []packageapi.ModuleSnapshot) (*packageapi.ModuleSnapshot, []CandidateResult, error) {
	if len(candidates) == 0 {
		return nil, nil, fmt.Errorf("no candidate snapshots")
	}
	results := make([]CandidateResult, 0, len(candidates))
	for _, candidate := range candidates {
		if candidate.Module != candidates[0].Module {
			return nil, nil, fmt.Errorf("candidates describe different modules: %q and %q", candidates[0].Module, candidate.Module)
		}
		version, err := packageapi.ParseVersion(candidate.Version)
		if err != nil {
			return nil, nil, fmt.Errorf("candidate %s: %w", candidate.Module, err)
		}
		problems, err := CheckSealedCompatibility(moduleDir, candidate)
		if err != nil {
			return nil, nil, err
		}
		results = append(results, CandidateResult{Snapshot: candidate, Version: version, Problems: problems})
	}
	sort.SliceStable(results, func(i, j int) bool { return versionLess(results[i].Version, results[j].Version) })
	var best *packageapi.ModuleSnapshot
	for i := range results {
		if len(results[i].Problems) == 0 {
			best = &results[i].Snapshot
		}
	}
	return best, results, nil
}

func versionLess(a, b packageapi.Version) bool {
	if a.Major != b.Major {
		return a.Major < b.Major
	}
	if a.Minor != b.Minor {
		return a.Minor < b.Minor
	}
	return a.Patch < b.Patch
}
