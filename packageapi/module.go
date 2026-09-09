package packageapi

// Module-level API snapshots and SemVer (docs/spec/82-package-semver.md
// section 6): a module is versioned as one unit, so its required release is
// the highest requirement over its packages, with a new package counting as
// an addition and a removed package as a breaking change.

import (
	"fmt"
	"sort"
)

// ModuleSnapshot is the checked public API of every package of a module.
type ModuleSnapshot struct {
	Module   string              `json:"module"`
	Version  string              `json:"version"`
	Packages map[string]Snapshot `json:"packages"`
}

// PackageChange is one package's contribution to a module report.
type PackageChange struct {
	Package string      `json:"package"`
	Level   ChangeLevel `json:"level"`
	Reason  string      `json:"reason,omitempty"`
	Changes []Change    `json:"changes,omitempty"`
}

// ModuleReport is the classification of a module API change.
type ModuleReport struct {
	Required ChangeLevel     `json:"required"`
	Packages []PackageChange `json:"packages"`
}

// CompareModules classifies the change from previous to current: the
// required release is the maximum over packages; an added package is minor,
// a removed package major.
func CompareModules(previous, current ModuleSnapshot) ModuleReport {
	report := ModuleReport{Required: Patch}
	paths := map[string]bool{}
	for path := range previous.Packages {
		paths[path] = true
	}
	for path := range current.Packages {
		paths[path] = true
	}
	sorted := make([]string, 0, len(paths))
	for path := range paths {
		sorted = append(sorted, path)
	}
	sort.Strings(sorted)
	for _, path := range sorted {
		old, existed := previous.Packages[path]
		now, present := current.Packages[path]
		var change PackageChange
		switch {
		case !present:
			change = PackageChange{Package: path, Level: Major, Reason: "package removed"}
		case !existed:
			change = PackageChange{Package: path, Level: Minor, Reason: "package added"}
		default:
			packageReport := Compare(old, now)
			change = PackageChange{Package: path, Level: packageReport.Required, Changes: packageReport.Changes}
		}
		if change.Level > report.Required {
			report.Required = change.Level
		}
		report.Packages = append(report.Packages, change)
	}
	return report
}

// EnforceModule requires the exact next version implied by CompareModules
// and an unchanged module identity.
func EnforceModule(previous, current ModuleSnapshot) (ModuleReport, error) {
	report := CompareModules(previous, current)
	if previous.Module == "" || current.Module == "" || previous.Module != current.Module {
		return report, fmt.Errorf("module identity changed from %q to %q", previous.Module, current.Module)
	}
	oldVersion, err := ParseVersion(previous.Version)
	if err != nil {
		return report, fmt.Errorf("previous snapshot: %w", err)
	}
	newVersion, err := ParseVersion(current.Version)
	if err != nil {
		return report, fmt.Errorf("current snapshot: %w", err)
	}
	expected := NextVersion(oldVersion, report.Required)
	if newVersion != expected {
		return report, fmt.Errorf("%s API change requires version %s; declared %s", report.Required, expected, newVersion)
	}
	return report, nil
}

// RequiredVersion is the version a module must declare after the change
// from previous to current.
func RequiredVersion(previous, current ModuleSnapshot) (Version, ModuleReport, error) {
	report := CompareModules(previous, current)
	oldVersion, err := ParseVersion(previous.Version)
	if err != nil {
		return Version{}, report, fmt.Errorf("previous snapshot: %w", err)
	}
	return NextVersion(oldVersion, report.Required), report, nil
}

// SameAPI reports whether two module snapshots expose identical APIs
// (versions aside): the check `oak mod download` applies to an archive's
// carried snapshot against the module it actually contains.
func SameAPI(a, b ModuleSnapshot) bool {
	if a.Module != b.Module || len(a.Packages) != len(b.Packages) {
		return false
	}
	for path, snapshot := range a.Packages {
		other, ok := b.Packages[path]
		if !ok || len(other.Exports) != len(snapshot.Exports) {
			return false
		}
		for name, export := range snapshot.Exports {
			if other.Exports[name] != export {
				return false
			}
		}
	}
	return true
}
