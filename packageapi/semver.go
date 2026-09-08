// Package packageapi classifies public Oak package API changes and enforces
// the version implied by them. Snapshots are produced after type checking, so
// Type is canonical semantic identity and ABI is canonical representation.
package packageapi

import (
	"fmt"
	"sort"
	"strconv"
	"strings"
)

type ChangeLevel uint8

const (
	Patch ChangeLevel = iota
	Minor
	Major
)

func (l ChangeLevel) String() string {
	switch l {
	case Major:
		return "major"
	case Minor:
		return "minor"
	default:
		return "patch"
	}
}

type Version struct {
	Major int
	Minor int
	Patch int
}

func ParseVersion(text string) (Version, error) {
	if strings.HasPrefix(text, "v") {
		text = text[1:]
	}
	parts := strings.Split(text, ".")
	if len(parts) != 3 {
		return Version{}, fmt.Errorf("version %q must have form MAJOR.MINOR.PATCH", text)
	}
	values := [3]int{}
	for i, part := range parts {
		if part == "" || (len(part) > 1 && part[0] == '0') {
			return Version{}, fmt.Errorf("version %q has a non-canonical component", text)
		}
		// Oak source is UTF-8, but SemVer numeric identifiers are defined by
		// the ASCII digits 0-9. Validate the lexical grammar before Atoi so
		// signs and other Unicode source characters cannot be normalized into
		// a different package version.
		for j := 0; j < len(part); j++ {
			if part[j] < '0' || part[j] > '9' {
				return Version{}, fmt.Errorf("version %q has an invalid component", text)
			}
		}
		n, err := strconv.Atoi(part)
		if err != nil {
			return Version{}, fmt.Errorf("version %q has an invalid component", text)
		}
		values[i] = n
	}
	return Version{Major: values[0], Minor: values[1], Patch: values[2]}, nil
}

func (v Version) String() string {
	return fmt.Sprintf("%d.%d.%d", v.Major, v.Minor, v.Patch)
}

// Export is one public name in a checked package API.
//
// Type is canonical semantic identity: parameter and result types, generic
// constraints, effects, and record shapes. ABI is canonical representation:
// calling convention, size/alignment, field offsets/order, tags and ownership.
// Documentation and implementation bodies intentionally do not appear.
type Export struct {
	Kind string `json:"kind"`
	Type string `json:"type"`
	ABI  string `json:"abi,omitempty"`
}

type Snapshot struct {
	Package string            `json:"package"`
	Version string            `json:"version"`
	Exports map[string]Export `json:"exports"`
}

type Change struct {
	Name   string      `json:"name"`
	Level  ChangeLevel `json:"level"`
	Reason string      `json:"reason"`
}

type Report struct {
	Required ChangeLevel `json:"required"`
	Changes  []Change    `json:"changes"`
}

func Compare(previous, current Snapshot) Report {
	report := Report{Required: Patch}
	for name, old := range previous.Exports {
		now, present := current.Exports[name]
		switch {
		case !present:
			report.add(name, Major, "public export removed")
		case old.Kind != now.Kind:
			report.add(name, Major, "export kind changed")
		case old.Type != now.Type:
			report.add(name, Major, "semantic type changed")
		case old.ABI != now.ABI:
			report.add(name, Major, "public ABI or layout changed")
		}
	}
	for name := range current.Exports {
		if _, existed := previous.Exports[name]; !existed {
			report.add(name, Minor, "public export added")
		}
	}
	sort.Slice(report.Changes, func(i, j int) bool {
		if report.Changes[i].Name != report.Changes[j].Name {
			return report.Changes[i].Name < report.Changes[j].Name
		}
		return report.Changes[i].Reason < report.Changes[j].Reason
	})
	return report
}

func (r *Report) add(name string, level ChangeLevel, reason string) {
	r.Changes = append(r.Changes, Change{Name: name, Level: level, Reason: reason})
	if level > r.Required {
		r.Required = level
	}
}

func NextVersion(previous Version, level ChangeLevel) Version {
	switch level {
	case Major:
		// Before 1.0, breaking and additive public changes both advance MINOR.
		if previous.Major == 0 {
			return Version{Minor: previous.Minor + 1}
		}
		return Version{Major: previous.Major + 1}
	case Minor:
		return Version{Major: previous.Major, Minor: previous.Minor + 1}
	default:
		return Version{Major: previous.Major, Minor: previous.Minor, Patch: previous.Patch + 1}
	}
}

// Enforce requires the exact next version implied by Compare. Exactness avoids
// accidental over-versioning and makes the rule reproducible by every client.
func Enforce(previous, current Snapshot) (Report, error) {
	report := Compare(previous, current)
	if previous.Package == "" || current.Package == "" || previous.Package != current.Package {
		return report, fmt.Errorf("package identity changed from %q to %q", previous.Package, current.Package)
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
