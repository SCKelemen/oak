package modules

import (
	"sort"

	"github.com/SCKelemen/oak/packageapi"
)

// Less orders versions numerically by major, minor, patch.
func Less(a, b packageapi.Version) bool {
	if a.Major != b.Major {
		return a.Major < b.Major
	}
	if a.Minor != b.Minor {
		return a.Minor < b.Minor
	}
	return a.Patch < b.Patch
}

// Select performs minimal version selection over the requirements gathered
// from every manifest in the build: for each module path, the selected
// version is the maximum version any manifest requires. It is the least
// version satisfying every requirement (Oak.Modules.Versions.select_minimal),
// so the build is reproducible from the manifests alone, with no lock file
// and no network (docs/spec/83-modules.md section 4.2).
func Select(requirements []Requirement) map[string]packageapi.Version {
	selected := map[string]packageapi.Version{}
	for _, requirement := range requirements {
		current, seen := selected[requirement.Path]
		if !seen || Less(current, requirement.Version) {
			selected[requirement.Path] = requirement.Version
		}
	}
	return selected
}

// SelectedPaths returns the module paths of a selection in sorted order, so
// loaders iterate deterministically.
func SelectedPaths(selected map[string]packageapi.Version) []string {
	paths := make([]string, 0, len(selected))
	for path := range selected {
		paths = append(paths, path)
	}
	sort.Strings(paths)
	return paths
}
