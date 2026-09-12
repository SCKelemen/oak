package modules

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/packageapi"
)

// ManifestFile is the module root marker and manifest (docs/spec/83-modules.md
// section 4).
const ManifestFile = "oak.mod"

// MaxManifestSize bounds a manifest read before parsing.
const MaxManifestSize = 1 << 20

// Requirement is one `require` line: a module path at a minimum version,
// optionally pinned to an archive location and content digest
// (`require example.com/dep 1.2.0 https://... sha256:<hex>`, section 4.4).
type Requirement struct {
	Path    string
	Version packageapi.Version
	// Location is the HTTPS archive URL, empty when the module comes from a
	// replace directive or a pre-populated cache.
	Location string
	// Digest is the pinned `sha256:<hex>` of the archive.
	Digest string
}

// VendorDir is the directory under a module root that holds vendored
// copies of its dependencies (`oak mod vendor`), each under its module path.
const VendorDir = "vendor"

// VendorListFile records what was vendored.
const VendorListFile = "modules.txt"

// Manifest is a parsed oak.mod.
type Manifest struct {
	// Path is the module path: the import-path prefix of every package in
	// the module.
	Path string
	// Oak is the declared language version (informational in v1).
	Oak string
	// Version is the module's own SemVer version (`version 1.2.0`), the
	// candidate `oak mod bump` checks against the previous API snapshot.
	Version string
	// Requires lists dependency modules in source order.
	Requires []Requirement
	// Replaces maps a required module path to a local directory (relative
	// to the manifest's directory unless absolute).
	Replaces map[string]string
	// Profile is the discipline profile the module's packages are judged
	// under (docs/spec/85-discipline.md section 1): "default", "strict", or
	// "" when the manifest does not say.
	Profile string
	// Steady lists the steady-state entry points (`steady <package> <fn>`,
	// docs/spec/85-discipline.md section 4): functions after which the
	// program may not allocate. The compiler checks each as if it declared
	// `forbids { Memory.Allocate }`.
	Steady []SteadyEntry
	// Admits lists the recorded-assumption codes this module accepts under
	// the strict profile (`admit <code>`, docs/spec/85-discipline.md section
	// 7): the assumption stays recorded and audited, but does not reject the
	// module's packages. Only AdmissibleAssumptions may be named.
	Admits []string
	// Links lists the native inputs this module links (`link <path>`,
	// docs/spec/83-modules.md section 4.6): static archives or relocatable
	// objects, as slash-separated paths relative to the module root, in
	// declaration order. The loader resolves and containment-checks them.
	Links []string
	// Frameworks lists the macOS frameworks this module links (`framework
	// <Name>`), in declaration order; other hosts ignore them with a note.
	Frameworks []string
}

// AdmissibleAssumptions are the diagnostic codes an `admit` directive may
// name: the recorded assumptions the checker leaves standing as warnings and
// the REPL's :obligations lists (docs/spec/85-discipline.md section 7). An
// error is never admissible; neither is a warning that is not an assumption.
var AdmissibleAssumptions = map[string]string{
	"OAK-B0110": "an unsafe block's writable-disjointness or foreign-buffer assumption",
	"OAK-B0122": "an unsafe block's foreign-function-pointer assumption (c.fn_at)",
	"OAK-D0102": "a tail-recursion obligation",
	"OAK-D0103": "a loop without a static iteration bound",
}

// SteadyEntry names one steady-state entry point: a function of a package of
// this module.
type SteadyEntry struct {
	Path string
	Name string
}

// Profiles are the discipline profiles a manifest may declare.
var Profiles = map[string]bool{"default": true, "strict": true}

// ParseManifest parses oak.mod text. The grammar is line-oriented:
//
//	module <path>
//	oak <version>
//	require <path> <version>
//	replace <path> => <directory>
//	profile <default|strict>
//	steady <package-path> <function>
//	admit <diagnostic-code>
//	link <path>
//	framework <Name>
//	// comment
//
// Unknown directives, malformed lines, duplicate `module`/`oak`/`replace`
// entries, and invalid paths or versions fail closed with an error naming the
// line.
func ParseManifest(text string) (Manifest, error) {
	if len(text) > MaxManifestSize {
		return Manifest{}, fmt.Errorf("oak.mod exceeds %d bytes", MaxManifestSize)
	}
	manifest := Manifest{Replaces: map[string]string{}}
	seenRequire := map[string]bool{}
	for number, raw := range strings.Split(text, "\n") {
		line := strings.TrimSpace(stripComment(raw))
		if line == "" {
			continue
		}
		fields := strings.Fields(line)
		lineNumber := number + 1
		switch fields[0] {
		case "module":
			if len(fields) != 2 {
				return Manifest{}, fmt.Errorf("oak.mod:%d: module directive takes exactly one path", lineNumber)
			}
			if manifest.Path != "" {
				return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate module directive", lineNumber)
			}
			if err := ValidateImportPath(fields[1]); err != nil {
				return Manifest{}, fmt.Errorf("oak.mod:%d: %v", lineNumber, err)
			}
			if IsStandardLibraryPath(fields[1]) {
				return Manifest{}, fmt.Errorf("oak.mod:%d: module path %q is reserved for the standard library (first segment needs a dot)", lineNumber, fields[1])
			}
			manifest.Path = fields[1]
		case "oak":
			if len(fields) != 2 {
				return Manifest{}, fmt.Errorf("oak.mod:%d: oak directive takes exactly one version", lineNumber)
			}
			if manifest.Oak != "" {
				return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate oak directive", lineNumber)
			}
			if _, err := packageapi.ParseVersion(fields[1]); err != nil {
				return Manifest{}, fmt.Errorf("oak.mod:%d: %v", lineNumber, err)
			}
			manifest.Oak = fields[1]
		case "version":
			if len(fields) != 2 {
				return Manifest{}, fmt.Errorf("oak.mod:%d: version directive takes exactly one version", lineNumber)
			}
			if manifest.Version != "" {
				return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate version directive", lineNumber)
			}
			if _, err := packageapi.ParseVersion(fields[1]); err != nil {
				return Manifest{}, fmt.Errorf("oak.mod:%d: %v", lineNumber, err)
			}
			manifest.Version = fields[1]
		case "require":
			if len(fields) != 3 && len(fields) != 5 {
				return Manifest{}, fmt.Errorf("oak.mod:%d: require directive takes a path and a version, optionally followed by an archive URL and sha256:<hex> digest", lineNumber)
			}
			if err := ValidateImportPath(fields[1]); err != nil {
				return Manifest{}, fmt.Errorf("oak.mod:%d: %v", lineNumber, err)
			}
			if IsStandardLibraryPath(fields[1]) {
				return Manifest{}, fmt.Errorf("oak.mod:%d: standard library path %q cannot be required", lineNumber, fields[1])
			}
			version, err := packageapi.ParseVersion(fields[2])
			if err != nil {
				return Manifest{}, fmt.Errorf("oak.mod:%d: %v", lineNumber, err)
			}
			if seenRequire[fields[1]] {
				return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate require of %q", lineNumber, fields[1])
			}
			seenRequire[fields[1]] = true
			requirement := Requirement{Path: fields[1], Version: version}
			if len(fields) == 5 {
				if err := ValidateLocation(fields[3]); err != nil {
					return Manifest{}, fmt.Errorf("oak.mod:%d: %v", lineNumber, err)
				}
				if _, err := ParseDigest(fields[4]); err != nil {
					return Manifest{}, fmt.Errorf("oak.mod:%d: %v", lineNumber, err)
				}
				requirement.Location, requirement.Digest = fields[3], fields[4]
			}
			manifest.Requires = append(manifest.Requires, requirement)
		case "replace":
			if len(fields) != 4 || fields[2] != "=>" {
				return Manifest{}, fmt.Errorf("oak.mod:%d: replace directive has the form `replace <path> => <directory>`", lineNumber)
			}
			if err := ValidateImportPath(fields[1]); err != nil {
				return Manifest{}, fmt.Errorf("oak.mod:%d: %v", lineNumber, err)
			}
			if _, dup := manifest.Replaces[fields[1]]; dup {
				return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate replace of %q", lineNumber, fields[1])
			}
			manifest.Replaces[fields[1]] = fields[3]
		case "profile":
			if len(fields) != 2 {
				return Manifest{}, fmt.Errorf("oak.mod:%d: profile directive takes exactly one name (default or strict)", lineNumber)
			}
			if manifest.Profile != "" {
				return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate profile directive", lineNumber)
			}
			if !Profiles[fields[1]] {
				return Manifest{}, fmt.Errorf("oak.mod:%d: unknown profile %q (default or strict; docs/spec/85-discipline.md section 1)", lineNumber, fields[1])
			}
			manifest.Profile = fields[1]
		case "steady":
			if len(fields) != 3 {
				return Manifest{}, fmt.Errorf("oak.mod:%d: steady directive has the form `steady <package-path> <function>`", lineNumber)
			}
			if err := ValidateImportPath(fields[1]); err != nil {
				return Manifest{}, fmt.Errorf("oak.mod:%d: %v", lineNumber, err)
			}
			if IsStandardLibraryPath(fields[1]) {
				return Manifest{}, fmt.Errorf("oak.mod:%d: steady entry names standard library path %q; entry points are this module's functions", lineNumber, fields[1])
			}
			if !validIdentifier(fields[2]) {
				return Manifest{}, fmt.Errorf("oak.mod:%d: steady entry %q is not a function name", lineNumber, fields[2])
			}
			for _, prior := range manifest.Steady {
				if prior.Path == fields[1] && prior.Name == fields[2] {
					return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate steady entry %s %s", lineNumber, fields[1], fields[2])
				}
			}
			manifest.Steady = append(manifest.Steady, SteadyEntry{Path: fields[1], Name: fields[2]})
		case "admit":
			if len(fields) != 2 {
				return Manifest{}, fmt.Errorf("oak.mod:%d: admit directive has the form `admit <diagnostic-code>`", lineNumber)
			}
			if _, admissible := AdmissibleAssumptions[fields[1]]; !admissible {
				return Manifest{}, fmt.Errorf("oak.mod:%d: %q is not an admissible recorded assumption (%s; docs/spec/85-discipline.md section 7)", lineNumber, fields[1], admissibleList())
			}
			for _, prior := range manifest.Admits {
				if prior == fields[1] {
					return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate admit of %s", lineNumber, fields[1])
				}
			}
			manifest.Admits = append(manifest.Admits, fields[1])
		case "link":
			if len(fields) != 2 {
				return Manifest{}, fmt.Errorf("oak.mod:%d: link directive has the form `link <path>` (an archive or object inside the module)", lineNumber)
			}
			if err := ValidateLinkPath(fields[1]); err != nil {
				return Manifest{}, fmt.Errorf("oak.mod:%d: link %s: %v", lineNumber, fields[1], err)
			}
			for _, prior := range manifest.Links {
				if prior == fields[1] {
					return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate link of %s", lineNumber, fields[1])
				}
			}
			manifest.Links = append(manifest.Links, fields[1])
		case "framework":
			if len(fields) != 2 {
				return Manifest{}, fmt.Errorf("oak.mod:%d: framework directive has the form `framework <Name>`", lineNumber)
			}
			if !validIdentifier(fields[1]) {
				return Manifest{}, fmt.Errorf("oak.mod:%d: framework %q is not a framework name (letters, digits, underscores)", lineNumber, fields[1])
			}
			for _, prior := range manifest.Frameworks {
				if prior == fields[1] {
					return Manifest{}, fmt.Errorf("oak.mod:%d: duplicate framework %s", lineNumber, fields[1])
				}
			}
			manifest.Frameworks = append(manifest.Frameworks, fields[1])
		default:
			return Manifest{}, fmt.Errorf("oak.mod:%d: unknown directive %q", lineNumber, fields[0])
		}
	}
	if manifest.Path == "" {
		return Manifest{}, fmt.Errorf("oak.mod: missing module directive")
	}
	for path, target := range manifest.Replaces {
		if !seenRequire[path] && !StandardLibraryRealization(target) {
			return Manifest{}, fmt.Errorf("oak.mod: replace of %q without a matching require", path)
		}
	}
	return manifest, nil
}

// ValidateLinkPath accepts a `link` operand: a slash-separated relative path
// inside the module (no absolute path, no empty, `.` or `..` segment, no
// backslash) naming a static archive (`.a`) or a relocatable object (`.o`).
// Shared libraries, linker scripts, and bare flags are rejected here; the
// loader checks that the resolved file exists and stays inside the module
// root through symlinks (docs/spec/83-modules.md section 4.6).
func ValidateLinkPath(path string) error {
	if path == "" {
		return fmt.Errorf("empty path")
	}
	if strings.HasPrefix(path, "/") || strings.Contains(path, "\\") || strings.Contains(path, ":") {
		return fmt.Errorf("must be a slash-separated path relative to the module root")
	}
	for _, segment := range strings.Split(path, "/") {
		if segment == "" || segment == "." || segment == ".." {
			return fmt.Errorf("must not contain empty, `.` or `..` segments")
		}
	}
	if !strings.HasSuffix(path, ".a") && !strings.HasSuffix(path, ".o") {
		return fmt.Errorf("must name a static archive (.a) or a relocatable object (.o)")
	}
	return nil
}

// admissibleList spells the admissible codes in a stable order for
// diagnostics.
func admissibleList() string {
	codes := make([]string, 0, len(AdmissibleAssumptions))
	for code := range AdmissibleAssumptions {
		codes = append(codes, code)
	}
	sort.Strings(codes)
	return strings.Join(codes, ", ")
}

// stripComment removes a `//` comment that starts the line or follows
// whitespace; `//` inside a token (an https:// location) is kept.
func stripComment(line string) string {
	for index := 0; index+1 < len(line); index++ {
		if line[index] == '/' && line[index+1] == '/' && (index == 0 || line[index-1] == ' ' || line[index-1] == '\t') {
			return line[:index]
		}
	}
	return line
}

// validIdentifier accepts an Oak identifier: a letter or underscore followed
// by letters, digits, or underscores.
func validIdentifier(text string) bool {
	if text == "" {
		return false
	}
	for i, r := range text {
		alpha := (r >= 'a' && r <= 'z') || (r >= 'A' && r <= 'Z') || r == '_'
		digit := r >= '0' && r <= '9'
		if !alpha && !(digit && i > 0) {
			return false
		}
	}
	return true
}

// StandardLibraryRealization reports whether a replace target names a
// standard library realization of a port rather than a directory
// (docs/spec/120-io.md section 1): a bare lowercase identifier with no
// path separator. The loader checks that the package exists.
func StandardLibraryRealization(target string) bool {
	if target == "" || strings.ContainsAny(target, "/\\.") {
		return false
	}
	return ValidPackageName(target)
}
