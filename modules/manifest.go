package modules

import (
	"fmt"
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

// Manifest is a parsed oak.mod.
type Manifest struct {
	// Path is the module path: the import-path prefix of every package in
	// the module.
	Path string
	// Oak is the declared language version (informational in v1).
	Oak string
	// Requires lists dependency modules in source order.
	Requires []Requirement
	// Replaces maps a required module path to a local directory (relative
	// to the manifest's directory unless absolute).
	Replaces map[string]string
	// Profile is the discipline profile the module's packages are judged
	// under (docs/spec/85-discipline.md section 1): "default", "strict", or
	// "" when the manifest does not say.
	Profile string
}

// Profiles are the discipline profiles a manifest may declare.
var Profiles = map[string]bool{"default": true, "strict": true}

// ParseManifest parses oak.mod text. The grammar is line-oriented:
//
//	module <path>
//	oak <version>
//	require <path> <version>
//	replace <path> => <directory>
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
		default:
			return Manifest{}, fmt.Errorf("oak.mod:%d: unknown directive %q", lineNumber, fields[0])
		}
	}
	if manifest.Path == "" {
		return Manifest{}, fmt.Errorf("oak.mod: missing module directive")
	}
	for path := range manifest.Replaces {
		if !seenRequire[path] {
			return Manifest{}, fmt.Errorf("oak.mod: replace of %q without a matching require", path)
		}
	}
	return manifest, nil
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
