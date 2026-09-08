package modules

import (
	"fmt"
	"strings"
)

// MaxImportPathLength bounds import paths; longer paths are rejected before
// any filesystem work happens.
const MaxImportPathLength = 256

// ValidateImportPath enforces the import-path grammar of
// docs/spec/83-modules.md section 3: one or more `/`-separated segments, each
// a non-empty run of ASCII lowercase letters, digits, `.`, `_`, and `-`,
// starting with a letter or digit. `.` and `..` are not segments, and no
// segment may contain two adjacent underscores (Reserved). The grammar is
// what makes the filesystem mapping containment-safe: a valid path can only
// name a directory below the module root.
func ValidateImportPath(path string) error {
	if path == "" {
		return fmt.Errorf("import path is empty")
	}
	if len(path) > MaxImportPathLength {
		return fmt.Errorf("import path %q exceeds %d bytes", path, MaxImportPathLength)
	}
	for _, segment := range strings.Split(path, "/") {
		if err := validateSegment(path, segment); err != nil {
			return err
		}
	}
	return nil
}

func validateSegment(path, segment string) error {
	if segment == "" {
		return fmt.Errorf("import path %q has an empty segment", path)
	}
	if segment == "." || segment == ".." {
		return fmt.Errorf("import path %q has a relative segment %q", path, segment)
	}
	if Reserved(segment) {
		return fmt.Errorf("import path %q segment %q contains the reserved sequence %q", path, segment, Separator)
	}
	for i, r := range segment {
		switch {
		case 'a' <= r && r <= 'z', '0' <= r && r <= '9':
		case r == '.', r == '_', r == '-':
			if i == 0 {
				return fmt.Errorf("import path %q segment %q must start with a letter or digit", path, segment)
			}
		default:
			return fmt.Errorf("import path %q segment %q has an invalid character %q", path, segment, r)
		}
	}
	return nil
}

// IsStandardLibraryPath reports whether an import path names a standard
// library package: like Go, a path whose first segment contains no dot is
// reserved for the standard library, and module paths must carry a dotted
// first segment (`example.com/...`).
func IsStandardLibraryPath(path string) bool {
	first := path
	if index := strings.IndexByte(path, '/'); index >= 0 {
		first = path[:index]
	}
	return !strings.Contains(first, ".")
}

// LastSegment returns the final path segment, the default binding name of an
// import and the required package clause name of an importable package.
func LastSegment(path string) string {
	if index := strings.LastIndexByte(path, '/'); index >= 0 {
		return path[index+1:]
	}
	return path
}

// ValidPackageName reports whether name may appear in a package clause: a
// lowercase ASCII identifier without the reserved `__` sequence. Package names
// are also identifiers (the default import alias), so the identifier grammar
// applies.
func ValidPackageName(name string) bool {
	if name == "" || Reserved(name) {
		return false
	}
	for i, r := range name {
		switch {
		case 'a' <= r && r <= 'z':
		case r == '_' && i > 0:
		case '0' <= r && r <= '9' && i > 0:
		default:
			return false
		}
	}
	return true
}

// HasPathPrefix reports whether path is prefix itself or lies below prefix
// in the import-path tree (segment-wise, never a plain string prefix).
func HasPathPrefix(path, prefix string) bool {
	return path == prefix || strings.HasPrefix(path, prefix+"/")
}
