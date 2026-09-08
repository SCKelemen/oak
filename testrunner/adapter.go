package testrunner

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strings"

	"github.com/SCKelemen/oak/compiler"
)

type adapterObject struct {
	Path   string `json:"path"`
	SHA256 string `json:"sha256"`
}
type adapterManifest struct {
	Version       int                          `json:"version"`
	Name          string                       `json:"name"`
	Deterministic bool                         `json:"deterministic"`
	Bindings      []compiler.SimulationBinding `json:"bindings"`
	Objects       []adapterObject              `json:"objects"`
}
type nativeAdapter struct {
	manifest adapterManifest
	identity string
	objects  [][]byte
}

// Adapter paths resolve from the manifest, never from a replay artifact. Each
// object is verified and snapshotted before compilation so a rebuild cannot
// race between fingerprinting and linking. Only self-contained archives and
// ELF relocatable objects are accepted; thin archives/shared libraries/scripts
// could introduce dependencies outside the recorded build.
func loadAdapter(path string) (*nativeAdapter, error) {
	if path == "" {
		return nil, nil
	}
	f, err := os.Open(path)
	if err != nil {
		return nil, err
	}
	defer f.Close()
	dec := json.NewDecoder(io.LimitReader(f, 1<<20))
	dec.DisallowUnknownFields()
	var m adapterManifest
	if err := dec.Decode(&m); err != nil {
		return nil, fmt.Errorf("adapter manifest: %w", err)
	}
	var extra any
	if err := dec.Decode(&extra); err != io.EOF {
		return nil, fmt.Errorf("adapter manifest: trailing data")
	}
	if m.Version != 1 || m.Name == "" || !m.Deterministic || len(m.Objects) == 0 || len(m.Objects) > 32 || len(m.Bindings) == 0 {
		return nil, fmt.Errorf("adapter manifest requires version 1, name, deterministic: true, bindings and 1..32 objects")
	}
	names, symbols := map[string]bool{}, map[string]bool{}
	validABI := func(s string) bool {
		switch s {
		case "c.UInt8", "c.UInt16", "c.UInt32", "c.UInt64", "c.Int8", "c.Int16", "c.Int32", "c.Int64":
			return true
		}
		return false
	}
	for _, b := range m.Bindings {
		if !cIdentifier.MatchString(b.Name) || !cIdentifier.MatchString(b.Symbol) || strings.HasPrefix(b.Symbol, "oak_") || names[b.Name] || symbols[b.Symbol] || !(b.Return == "()" || validABI(b.Return)) {
			return nil, fmt.Errorf("adapter manifest: invalid or duplicate binding %q; oak_ symbols are reserved", b.Name)
		}
		for _, p := range b.Parameters {
			if !validABI(p) {
				return nil, fmt.Errorf("adapter manifest: %s requires fixed-width scalar C parameters", b.Name)
			}
		}
		names[b.Name], symbols[b.Symbol] = true, true
	}
	a := &nativeAdapter{manifest: m}
	// Paths are locators, not build identity. Moving the same adapter must not
	// break exact replay; declaration order and object link order are identity.
	identity := m
	identity.Objects = append([]adapterObject(nil), m.Objects...)
	for i, obj := range m.Objects {
		if obj.Path == "" || (filepath.Ext(obj.Path) != ".a" && filepath.Ext(obj.Path) != ".o") {
			return nil, fmt.Errorf("adapter object must be .a or .o")
		}
		p := obj.Path
		if !filepath.IsAbs(p) {
			p = filepath.Join(filepath.Dir(path), p)
		}
		file, err := os.Open(p)
		if err != nil {
			return nil, err
		}
		data, readErr := io.ReadAll(io.LimitReader(file, (64<<20)+1))
		file.Close()
		if readErr != nil {
			return nil, readErr
		}
		if len(data) > 64<<20 {
			return nil, fmt.Errorf("adapter object exceeds 64 MiB")
		}
		hash := sha256.Sum256(data)
		if obj.SHA256 != hex.EncodeToString(hash[:]) {
			return nil, fmt.Errorf("adapter object %s: SHA-256 mismatch", obj.Path)
		}
		archive := bytes.HasPrefix(data, []byte("!<arch>\n"))
		elf := len(data) >= 18 && bytes.Equal(data[:4], []byte{127, 'E', 'L', 'F'}) && (data[5] == 1 && data[16] == 1 && data[17] == 0 || data[5] == 2 && data[16] == 0 && data[17] == 1)
		if !archive && !elf {
			return nil, fmt.Errorf("adapter object %s: expected self-contained archive or ELF relocatable object", obj.Path)
		}
		a.objects = append(a.objects, data)
		identity.Objects[i].Path = ""
	}
	encoded, err := json.Marshal(identity)
	if err != nil {
		return nil, err
	}
	a.identity = string(encoded)
	return a, nil
}

func packageCompilation(pkg Package, adapter *nativeAdapter) compiler.Compilation {
	comp := compiler.New().WithSource(filepath.Join(pkg.Dir, "<oak-test-package>"), pkg.Source)
	if pkg.Module {
		// Module packages resolve imports through the enclosing oak.mod; the
		// root package's *_test.oak files join it only in this test build.
		comp = compiler.New().WithPackageDir(pkg.Dir).WithTestFiles(true)
	}
	// All invocations of a package containing Sim tests use the same profile,
	// preserving fingerprints across test selection and exact replay.
	for _, test := range pkg.Registry {
		if test.Kind == "simulation" {
			var bindings []compiler.SimulationBinding
			if adapter != nil {
				bindings = adapter.manifest.Bindings
			}
			return comp.WithSimulation(bindings)
		}
	}
	return comp
}
