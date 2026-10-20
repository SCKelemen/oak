package leansources

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"fmt"
	"sort"
	"strings"
	"testing"
)

// Reviewed source identities, not values regenerated from the test input.
const expectedObjectIdentity = "ab2af11d0ae904b63fa3fba54cd2ade4d16f85c52649c851ddae6ac99c09f659"
const expectedImageIdentity = "9060359c9cdba07e6fa81bd1058b8453614861e01ad2b0eb33b3eb0916405208"

// Independently attest the returned source bytes and the runtime build order.
// Every Oak import must already have been built from this same closed source
// inventory; a matching unordered digest alone cannot establish that order.
func auditClosureCustody(sources []Source, domain, expected string) error {
	known := make(map[string][]byte)
	var paths []string
	for _, source := range sources {
		if _, duplicate := known[source.Path]; duplicate ||
			!strings.HasSuffix(source.Path, ".lean") || strings.Contains(source.Path, "..") {
			return fmt.Errorf("invalid or duplicate path %q", source.Path)
		}
		for line := range strings.SplitSeq(string(source.Bytes), "\n") {
			if !strings.HasPrefix(line, "import ") {
				continue
			}
			for _, module := range strings.Fields(strings.TrimPrefix(line, "import ")) {
				if strings.HasPrefix(module, "Oak.") {
					path := strings.ReplaceAll(module, ".", "/") + ".lean"
					if _, built := known[path]; !built {
						return fmt.Errorf("unbuilt import %s in %s", module, source.Path)
					}
				}
			}
		}
		known[source.Path] = source.Bytes
		paths = append(paths, source.Path)
	}
	sort.Strings(paths)
	digest := sha256.New()
	digest.Write([]byte(domain))
	var length [8]byte
	for _, path := range paths {
		binary.BigEndian.PutUint64(length[:], uint64(len(path)))
		digest.Write(length[:])
		digest.Write([]byte(path))
		binary.BigEndian.PutUint64(length[:], uint64(len(known[path])))
		digest.Write(length[:])
		digest.Write(known[path])
	}
	if hex.EncodeToString(digest.Sum(nil)) != expected {
		return fmt.Errorf("source bytes do not match the reviewed closure identity")
	}
	return nil
}

func checkClosureCustodyControls(t *testing.T, sources []Source, domain, expected string) {
	t.Helper()
	if err := auditClosureCustody(sources, domain, expected); err != nil {
		t.Fatal(err)
	}
	const shared = "Oak/ControlFlowPlan.lean"
	index := -1
	for i, source := range sources {
		if source.Path == shared {
			index = i
		}
	}
	if index < 0 {
		t.Fatal("missing shared control-flow dependency")
	}
	clone := func() []Source {
		out := make([]Source, len(sources))
		for i, source := range sources {
			out[i] = Source{source.Path, append([]byte(nil), source.Bytes...)}
		}
		return out
	}
	// Keep the existing exact required-test inventory: these controls execute
	// within both required custody roots, not in optional or unselected tests.
	for _, name := range []string{"removed", "reordered", "mutated", "duplicated"} {
		changed := clone()
		switch name {
		case "removed":
			changed = append(changed[:index], changed[index+1:]...)
		case "reordered":
			dependency := changed[index]
			changed = append(append(changed[:index], changed[index+1:]...), dependency)
		case "mutated":
			// Preserve imports and the import graph; only byte custody can
			// reject this changed transitive dependency.
			changed[index].Bytes = append(changed[index].Bytes, '\n')
		case "duplicated":
			changed = append(changed, changed[index])
		}
		if err := auditClosureCustody(changed, domain, expected); err == nil {
			t.Fatalf("%s shared dependency accepted", name)
		} else {
			t.Logf("%s shared dependency refused: %v", name, err)
		}
	}
}
