package leansources

import (
	"bytes"
	"strings"
	"testing"
)

func TestEmbeddedClosureCustody(t *testing.T) {
	before := Identity()
	sources := Sources()
	if len(sources) != 41 {
		t.Fatalf("unexpected closure size: %d", len(sources))
	}
	known := map[string]bool{}
	for _, s := range sources {
		if known[s.Path] || !strings.HasSuffix(s.Path, ".lean") || strings.Contains(s.Path, "..") {
			t.Fatalf("bad closure path %q", s.Path)
		}
		known[s.Path] = true
	}
	if !known["Oak/CheckedBundleAudit.lean"] || !known["Oak/BitwiseSourceObjectParity.lean"] {
		t.Fatal("missing root")
	}
	for _, source := range sources {
		for line := range strings.SplitSeq(string(source.Bytes), "\n") {
			if strings.HasPrefix(line, "import ") {
				for _, module := range strings.Fields(strings.TrimPrefix(line, "import ")) {
					if strings.HasPrefix(module, "Oak.") && !known[strings.ReplaceAll(module, ".", "/")+".lean"] {
						t.Fatalf("missing import %s", module)
					}
				}
			}
		}
	}
	original := append([]byte(nil), sources[0].Bytes...)
	sources[0].Bytes[0] ^= 1
	sources[0].Path = "attacker.lean"
	if Identity() != before || !bytes.Equal(Sources()[0].Bytes, original) {
		t.Fatal("caller mutated embedded proof authority")
	}
}
