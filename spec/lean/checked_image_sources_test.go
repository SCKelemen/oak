package leansources

import (
	"bytes"
	"crypto/sha256"
	"encoding/hex"
	"strings"
	"testing"
)

func TestImageEmbeddedClosureCustody(t *testing.T) {
	const expectedImageIdentity = "c8c958c509fc4f4cf97471a38a73819b3e88cff6ae56523afb23c8ea29323473"
	if ImageIdentity() != expectedImageIdentity {
		t.Fatal("frozen image proof identity changed")
	}
	if Identity() != "54d04d89ad7e7323e6aff70d88e952e1d1935093844189f8ab3eced09e416c30" {
		t.Fatal("legacy object identity changed")
	}
	sources := ImageSources()
	if len(sources) != 42 {
		t.Fatalf("image closure size %d", len(sources))
	}
	known := map[string]bool{}
	hashes := map[string]string{}
	for _, s := range sources {
		if known[s.Path] || strings.Contains(s.Path, "..") || !strings.HasSuffix(s.Path, ".lean") {
			t.Fatal("bad path")
		}
		for line := range strings.SplitSeq(string(s.Bytes), "\n") {
			if strings.HasPrefix(line, "import ") {
				for _, module := range strings.Fields(strings.TrimPrefix(line, "import ")) {
					if strings.HasPrefix(module, "Oak.") && !known[strings.ReplaceAll(module, ".", "/")+".lean"] {
						t.Fatalf("unbuilt import %s in %s", module, s.Path)
					}
				}
			}
		}
		known[s.Path] = true
		hash := sha256.Sum256(s.Bytes)
		hashes[s.Path] = hex.EncodeToString(hash[:])
	}
	if known["Oak/CheckedBundleAudit.lean"] || known["Oak/BitwiseSourceObjectParity.lean"] {
		t.Fatal("object roots leaked into image closure")
	}
	for path, hash := range map[string]string{
		"Oak/NativeBitwiseImage.lean":            "23547baa9c33065e1a64c8f7dbbd1c8682cfdef3c1d3542da0b1671ea30590fc",
		"Oak/BitwiseSourceImageParity.lean":      "baaa703678adf45c0398892edd4240cf1b9c2ace22f00cda69c6e7ce4e65ab29",
		"Oak/BitwiseSourceImageParityAudit.lean": "aae3a66847ee2793dc1fdaf1c08c54a9e8dbdec55cd972a18c0f426ff7f1db08",
	} {
		if hashes[path] != hash {
			t.Fatalf("frozen image proof changed: %s", path)
		}
	}
	original := append([]byte{}, sources[0].Bytes...)
	sources[0].Bytes[0] ^= 1
	sources[0].Path = "untrusted.lean"
	if ImageIdentity() != expectedImageIdentity || !bytes.Equal(ImageSources()[0].Bytes, original) {
		t.Fatal("mutable image source authority")
	}
}
