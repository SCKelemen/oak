package modules

import (
	"strings"
	"testing"
)

// `link <path>` and `framework <Name>` (docs/spec/83-modules.md section
// 4.6) parse in declaration order; operands that could leave the module or
// smuggle flags are rejected at the manifest.
func TestManifestLinkAndFramework(t *testing.T) {
	manifest, err := ParseManifest("module example.com/x\nlink native/libhello.a\nlink build/extra.o // an object\nframework Metal\nframework Foundation\n")
	if err != nil {
		t.Fatal(err)
	}
	if len(manifest.Links) != 2 || manifest.Links[0] != "native/libhello.a" || manifest.Links[1] != "build/extra.o" {
		t.Fatalf("links = %v", manifest.Links)
	}
	if len(manifest.Frameworks) != 2 || manifest.Frameworks[0] != "Metal" || manifest.Frameworks[1] != "Foundation" {
		t.Fatalf("frameworks = %v", manifest.Frameworks)
	}
	rejected := map[string]string{
		"link arity":           "module example.com/x\nlink\n",
		"link absolute":        "module example.com/x\nlink /usr/lib/libc.a\n",
		"link parent segment":  "module example.com/x\nlink ../other/libx.a\n",
		"link dot segment":     "module example.com/x\nlink ./libx.a\n",
		"link empty segment":   "module example.com/x\nlink native//libx.a\n",
		"link shared library":  "module example.com/x\nlink native/libx.so\n",
		"link bare flag":       "module example.com/x\nlink -lfoo\n",
		"link duplicate":       "module example.com/x\nlink native/libx.a\nlink native/libx.a\n",
		"framework arity":      "module example.com/x\nframework\n",
		"framework bad name":   "module example.com/x\nframework Core.Foundation\n",
		"framework duplicate":  "module example.com/x\nframework Metal\nframework Metal\n",
		"framework with flags": "module example.com/x\nframework -framework Metal\n",
	}
	for name, text := range rejected {
		if _, err := ParseManifest(text); err == nil {
			t.Errorf("%s: expected rejection", name)
		}
	}
	if _, err := ParseManifest("module example.com/x\nlink ../x.a\n"); err == nil || !strings.Contains(err.Error(), "link ../x.a") {
		t.Fatalf("the rejection names the directive and operand: %v", err)
	}
}
