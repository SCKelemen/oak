package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/opt"
)

func TestNativeSearchRequiresCostedNativeLane(t *testing.T) {
	for _, arch := range []string{"arm64", "rv64"} {
		report := &opt.Report{}
		search, err := nativeSearch(arch, report)
		if err != nil || search == nil {
			t.Fatalf("nativeSearch(%q) returned %v, %v", arch, search, err)
		}
		if search.Costs == nil || search.Costs.Name() != "static-"+arch {
			t.Fatalf("nativeSearch(%q) has wrong cost model %v", arch, search.Costs)
		}
	}
	for _, arch := range []string{"", "wasm32", "amd64", "native-unknown"} {
		search, err := nativeSearch(arch, &opt.Report{})
		if search != nil || err == nil || !strings.Contains(err.Error(), "no native cost model") {
			t.Fatalf("nativeSearch(%q) returned %v, %v; expected refusal", arch, search, err)
		}
	}
}
