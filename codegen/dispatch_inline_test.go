package codegen

import (
	"fmt"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/semir"
)

// Even a scalar leaf realization crosses a target boundary: the wrapper
// runs on the baseline and may call it only after selecting its feature.
// The codec hot-helper exception must not override that boundary either.
func TestDispatchRealizationsKeepTargetBoundary(t *testing.T) {
	for _, feature := range semir.CPUFeatures() {
		for _, name := range []string{"realization", "json_digits_at"} {
			t.Run(feature.Name+"/"+name, func(t *testing.T) {
				generated := generateSourceC(t, fmt.Sprintf(`
meaning: (x: u32): u32 dispatch { %s: %s } = x + u32(1)
%s: (x: u32): u32 = x + u32(1)
direct_only: (x: u32): u32 = x + u32(2)
`, feature.Name, name, name))
				signature := "u32 oak_" + name + "( u32 x )"
				if strings.Contains(generated, "OAK_INLINE "+signature) {
					t.Fatal("a feature realization was forced inline across the baseline target boundary")
				}
				if strings.Count(generated, feature.Attribute+" "+signature) != 2 {
					t.Fatal("realization prototype and definition must retain the feature target attribute")
				}
				for _, want := range []string{
					"OAK_INLINE u32 oak_direct_only( u32 x )",
					"if (oak_cpu_features & " + feature.Macro() + ")",
					fmt.Sprintf(`oak_dispatch_divergence( "meaning", %q )`, feature.Name),
				} {
					if !strings.Contains(generated, want) {
						t.Fatalf("generated C lacks %q", want)
					}
				}
			})
		}
	}
}
