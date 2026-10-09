package semir

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"strings"
	"testing"
)

// These are the catalog attributes used for generated realization prototypes
// and definitions. Compile real extension intrinsics, not just string checks:
// bare target("crc") worked with Clang but broke native GCC builds of hash.
// The native ARM64 gate requires both children to pass, so unavailable tools
// (optional for local development) cannot silently reduce that lane's coverage.
func TestCPUFeatureAttributesCompile(t *testing.T) {
	for _, family := range []string{"gcc", "clang"} {
		t.Run(family, func(t *testing.T) {
			name := family
			if family == "gcc" && (runtime.GOARCH != "arm64" || runtime.GOOS != "linux") {
				name = "aarch64-linux-gnu-gcc"
			}
			cc, err := exec.LookPath(name)
			if err != nil {
				t.Skipf("AArch64 %s compiler unavailable: %v", family, err)
			}
			args := []string{"-std=c11", "-O2", "-ffreestanding", "-Wall", "-Wextra", "-Werror"}
			if family == "clang" {
				args = append(args, "--target=aarch64-none-elf")
			}
			var source strings.Builder
			// In particular, Apple's gcc alias must not stand in for real GCC.
			if family == "gcc" {
				source.WriteString("#if !defined(__GNUC__) || defined(__clang__)\n#error real GCC required\n#endif\n")
			} else {
				source.WriteString("#ifndef __clang__\n#error real Clang required\n#endif\n")
			}
			source.WriteString("#ifndef __aarch64__\n#error AArch64 target required\n#endif\n#include <arm_acle.h>\n#include <arm_neon.h>\n#include <arm_sve.h>\n")
			bodies := map[string]string{
				"crc":  "unsigned crc(unsigned a, unsigned b) { return __crc32cw(a, b); }",
				"sha2": "uint32x4_t sha2(uint32x4_t a, uint32x4_t b) { return vsha256su0q_u32(a, b); }",
				"sve":  "unsigned long sve(void) { return svcntb(); }",
				"sve2": "svuint8_t sve2(svuint8_t a, svuint8_t b, svuint8_t c) { return sveorbt_u8(a, b, c); }",
			}
			for _, feature := range CPUFeatures() {
				if feature.Arch != "arm64" {
					continue
				}
				body, ok := bodies[feature.Name]
				if !ok {
					t.Fatalf("no compile probe for AArch64 feature %s", feature.Name)
				}
				// Exercise both the declaration and the definition, as codegen does.
				fmt.Fprintf(&source, "%s %s;\n%s %s\n", feature.Attribute, strings.SplitN(body, " {", 2)[0], feature.Attribute, body)
			}
			// The +crc attribute must retain unrelated features from a stronger
			// command-line baseline, rather than resetting it to armv8-a.
			crc, _ := LookupCPUFeature("crc")
			fmt.Fprintf(&source, "#ifdef __ARM_FEATURE_DOTPROD\n%s uint32x4_t preserve_dotprod(uint32x4_t a, uint8x16_t b, uint8x16_t c) { return vdotq_u32(a, b, c); }\n#endif\n", crc.Attribute)
			dir := t.TempDir()
			path := filepath.Join(dir, "features.c")
			if err := os.WriteFile(path, []byte(source.String()), 0o600); err != nil {
				t.Fatal(err)
			}
			for _, march := range []string{"armv8-a", "armv8.2-a+dotprod"} {
				command := append(append([]string{}, args...), "-march="+march, "-c", path, "-o", filepath.Join(dir, "features.o"))
				if output, err := exec.Command(cc, command...).CombinedOutput(); err != nil {
					t.Fatalf("%s at %s: %v\n%s\n--- C ---\n%s", family, march, err, output, source.String())
				}
			}
		})
	}
}
