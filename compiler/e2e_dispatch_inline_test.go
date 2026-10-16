package compiler

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"runtime"
	"testing"
)

// Compile the same short CRC claim shapes as TestDispatchClaimsAreChecked
// through real GCC and Clang. A target-attributed always_inline realization
// fails compilation when the baseline wrapper lacks CRC, before the runner
// can check either the true or the deliberately false claim.
func TestAArch64DispatchLeafCCompilers(t *testing.T) {
	generated, err := New().WithSource("dispatch_inline.oak", `
wrong: (x: u32): u32 dispatch { crc: wrong_realization } = x + u32(1)
wrong_realization: (x: u32): u32 = x + u32(2)
right: (x: u32): u32 dispatch { crc: right_realization } = x * u32(3)
right_realization: (x: u32): u32 = x * u32(3)
`).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
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
			// An alias to the other family must not count as coverage.
			identity := "#if !defined(__GNUC__) || defined(__clang__)\n#error real GCC required\n#endif\n"
			args := []string{"-std=c11", "-ffreestanding", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function"}
			if family == "clang" {
				identity = "#ifndef __clang__\n#error real Clang required\n#endif\n"
				args = append(args, "--target=aarch64-none-elf")
			}
			identity += "#ifndef __aarch64__\n#error AArch64 target required\n#endif\n"
			dir := t.TempDir()
			input := filepath.Join(dir, "claims.c")
			if err := os.WriteFile(input, []byte(identity+generated), 0o600); err != nil {
				t.Fatal(err)
			}
			for _, march := range []string{"armv8-a", "armv8-a+crc"} {
				for _, level := range []string{"-O0", "-O1", "-O2"} {
					for _, checked := range []bool{false, true} {
						label := fmt.Sprintf("%s %s checked=%t", march, level, checked)
						t.Log(label)
						command := append(append([]string{}, args...), "-march="+march, level)
						if checked {
							command = append(command, "-DOAK_CHECK_DISPATCH")
						}
						command = append(command, "-c", input, "-o", filepath.Join(dir, "claims.o"))
						if output, err := exec.Command(cc, command...).CombinedOutput(); err != nil {
							t.Fatalf("%s: compile baseline-to-realization call: %v\n%s\n--- C ---\n%s", label, err, output, generated)
						}
					}
				}
			}
		})
	}
}
