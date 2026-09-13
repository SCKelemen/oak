package compiler

import (
	"bytes"
	"context"
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"
	"time"

	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// Executables linked by the Oak assembler alone (docs/spec/94-assembler.md
// §9): every body lowered natively, the start stub the program's whole
// runtime, no C compiled and nothing external linked. The freestanding
// images run under the system emulators, which exit with the program's
// result (the sifive_test finisher on RISC-V's virt board, semihosting
// SYS_EXIT on AArch64's); the Linux ones under user-mode QEMU where it is
// installed (the CI cross-targets job).

// runImage runs a freestanding executable under a system emulator and
// returns its exit code (-1 when it did not exit).
func runImage(t *testing.T, tgt target.Target, image []byte) int {
	t.Helper()
	var qemu string
	var args []string
	switch tgt.Arch {
	case target.ArchRiscv64:
		qemu, args = "qemu-system-riscv64", []string{"-M", "virt", "-bios", "none"}
	case target.ArchArm64:
		qemu, args = "qemu-system-aarch64", []string{"-M", "virt", "-cpu", "cortex-a57", "-semihosting-config", "enable=on,target=native"}
	default:
		t.Skipf("no system emulator for %s", tgt)
	}
	if _, err := exec.LookPath(qemu); err != nil {
		t.Skipf("%s not present", qemu)
	}
	path := filepath.Join(t.TempDir(), "image.elf")
	if err := os.WriteFile(path, image, 0o755); err != nil {
		t.Fatal(err)
	}
	ctx, cancel := context.WithTimeout(context.Background(), 60*time.Second)
	defer cancel()
	cmd := exec.CommandContext(ctx, qemu, append(args, "-nographic", "-monitor", "none", "-kernel", path)...)
	var out bytes.Buffer
	cmd.Stdout, cmd.Stderr = &out, &out
	err := cmd.Run()
	if ctx.Err() != nil {
		t.Fatalf("%s did not exit (a trap has no handler in the start stub):\n%s", qemu, out.String())
	}
	if err == nil {
		return 0
	}
	if exitErr, isExit := err.(*exec.ExitError); isExit {
		return exitErr.ExitCode()
	}
	t.Fatalf("%s: %v\n%s", qemu, err, out.String())
	return -1
}

var nativeExecCorpus = []struct {
	name, source string
	want         int
}{
	{"integers", nativeProgram, 42},
	{"span_calls", nativeSpanCallProgram, 42},
	{"arrays", nativeRV64ArrayProgram, 42},
	{"records", nativeRecordABIProgram, 42},
	{"unions", nativeADTProgram, 42},
	{"extra", nativeRV64Extra, 7},
}

func TestE2ENativeExecutableUnderQEMU(t *testing.T) {
	skipInShort(t)
	for _, arch := range []string{target.ArchRiscv64, target.ArchArm64} {
		tgt := target.Target{OS: target.OSFreestanding, Arch: arch}
		t.Run(tgt.String(), func(t *testing.T) {
			for _, program := range nativeExecCorpus {
				t.Run(program.name, func(t *testing.T) {
					image, err := New().WithSource("native.oak", program.source).WithTarget(tgt).EmitExecutable().Get()
					if err != nil {
						t.Fatalf("link: %v", err)
					}
					if code := runImage(t, tgt, image); code != program.want {
						t.Fatalf("the executable exited %d, want %d", code, program.want)
					}
				})
			}
		})
	}
}

// A program with a body outside the native subset cannot be linked by the
// Oak assembler: the refusal names the function.
func TestE2ENativeExecutableRefusesCBodies(t *testing.T) {
	// Floating point stays with C on the soft-float freestanding target.
	source := "scale: (x: f64) -> f64 = x * 2.0\n\nmain: (): i32 {\n  scale(1.0) == 2.0 ? 0 | 1\n}\n"
	_, err := New().WithSource("native.oak", source).WithTarget(target.Target{OS: target.OSFreestanding, Arch: target.ArchRiscv64}).EmitExecutable().Get()
	if err == nil || !strings.Contains(err.Error(), "stayed with the C backend") {
		t.Fatalf("a program with C bodies linked natively: %v", err)
	}
}

// The Linux executables run under user-mode QEMU where one is installed.
func TestE2ENativeExecutableLinuxUnderUserQEMU(t *testing.T) {
	for _, arch := range []string{target.ArchRiscv64, target.ArchArm64} {
		tgt := target.Target{OS: target.OSLinux, Arch: arch}
		t.Run(tgt.String(), func(t *testing.T) {
			emulator, err := toolchain.ResolveEmulator(tgt, nil, nil)
			if err != nil {
				t.Skipf("no emulator: %v", err)
			}
			for _, program := range nativeExecCorpus {
				image, err := New().WithSource("native.oak", program.source).WithTarget(tgt).EmitExecutable().Get()
				if err != nil {
					t.Fatalf("%s: link: %v", program.name, err)
				}
				path := filepath.Join(t.TempDir(), program.name)
				if err := os.WriteFile(path, image, 0o755); err != nil {
					t.Fatal(err)
				}
				cmd := exec.Command(emulator.Path, append(append([]string{}, emulator.Args...), path)...)
				out, err := cmd.CombinedOutput()
				code := 0
				if exitErr, isExit := err.(*exec.ExitError); isExit {
					code = exitErr.ExitCode()
				} else if err != nil {
					t.Fatalf("%s: %v\n%s", program.name, err, out)
				}
				if code != program.want {
					t.Fatalf("%s exited %d under %s, want %d\n%s", program.name, code, emulator.Command(), program.want, out)
				}
			}
		})
	}
}
