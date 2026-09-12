// Package target names the platforms Oak compiles for (docs/spec/90-backend.md
// §2a): an operating system and an architecture, spelled `os/arch` as Go
// spells them. The compiler emits one C translation unit whatever the
// target; the target decides which assembler lane applies to `.oakasm`
// units, the companion object's format, and which C compiler the tooling
// drives (package toolchain). Every build is a cross build: the host is
// only the default target.
package target

import (
	"fmt"
	"os"
	"runtime"
	"sort"
	"strings"
)

// Target is one operating system and architecture pair.
type Target struct {
	OS   string
	Arch string
}

// The operating systems and architectures of the supported set.
const (
	OSLinux        = "linux"
	OSDarwin       = "darwin"
	OSFreestanding = "freestanding" // no operating system: a relocatable object the user links with their own startup

	ArchArm64   = "arm64"
	ArchAmd64   = "amd64"
	ArchRiscv64 = "riscv64"
	ArchArm     = "arm"     // 32-bit Arm, Thumb: the Cortex-M microcontrollers (freestanding only)
	ArchRiscv32 = "riscv32" // 32-bit RISC-V microcontrollers (freestanding only)
)

// supported is the closed set of targets the tooling drives. The 64-bit
// members are LP64 (32-bit int, 64-bit long and pointer), the 32-bit
// microcontroller members ILP32 — the two C data models the backend
// admits (docs/spec/92-ffi.md §2.4).
var supported = []Target{
	{OSLinux, ArchArm64}, {OSLinux, ArchAmd64}, {OSLinux, ArchRiscv64},
	{OSDarwin, ArchArm64}, {OSDarwin, ArchAmd64},
	{OSFreestanding, ArchArm64}, {OSFreestanding, ArchAmd64}, {OSFreestanding, ArchRiscv64},
	{OSFreestanding, ArchArm}, {OSFreestanding, ArchRiscv32},
}

// DataModel is the target's C data model as the widths of the
// machine-sized Oak types: (int bits, pointer bits) — ILP32 for the 32-bit
// architectures, LP64 otherwise.
func (t Target) DataModel() (intBits, ptrBits int) {
	if t.Arch == ArchArm || t.Arch == ArchRiscv32 {
		return 32, 32
	}
	return 32, 64
}

// DefaultCPU is the processor a target compiles for when the build names
// none (`-cpu`, OAKCPU): the toolchain's baseline for the hosted targets
// (""), and for the freestanding ones a processor whose defaults match the
// companion object — soft-float RISC-V (`generic_rv64`, `generic_rv32`) and
// the Cortex-M4 for Arm (the most common STM32 core; `-cpu cortex_m0`,
// `cortex_m3`, `cortex_m7`, `cortex_m33` name the others).
func (t Target) DefaultCPU() string {
	if !t.Freestanding() {
		return ""
	}
	switch t.Arch {
	case ArchRiscv64:
		return "generic_rv64"
	case ArchRiscv32:
		return "generic_rv32"
	case ArchArm:
		return "cortex_m4"
	}
	return ""
}

// Supported lists the targets in a fixed order.
func Supported() []Target {
	out := append([]Target(nil), supported...)
	sort.Slice(out, func(i, j int) bool { return out[i].String() < out[j].String() })
	return out
}

// Host is the platform the compiler runs on. It need not be supported
// (a build on such a host must name a target).
func Host() Target { return Target{OS: runtime.GOOS, Arch: runtime.GOARCH} }

func (t Target) String() string { return t.OS + "/" + t.Arch }

// Supported reports membership in the closed set.
func (t Target) Supported() bool {
	for _, s := range supported {
		if s == t {
			return true
		}
	}
	return false
}

// IsHost reports whether the target is the platform the compiler runs on.
func (t Target) IsHost() bool { return t == Host() }

// Parse reads `os/arch`. The empty string is the host.
func Parse(text string) (Target, error) {
	if text == "" {
		return Host(), nil
	}
	os, arch, ok := strings.Cut(text, "/")
	if !ok || os == "" || arch == "" {
		return Target{}, fmt.Errorf("target %q: spell it os/arch, one of %s", text, spellSupported())
	}
	t := Target{OS: os, Arch: arch}
	if !t.Supported() {
		return Target{}, fmt.Errorf("target %s is not supported; one of %s", t, spellSupported())
	}
	return t, nil
}

// FromEnv resolves the target of a build: the flag when given, else the
// OAKOS and OAKARCH variables (each defaulting to the host's component, as
// GOOS and GOARCH do), read through getenv.
func FromEnv(flag string, getenv func(string) string) (Target, error) {
	if flag != "" {
		return Parse(flag)
	}
	if getenv == nil {
		getenv = os.Getenv
	}
	t := Host()
	if v := getenv("OAKOS"); v != "" {
		t.OS = v
	}
	if v := getenv("OAKARCH"); v != "" {
		t.Arch = v
	}
	if t.IsHost() {
		return t, nil
	}
	if !t.Supported() {
		return Target{}, fmt.Errorf("target %s (from OAKOS/OAKARCH) is not supported; one of %s", t, spellSupported())
	}
	return t, nil
}

func spellSupported() string {
	names := make([]string, 0, len(supported))
	for _, t := range Supported() {
		names = append(names, t.String())
	}
	return strings.Join(names, ", ")
}

// AsmArch is the assembler lane of the architecture (docs/spec/94-assembler.md
// §9): "arm64", "rv64", or "" when no lane exists (amd64).
func (t Target) AsmArch() string {
	switch t.Arch {
	case ArchArm64:
		return "arm64"
	case ArchRiscv64:
		return "rv64"
	}
	return ""
}

// MachO reports whether the target's relocatable objects are Mach-O; every
// other target is ELF.
func (t Target) MachO() bool { return t.OS == OSDarwin }

// Freestanding reports a target without an operating system: the build
// produces a relocatable object (`-c`), never an executable.
func (t Target) Freestanding() bool { return t.OS == OSFreestanding }

// StaticLink reports whether executables link statically by default: Linux
// targets do (a binary that runs on any distribution, as Go's do); Darwin
// forbids static libc.
func (t Target) StaticLink() bool { return t.OS == OSLinux }

func (t Target) llvmArch() string {
	switch t.Arch {
	case ArchArm64:
		return "aarch64"
	case ArchAmd64:
		return "x86_64"
	case ArchArm:
		return "thumb" // Cortex-M executes Thumb only
	}
	return t.Arch
}

// ZigTriple is the target as `zig cc --target=` spells it: musl for Linux
// (a hermetic static libc), macos, or freestanding.
func (t Target) ZigTriple() string {
	switch t.OS {
	case OSLinux:
		return t.llvmArch() + "-linux-musl"
	case OSDarwin:
		return t.llvmArch() + "-macos-none"
	}
	if t.Arch == ArchArm {
		return "thumb-freestanding-eabi"
	}
	return t.llvmArch() + "-freestanding-none"
}

// LLVMTriple is the target as `clang --target=` spells it.
func (t Target) LLVMTriple() string {
	switch t.OS {
	case OSLinux:
		return t.llvmArch() + "-unknown-linux-musl"
	case OSDarwin:
		return t.llvmArch() + "-apple-macosx"
	}
	if t.Arch == ArchArm {
		return "thumbv7em-none-eabi"
	}
	return t.llvmArch() + "-unknown-none-elf"
}

// GNUPrefixes are the cross-compiler name prefixes GNU toolchains use for
// the target (`riscv64-linux-gnu-gcc`, `riscv64-elf-gcc`), most specific
// first. Darwin has none.
func (t Target) GNUPrefixes() []string {
	switch t.OS {
	case OSLinux:
		return []string{t.llvmArch() + "-linux-gnu-", t.llvmArch() + "-linux-musl-"}
	case OSFreestanding:
		if t.Arch == ArchArm {
			return []string{"arm-none-eabi-"}
		}
		return []string{t.llvmArch() + "-elf-", t.llvmArch() + "-none-elf-", t.llvmArch() + "-unknown-elf-"}
	}
	return nil
}
