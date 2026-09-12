// Package toolchain chooses the C compiler that realizes an Oak build for a
// target (docs/spec/115-tooling.md §1, docs/spec/90-backend.md §2a). Oak
// emits C and drives a compiler; for a build to work from every host, the
// driver is resolved from what the host has, in a fixed order, and the
// result is an argv — an executable path and arguments — that exec runs
// directly, never through a shell.
package toolchain

import (
	"fmt"
	"os"
	"os/exec"
	"strings"

	"github.com/SCKelemen/oak/target"
)

// Driver is a resolved C compiler invocation for one target.
type Driver struct {
	// Kind names how the driver was found: "explicit" (OAK_CC), "host"
	// (cc for the host target), "zig" (zig cc), "clang" (a cross clang),
	// "gnu" (a target-prefixed gcc).
	Kind string
	// Path is the executable (resolved through the lookup), Args the
	// arguments that select the target, before the compilation's own.
	Path string
	Args []string
	// Static adds -static: Linux targets other than the host.
	Static bool
	// Object marks a freestanding build: compile to a relocatable object.
	Object bool
}

// Command spells the driver for diagnostics and cache keys.
func (d Driver) Command() string {
	return strings.Join(append([]string{d.Path}, d.Args...), " ")
}

// Lookup finds executables on the host: exec.LookPath in the tooling, a
// table in tests.
type Lookup func(name string) (string, error)

// Options are the build's attributes beyond the target.
type Options struct {
	// CPU names the processor (`-cpu`, OAKCPU): passed as -mcpu=<name>;
	// "" takes the target's default (target.DefaultCPU).
	CPU string
}

// Resolve chooses the driver for t. The order, first match wins:
//
//  1. OAK_CC — an explicit compiler executable, taken as already targeting
//     t; OAK_CFLAGS adds arguments (split on whitespace). The user's word.
//  2. cc on PATH when t is the host.
//  3. zig on PATH: `zig cc --target=<triple>` — one binary that targets
//     everything and carries musl, so a Linux cross build is static and
//     hermetic.
//  4. clang on PATH: `clang --target=<triple>`, with `--sysroot=$OAK_SYSROOT`
//     for a hosted target (a hosted cross build without a sysroot cannot
//     link, so clang is skipped without one); freestanding needs none.
//  5. A GNU cross compiler by the target's prefixes (`riscv64-linux-gnu-gcc`,
//     `riscv64-elf-gcc`).
//
// Freestanding targets always add -ffreestanding -nostdlib, drop unwind
// tables (no runtime to read them), and compile to a relocatable object.
// A processor (opts.CPU, else the target's default) is passed as -mcpu.
func Resolve(t target.Target, opts Options, look Lookup, getenv func(string) string) (Driver, error) {
	if look == nil {
		look = exec.LookPath
	}
	if getenv == nil {
		getenv = os.Getenv
	}
	cpu := opts.CPU
	if cpu == "" {
		cpu = getenv("OAKCPU")
	}
	if cpu == "" {
		cpu = t.DefaultCPU()
	}
	finish := func(d Driver) (Driver, error) {
		if flag := cpuFlag(d.Kind, t, cpu); flag != "" && d.Kind != "explicit" {
			d.Args = append(d.Args, flag)
		}
		if t.Freestanding() {
			d.Object = true
			d.Args = append(d.Args, "-ffreestanding", "-nostdlib", "-fno-unwind-tables", "-fno-asynchronous-unwind-tables", "-DOAK_FREESTANDING")
		} else if t.StaticLink() && !t.IsHost() {
			d.Static = true
		}
		return d, nil
	}
	if cc := getenv("OAK_CC"); cc != "" {
		path, err := look(cc)
		if err != nil {
			return Driver{}, fmt.Errorf("OAK_CC=%s: %v", cc, err)
		}
		return finish(Driver{Kind: "explicit", Path: path, Args: strings.Fields(getenv("OAK_CFLAGS"))})
	}
	if !t.Supported() {
		return Driver{}, fmt.Errorf("target %s is not supported", t)
	}
	if t.IsHost() {
		if path, err := look("cc"); err == nil {
			return finish(Driver{Kind: "host", Path: path})
		}
	}
	if path, err := look("zig"); err == nil {
		return finish(Driver{Kind: "zig", Path: path, Args: []string{"cc", "--target=" + t.ZigTriple()}})
	}
	if path, err := look("clang"); err == nil {
		args := []string{"--target=" + t.LLVMTriple()}
		if sysroot := getenv("OAK_SYSROOT"); sysroot != "" {
			args = append(args, "--sysroot="+sysroot)
		}
		if t.Freestanding() || getenv("OAK_SYSROOT") != "" || t.IsHost() {
			return finish(Driver{Kind: "clang", Path: path, Args: args})
		}
	}
	for _, prefix := range t.GNUPrefixes() {
		if path, err := look(prefix + "gcc"); err == nil {
			return finish(Driver{Kind: "gnu", Path: path})
		}
	}
	if t.IsHost() {
		return Driver{}, fmt.Errorf("no C compiler (cc, zig, clang) on PATH; use -emit-c to write C instead, or set OAK_CC")
	}
	return Driver{}, fmt.Errorf("no C compiler on this host can target %s: install zig (one compiler for every target), a clang with OAK_SYSROOT pointing at a %s sysroot, or a GNU cross compiler (%s); or set OAK_CC to one that already targets it", t, t, strings.Join(prefixedNames(t), ", "))
}

// cpuFlag spells the processor for the driver: -mcpu=<name> for zig and
// clang (LLVM processor names, `cortex_m4`, `generic_rv64`); GNU gcc spells
// Arm processors with a hyphen (`cortex-m4`) and RISC-V ones as -march
// strings, which the LLVM names are not — so a GNU driver takes the Arm
// spelling and leaves RISC-V to its own defaults ("": no flag).
func cpuFlag(kind string, t target.Target, cpu string) string {
	if cpu == "" {
		return ""
	}
	if kind == "gnu" {
		if t.Arch == target.ArchArm {
			return "-mcpu=" + strings.ReplaceAll(cpu, "_", "-")
		}
		return ""
	}
	return "-mcpu=" + cpu
}

func prefixedNames(t target.Target) []string {
	var names []string
	for _, prefix := range t.GNUPrefixes() {
		names = append(names, prefix+"gcc")
	}
	if len(names) == 0 {
		names = []string{"none for " + t.OS}
	}
	return names
}

// Emulator runs a cross-built executable on the host (docs/spec/90-backend.md
// §2a): an argv prefix — the emulator and its arguments — to which the
// binary and the program's own arguments are appended.
type Emulator struct {
	Kind string // "explicit" (OAK_EMULATOR), "qemu"
	Path string
	Args []string
}

// Command spells the emulator for diagnostics.
func (e Emulator) Command() string {
	return strings.Join(append([]string{e.Path}, e.Args...), " ")
}

// ResolveEmulator chooses how `oak run -target` executes a binary for t.
// The host target needs none (a nil emulator, no error). A foreign Linux
// target runs through `OAK_EMULATOR` (an executable, its arguments from
// `OAK_EMULATOR_ARGS` split on whitespace), else QEMU's user-mode
// emulator by architecture (`qemu-riscv64`, `qemu-aarch64`, `qemu-x86_64`,
// or the `-static` spellings distributions install) — a static musl binary
// needs no sysroot. A foreign Darwin or freestanding target cannot be run
// from the tooling and is refused.
func ResolveEmulator(t target.Target, look Lookup, getenv func(string) string) (*Emulator, error) {
	if look == nil {
		look = exec.LookPath
	}
	if getenv == nil {
		getenv = os.Getenv
	}
	if t.IsHost() {
		return nil, nil
	}
	if name := getenv("OAK_EMULATOR"); name != "" {
		path, err := look(name)
		if err != nil {
			return nil, fmt.Errorf("OAK_EMULATOR=%s: %v", name, err)
		}
		return &Emulator{Kind: "explicit", Path: path, Args: strings.Fields(getenv("OAK_EMULATOR_ARGS"))}, nil
	}
	if t.OS != target.OSLinux {
		if t.Freestanding() {
			return nil, fmt.Errorf("a %s build is a relocatable object for your own startup and machine; run it under your own emulator harness (compiler/e2e_mcu_test.go is the shape)", t)
		}
		return nil, fmt.Errorf("cannot run a %s program on this %s host: no user-mode emulator exists for it (set OAK_EMULATOR to one)", t, target.Host())
	}
	for _, name := range qemuUserNames(t) {
		if path, err := look(name); err == nil {
			return &Emulator{Kind: "qemu", Path: path}, nil
		}
	}
	return nil, fmt.Errorf("cannot run a %s program on this %s host: no user-mode emulator on PATH (install QEMU's user-mode emulators — %s — or set OAK_EMULATOR)", t, target.Host(), strings.Join(qemuUserNames(t), ", "))
}

// qemuUserNames are QEMU's user-mode emulator names for a Linux target.
func qemuUserNames(t target.Target) []string {
	arch := map[string]string{target.ArchArm64: "aarch64", target.ArchAmd64: "x86_64", target.ArchRiscv64: "riscv64"}[t.Arch]
	if arch == "" {
		return nil
	}
	return []string{"qemu-" + arch, "qemu-" + arch + "-static"}
}
