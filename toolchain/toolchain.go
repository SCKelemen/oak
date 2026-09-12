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
// Freestanding targets always add -ffreestanding -nostdlib and compile to
// a relocatable object.
func Resolve(t target.Target, look Lookup, getenv func(string) string) (Driver, error) {
	if look == nil {
		look = exec.LookPath
	}
	if getenv == nil {
		getenv = os.Getenv
	}
	finish := func(d Driver) (Driver, error) {
		if t.Freestanding() {
			d.Object = true
			d.Args = append(d.Args, "-ffreestanding", "-nostdlib", "-DOAK_FREESTANDING")
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
