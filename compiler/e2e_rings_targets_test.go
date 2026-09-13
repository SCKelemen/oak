package compiler

import (
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/toolchain"
)

// The rings under the memory refinement layers (docs/spec/69-aarch64-
// memory-refinement.md, 69-riscv-memory-refinement.md): the compiled ring
// operations carry the ISA instructions the refinement chapters assign to
// their orders. Each function is compiled from Oak through C to target
// assembly with clang, and its body must contain the acquire and release
// families — `ldar`/`stlr` on AArch64, `fence` around the accesses on
// RISC-V — and the exclusive or CAS forms where a claim is made. Skips
// without a clang that has both targets.
func ringsTargetAssembly(t *testing.T, targetTriple, march string) string {
	t.Helper()
	clang, err := exec.LookPath("clang")
	if err != nil {
		t.Skip("clang is required to inspect target assembly")
	}
	code, err := New().WithPackageDir(ringsModule(t, ringsThreadedProgram)).EmitC().Get()
	if err != nil {
		t.Fatal(err)
	}
	dir := t.TempDir()
	cPath, sPath := filepath.Join(dir, "rings.c"), filepath.Join(dir, "rings.s")
	if err := os.WriteFile(cPath, []byte(code), 0o644); err != nil {
		t.Fatal(err)
	}
	args := []string{"--target=" + targetTriple, "-march=" + march, "-std=c11", "-O2", "-ffreestanding", "-Wno-parentheses-equality", "-S", cPath, "-o", sPath}
	if out, err := exec.Command(clang, args...).CombinedOutput(); err != nil {
		// Apple's clang has no RISC-V backend: zig's bundled clang does.
		zig, zigErr := exec.LookPath("zig")
		if zigErr != nil {
			t.Skipf("clang cannot compile for %s and zig is absent: %v\n%s", targetTriple, err, out)
		}
		zigArgs := []string{"cc", "--target=" + zigTriple(targetTriple), "-mcpu=" + zigCPU(march), "-std=c11", "-O2", "-ffreestanding", "-Wno-parentheses-equality", "-S", cPath, "-o", sPath}
		if out, err := exec.Command(zig, zigArgs...).CombinedOutput(); err != nil {
			t.Skipf("neither clang nor zig cc compiles for %s: %v\n%s", targetTriple, err, out)
		}
	}
	assembly, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	return strings.ToLower(string(assembly))
}

// zigTriple and zigCPU spell a clang target for zig cc.
func zigTriple(clangTriple string) string {
	switch clangTriple {
	case "riscv64-unknown-none-elf":
		return "riscv64-freestanding-none"
	case "aarch64-none-elf":
		return "aarch64-freestanding-none"
	}
	return clangTriple
}

func zigCPU(march string) string {
	switch march {
	case "rv64gc":
		return "generic_rv64+m+a+f+d+c"
	case "armv8-a":
		return "generic"
	}
	return march
}

func ringsFunctionBody(t *testing.T, assembly, symbol string) string {
	t.Helper()
	label := symbol + ":"
	start := strings.Index(assembly, label)
	if start < 0 {
		t.Fatalf("assembly lacks %s", label)
	}
	rest := assembly[start+len(label):]
	end := strings.Index(rest, ".lfunc_end")
	if end < 0 {
		end = len(rest)
	}
	return rest[:end]
}

func ringsHasInstruction(body string, mnemonics ...string) bool {
	for _, mnemonic := range mnemonics {
		if regexp.MustCompile(`(?m)^\s*`+regexp.QuoteMeta(mnemonic)+`\s`).FindStringIndex(body) != nil {
			return true
		}
	}
	return false
}

func requireRingsInstruction(t *testing.T, body, function string, alternatives ...string) {
	t.Helper()
	if !ringsHasInstruction(body, alternatives...) {
		t.Fatalf("%s lacks %v:\n%s", function, alternatives, body)
	}
}

// AArch64 (baseline ARMv8-A): every release publication is `stlr`, every
// acquire observation `ldar`; the claims of the MPSC, MPMC, and intrusive
// rings use the exclusive pairs (or, under LSE, `cas`/`swp`).
func TestRingsAArch64Refinement(t *testing.T) {
	assembly := ringsTargetAssembly(t, "aarch64-none-elf", "armv8-a")
	for _, fn := range []string{"oak_rings__spsc_upush_u32", "oak_rings__spsc_upop_u32", "oak_rings__mpsc_upush_u32", "oak_rings__mpsc_upop_u32", "oak_rings__mpmc_upush_u32", "oak_rings__mpmc_upop_u32", "oak_rings__intrusive_upush", "oak_rings__intrusive_upop"} {
		body := ringsFunctionBody(t, assembly, fn)
		requireRingsInstruction(t, body, fn, "stlr", "stlxr")
		requireRingsInstruction(t, body, fn, "ldar", "ldaxr")
	}
	for _, fn := range []string{"oak_rings__mpsc_upush_u32", "oak_rings__mpmc_upush_u32", "oak_rings__mpmc_upop_u32"} {
		requireRingsInstruction(t, ringsFunctionBody(t, assembly, fn), fn, "ldxr", "ldaxr", "cas", "casa", "casl", "casal")
	}
	requireRingsInstruction(t, ringsFunctionBody(t, assembly, "oak_rings__intrusive_upush"), "oak_rings__intrusive_upush", "ldaxr", "swpal", "swp", "swpa", "swpl")
}

// RISC-V (rv64gc): the OS-profile acquire is the full fence before the
// load, release the `fence rw,w` before the store; claims are `lr`/`sc`
// pairs and the intrusive exchange an `amoswap` with `.aqrl`.
func TestRingsRISCV64Refinement(t *testing.T) {
	assembly := ringsTargetAssembly(t, "riscv64-unknown-none-elf", "rv64gc")
	for _, fn := range []string{"oak_rings__spsc_upush_u32", "oak_rings__spsc_upop_u32", "oak_rings__mpsc_upush_u32", "oak_rings__mpsc_upop_u32", "oak_rings__mpmc_upush_u32", "oak_rings__mpmc_upop_u32", "oak_rings__intrusive_upush", "oak_rings__intrusive_upop"} {
		requireRingsInstruction(t, ringsFunctionBody(t, assembly, fn), fn, "fence")
	}
	for _, fn := range []string{"oak_rings__mpsc_upush_u32", "oak_rings__mpmc_upush_u32", "oak_rings__mpmc_upop_u32"} {
		requireRingsInstruction(t, ringsFunctionBody(t, assembly, fn), fn, "lr.w", "lr.w.aqrl", "lr.w.aq", "amocas.w", "amocas.w.aqrl")
	}
	requireRingsInstruction(t, ringsFunctionBody(t, assembly, "oak_rings__intrusive_upush"), "oak_rings__intrusive_upush", "amoswap.w.aqrl")
}

// The threaded harness cross-built for the two hosted weak-memory Linux
// targets links statically with pthreads; where a user-mode emulator is
// present (CI installs qemu-user-static) it runs and must print `rings ok`.
// On this project's AArch64 development hosts the native threaded witness
// (TestE2ERingsThreaded) is the same program on real weak-memory hardware.
func TestRingsCrossTargets(t *testing.T) {
	for _, tgt := range []target.Target{{OS: target.OSLinux, Arch: target.ArchRiscv64}, {OS: target.OSLinux, Arch: target.ArchArm64}} {
		t.Run(tgt.String(), func(t *testing.T) {
			drv, err := toolchain.Resolve(tgt, toolchain.Options{}, nil, nil)
			if err != nil || drv.Kind == "host" {
				t.Skipf("no cross compiler for %s (%v)", tgt, err)
			}
			code, err := New().WithPackageDir(ringsModule(t, ringsThreadedProgram)).WithTarget(tgt).EmitC().Get()
			if err != nil {
				t.Fatal(err)
			}
			dir := t.TempDir()
			cPath, bin := filepath.Join(dir, "rings.c"), filepath.Join(dir, "rings")
			if err := os.WriteFile(cPath, []byte(code+ringsHarness), 0o644); err != nil {
				t.Fatal(err)
			}
			args := append(append([]string{}, drv.Args...), "-std=c11", "-O2", "-pthread", "-Wno-parentheses-equality")
			if drv.Static {
				args = append(args, "-static")
			}
			args = append(args, "-o", bin, cPath)
			if out, err := exec.Command(drv.Path, args...).CombinedOutput(); err != nil {
				t.Fatalf("%s: %v\n%s", drv.Command(), err, out)
			}
			emulator, err := toolchain.ResolveEmulator(tgt, nil, nil)
			if err != nil {
				t.Skipf("linked for %s; no emulator to run it (%v)", tgt, err)
			}
			out, err := exec.Command(emulator.Path, append(append([]string{}, emulator.Args...), bin)...).CombinedOutput()
			if err != nil || !strings.Contains(string(out), "rings ok") {
				t.Fatalf("%s under %s: %v\n%s", tgt, emulator.Command(), err, out)
			}
		})
	}
}
