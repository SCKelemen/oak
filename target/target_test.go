package target

import (
	"runtime"
	"testing"
)

func TestParseAndEnv(t *testing.T) {
	for _, text := range []string{"linux/riscv64", "linux/arm64", "linux/amd64", "darwin/arm64", "freestanding/riscv64"} {
		tgt, err := Parse(text)
		if err != nil || tgt.String() != text || !tgt.Supported() {
			t.Errorf("Parse(%q) = %v, %v", text, tgt, err)
		}
	}
	for _, bad := range []string{"riscv64", "linux-riscv64", "plan9/amd64", "darwin/riscv64", "linux/"} {
		if _, err := Parse(bad); err == nil {
			t.Errorf("Parse(%q) accepted", bad)
		}
	}
	if tgt, _ := Parse(""); !tgt.IsHost() {
		t.Error("empty spelling is the host")
	}
	env := map[string]string{"OAKARCH": "riscv64", "OAKOS": "linux"}
	getenv := func(k string) string { return env[k] }
	if tgt, err := FromEnv("", getenv); err != nil || tgt.String() != "linux/riscv64" {
		t.Errorf("FromEnv = %v, %v", tgt, err)
	}
	if tgt, err := FromEnv("linux/amd64", getenv); err != nil || tgt.String() != "linux/amd64" {
		t.Errorf("flag over env: %v, %v", tgt, err)
	}
	delete(env, "OAKOS")
	if tgt, err := FromEnv("", getenv); err != nil || tgt.OS != runtime.GOOS || tgt.Arch != "riscv64" {
		if runtime.GOOS == "darwin" {
			// darwin/riscv64 is not a platform: the env is refused.
			if err == nil {
				t.Errorf("darwin/riscv64 accepted")
			}
		} else {
			t.Errorf("OAKARCH alone: %v, %v", tgt, err)
		}
	}
}

func TestSpellings(t *testing.T) {
	rv := Target{OSLinux, ArchRiscv64}
	if rv.ZigTriple() != "riscv64-linux-musl" || rv.LLVMTriple() != "riscv64-unknown-linux-musl" || rv.AsmArch() != "rv64" || rv.MachO() || !rv.StaticLink() {
		t.Errorf("linux/riscv64 spellings: %s %s %s", rv.ZigTriple(), rv.LLVMTriple(), rv.AsmArch())
	}
	mac := Target{OSDarwin, ArchArm64}
	if mac.ZigTriple() != "aarch64-macos-none" || mac.LLVMTriple() != "aarch64-apple-macosx" || !mac.MachO() || mac.StaticLink() || mac.GNUPrefixes() != nil {
		t.Errorf("darwin/arm64 spellings: %s %s", mac.ZigTriple(), mac.LLVMTriple())
	}
	bare := Target{OSFreestanding, ArchRiscv64}
	if !bare.Freestanding() || bare.GNUPrefixes()[0] != "riscv64-elf-" || bare.ZigTriple() != "riscv64-freestanding-none" {
		t.Errorf("freestanding/riscv64 spellings: %v %s", bare.GNUPrefixes(), bare.ZigTriple())
	}
	if (Target{OSLinux, ArchAmd64}).AsmArch() != "" {
		t.Error("amd64 has no assembler lane")
	}
	// The microcontroller members: freestanding only, ILP32, no lane.
	for _, arch := range []string{ArchArm, ArchRiscv32} {
		mcu := Target{OSFreestanding, arch}
		if !mcu.Supported() || (Target{OSLinux, arch}).Supported() || mcu.AsmArch() != "" {
			t.Errorf("%s: supported freestanding only, without a lane", arch)
		}
		if i, p := mcu.DataModel(); i != 32 || p != 32 {
			t.Errorf("%s data model %d/%d, want ILP32", arch, i, p)
		}
	}
	if i, p := rv.DataModel(); i != 32 || p != 64 {
		t.Errorf("linux/riscv64 data model %d/%d, want LP64", i, p)
	}
	arm := Target{OSFreestanding, ArchArm}
	if arm.ZigTriple() != "thumb-freestanding-eabi" || arm.LLVMTriple() != "thumbv7em-none-eabi" || arm.GNUPrefixes()[0] != "arm-none-eabi-" || arm.DefaultCPU() != "cortex_m4" {
		t.Errorf("freestanding/arm spellings: %s %s %v %s", arm.ZigTriple(), arm.LLVMTriple(), arm.GNUPrefixes(), arm.DefaultCPU())
	}
	if bare.DefaultCPU() != "generic_rv64+m" || rv.DefaultCPU() != "" {
		t.Errorf("default cpus: %q %q", bare.DefaultCPU(), rv.DefaultCPU())
	}
}

// CPUFeatures reads the RISC-V extensions of zig-style names and ISA
// strings, with the conservative defaults (docs/spec/94-assembler.md §9).
func TestCPUFeatures(t *testing.T) {
	bare := Target{OS: OSFreestanding, Arch: ArchRiscv64}
	linux := Target{OS: OSLinux, Arch: ArchRiscv64}
	for _, c := range []struct {
		tgt  Target
		cpu  string
		c, v bool
	}{
		{bare, "", false, false}, {bare, "generic_rv64+m", false, false}, {bare, "generic_rv64+m+c", true, false},
		{bare, "generic_rv64+m+a+c+v", true, true}, {bare, "rv64gc", true, false}, {bare, "rv64gcv", true, true},
		{bare, "rv64imv", false, true}, {bare, "sifive_u74", false, false}, {linux, "", true, false},
	} {
		features := c.tgt.CPUFeatures(c.cpu)
		if features["c"] != c.c || features["v"] != c.v {
			t.Errorf("%s %q: c=%v v=%v", c.tgt, c.cpu, features["c"], features["v"])
		}
	}
	if features := (Target{OS: OSLinux, Arch: ArchArm64}).CPUFeatures("neoverse_v2"); len(features) != 0 {
		t.Errorf("arm64 reports RISC-V features: %v", features)
	}
}
