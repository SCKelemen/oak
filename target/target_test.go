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
}
