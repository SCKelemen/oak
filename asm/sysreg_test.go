package asm

import (
	"bytes"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"sort"
	"strings"
	"testing"
)

// The system register table (sysregs_gen.go, from Arm's SysReg XML) is
// checked against the host LLVM assembler: every readable register through
// `mrs`, every writable one through `msr`, both assemblers must produce the
// same word wherever both know the name. Registers newer than the host
// LLVM are skipped, never reported as disagreements.
func TestSystemRegistersAgainstLLVM(t *testing.T) {
	llvmMC := findLLVMMC(t)
	var names []string
	for name := range systemRegisterEncodings {
		names = append(names, name)
	}
	sort.Strings(names)
	var texts []string
	for _, name := range names {
		enc := systemRegisterEncodings[name]
		if enc.Read {
			texts = append(texts, "mrs x1, "+name)
		}
		if enc.Write {
			texts = append(texts, "msr "+name+", x1")
		}
	}
	expected := llvmEncode(t, llvmMC, texts)
	agreed, unknown := 0, 0
	var failures []string
	for i, text := range texts {
		word, err := encodeText(t, text)
		if expected[i] == nil {
			unknown++
			continue
		}
		if err != nil {
			failures = append(failures, fmt.Sprintf("  %-32s llvm %x; we fail: %v", text, expected[i], err))
			continue
		}
		if !bytes.Equal(wordBytes(word), expected[i]) {
			failures = append(failures, fmt.Sprintf("  %-32s llvm %x; we %x", text, expected[i], wordBytes(word)))
			continue
		}
		agreed++
	}
	t.Logf("%s: %d registers, %d accesses agree with llvm-mc, %d unknown to it", sysRegRelease, len(names), agreed, unknown)
	if len(failures) > 0 {
		t.Errorf("%d system register accesses disagree:\n%s", len(failures), strings.Join(failures, "\n"))
	}
}

// The checker holds mrs/msr to Arm's register names and access directions.
func TestSystemRegisterChecks(t *testing.T) {
	cases := []struct {
		body string
		want string
	}{
		{"mrs x9, cntvct_el0", ""},
		{"msr vbar_el1, x0", ""},
		{"mrs x9, s3_3_c14_c0_2", ""},
		{"mrs x9, cntvct_el9", "not a system register"},
		{"msr cntvct_el0, x0", "not writable"},
		{"mrs x9, osdtrtx_el1", ""},
	}
	for _, c := range cases {
		unit, errs := ParseUnit("sr.oakasm", "f: (a: u64) -> u64 = {\n  system\n  bind x0 = a\n  clobber x9\n  "+c.body+"\n  ret\n}\n")
		if len(errs) != 0 {
			t.Fatalf("%s: parse: %v", c.body, errs)
		}
		sig, err := parseSignature("f: (a: u64) -> u64")
		if err != nil {
			t.Fatal(err)
		}
		findings := Check(unit.Functions[0], sig, nil)
		got := fmt.Sprint(findings)
		if c.want == "" && len(findings) != 0 {
			t.Errorf("%s: unexpected findings %v", c.body, findings)
		}
		if c.want != "" && !strings.Contains(got, c.want) {
			t.Errorf("%s: want a finding containing %q, got %v", c.body, c.want, findings)
		}
	}
}

// The committed generated tables are what the generators produce from the
// releases under external/ (skipped when a release is absent).
func TestGeneratedTablesCurrent(t *testing.T) {
	generators := []struct {
		name, pkg, glob, out string
	}{
		{"encodings", "./internal/isagen", filepath.Join("..", "..", "external", "isa-a64", "ISA_A64_xml_A_profile-*"), "encodings_gen.go"},
		{"system registers", "./internal/sysreggen", filepath.Join("..", "..", "external", "sysreg", "SysReg_xml_A_profile-*"), "sysregs_gen.go"},
	}
	for _, g := range generators {
		candidates, _ := filepath.Glob(g.glob)
		var dirs []string
		for _, c := range candidates {
			if info, err := os.Stat(c); err == nil && info.IsDir() && !strings.HasSuffix(c, "xhtml") {
				if entries, err := filepath.Glob(filepath.Join(c, "*.xml")); err == nil && len(entries) > 0 {
					dirs = append(dirs, c)
				}
			}
		}
		if len(dirs) == 0 {
			t.Logf("%s: release not present, skipped", g.name)
			continue
		}
		sort.Strings(dirs)
		dir := dirs[len(dirs)-1]
		fresh := filepath.Join(t.TempDir(), g.out)
		cmd := exec.Command("go", "run", g.pkg, "-xml", dir, "-o", fresh)
		var stderr bytes.Buffer
		cmd.Stderr = &stderr
		if err := cmd.Run(); err != nil {
			t.Fatalf("%s: %v\n%s", g.name, err, stderr.String())
		}
		want, err := os.ReadFile(fresh)
		if err != nil {
			t.Fatal(err)
		}
		got, err := os.ReadFile(g.out)
		if err != nil {
			t.Fatal(err)
		}
		if !bytes.Equal(want, got) {
			t.Errorf("%s: %s differs from what the generator produces from %s; rerun the generator", g.name, g.out, filepath.Base(dir))
		}
	}
}

// The registers the OS pilot's kernel adapter moves onto the verified
// assembler (docs/notes/os-language-requests-2026-09.md, R6): MMU enable,
// vector install, and EL0 entry read and write these four.
func TestKernelAdapterSystemRegisters(t *testing.T) {
	for _, name := range []string{"mair_el1", "sp_el0", "elr_el1", "spsr_el1"} {
		enc, known := systemRegisterEncodings[name]
		if !known {
			t.Fatalf("%s is not in the system register table", name)
		}
		if !enc.Read || !enc.Write {
			t.Fatalf("%s must be readable and writable (MRS and MSR): %+v", name, enc)
		}
	}
}
