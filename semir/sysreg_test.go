package semir

import "testing"

func TestArm64SysRegCatalogIsLegalAndUnique(t *testing.T) {
	regs := Arm64SysRegs()
	if len(regs) != 28 {
		t.Fatalf("system-register catalog has %d entries, want 28", len(regs))
	}
	seenReg := map[string]bool{}
	seenMember := map[string]bool{}
	for _, reg := range regs {
		if !reg.Legal() {
			t.Fatalf("illegal system-register spec: %+v", reg)
		}
		if seenReg[reg.Name] {
			t.Fatalf("duplicate system-register identity %q", reg.Name)
		}
		seenReg[reg.Name] = true
		if seenMember[reg.ReadMember()] {
			t.Fatalf("duplicate read member %q", reg.ReadMember())
		}
		seenMember[reg.ReadMember()] = true
		if _, err := reg.ReadEffect(); err != nil {
			t.Fatalf("read effect for %q: %v", reg.Name, err)
		}
		if reg.Access.CanWrite() {
			if seenMember[reg.WriteMember()] {
				t.Fatalf("duplicate write member %q", reg.WriteMember())
			}
			seenMember[reg.WriteMember()] = true
			if _, err := reg.WriteEffect(); err != nil {
				t.Fatalf("write effect for %q: %v", reg.Name, err)
			}
		}
	}
}

func TestReadOnlySysRegsHaveNoWriteSurface(t *testing.T) {
	for _, name := range []string{"currentel", "esr_el2", "far_el2", "hpfar_el2", "cntvct_el0", "cntpct_el0", "cntfrq_el0"} {
		if _, found, _ := LookupArm64SysRegMember("write_" + name); found {
			t.Fatalf("read-only register %s unexpectedly exposes a write member", name)
		}
		if _, found, write := LookupArm64SysRegMember("read_" + name); !found || write {
			t.Fatalf("read member for %s missing or misclassified", name)
		}
	}
}

func TestSysRegLookupAllocatesNothing(t *testing.T) {
	allocs := testing.AllocsPerRun(1000, func() {
		reg, found, write := LookupArm64SysRegMember("write_hcr_el2")
		if !found || !write || reg.Name != "hcr_el2" {
			panic("lookup failed")
		}
	})
	if allocs != 0 {
		t.Fatalf("system-register lookup allocated %.2f objects per call; want zero", allocs)
	}
}

// The four registers the OS pilot's kernel adapter needs beyond the EL2
// path (docs/notes/os-language-requests-2026-09.md, R6): the MMU register
// program writes mair_el1; the EL0 entry writes sp_el0, elr_el1 and
// spsr_el1 before ERET. Round one pinned them in the assembler's encoding
// table only; the library catalog is a separate surface and must carry
// them too.
func TestKernelAdapterSysRegsAreInTheLibraryCatalog(t *testing.T) {
	for _, name := range []string{"mair_el1", "sp_el0", "elr_el1", "spsr_el1"} {
		reg, found, write := LookupArm64SysRegMember("write_" + name)
		if !found || !write || reg.Name != name {
			t.Fatalf("arm64.write_%s is missing from the library catalog", name)
		}
		if _, found, write := LookupArm64SysRegMember("read_" + name); !found || write {
			t.Fatalf("arm64.read_%s is missing from the library catalog", name)
		}
	}
}
