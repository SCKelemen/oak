package semir

import "fmt"

// SysRegAccess is the architectural access direction Oak exposes for a system
// register. It is static catalog data; generated code contains no access tag.
type SysRegAccess uint8

const (
	SysRegReadOnly SysRegAccess = iota + 1
	SysRegReadWrite
)

func (a SysRegAccess) CanRead() bool  { return a == SysRegReadOnly || a == SysRegReadWrite }
func (a SysRegAccess) CanWrite() bool { return a == SysRegReadWrite }

// SysRegSpec is one AArch64 system-register contract. v1 deliberately admits
// only 64-bit register transfers used by the EL2/EL1 bootstrap path.
type SysRegSpec struct {
	Name   string
	Asm    string
	Access SysRegAccess
}

func (s SysRegSpec) Legal() bool {
	return s.Name != "" && s.Asm != "" && s.Access.CanRead()
}

func (s SysRegSpec) ReadMember() string  { return "read_" + s.Name }
func (s SysRegSpec) WriteMember() string { return "write_" + s.Name }

func (s SysRegSpec) ReadEffect() (Effect, error) {
	if !s.Legal() || !s.Access.CanRead() {
		return Effect{}, fmt.Errorf("system register %q is not readable", s.Name)
	}
	return Effect{Namespace: "Machine", Name: "SysRegRead", Parameters: []string{s.Name}}, nil
}

func (s SysRegSpec) WriteEffect() (Effect, error) {
	if !s.Legal() || !s.Access.CanWrite() {
		return Effect{}, fmt.Errorf("system register %q is not writable", s.Name)
	}
	return Effect{Namespace: "Machine", Name: "SysRegWrite", Parameters: []string{s.Name}}, nil
}

// Keep this catalog intentionally small and explicit. Adding a register is a
// language change: its privilege/access semantics and backend spelling must be
// reviewed together.
var arm64SysRegs = [...]SysRegSpec{
	{Name: "currentel", Asm: "CurrentEL", Access: SysRegReadOnly},
	{Name: "esr_el2", Asm: "ESR_EL2", Access: SysRegReadOnly},
	{Name: "far_el2", Asm: "FAR_EL2", Access: SysRegReadOnly},
	{Name: "hpfar_el2", Asm: "HPFAR_EL2", Access: SysRegReadOnly},
	{Name: "cntvct_el0", Asm: "CNTVCT_EL0", Access: SysRegReadOnly},
	{Name: "cntpct_el0", Asm: "CNTPCT_EL0", Access: SysRegReadOnly},
	{Name: "cntfrq_el0", Asm: "CNTFRQ_EL0", Access: SysRegReadOnly},
	{Name: "cnthp_ctl_el2", Asm: "CNTHP_CTL_EL2", Access: SysRegReadWrite},
	{Name: "cnthp_cval_el2", Asm: "CNTHP_CVAL_EL2", Access: SysRegReadWrite},

	{Name: "hcr_el2", Asm: "HCR_EL2", Access: SysRegReadWrite},
	{Name: "vttbr_el2", Asm: "VTTBR_EL2", Access: SysRegReadWrite},
	{Name: "vtcr_el2", Asm: "VTCR_EL2", Access: SysRegReadWrite},
	{Name: "cnthctl_el2", Asm: "CNTHCTL_EL2", Access: SysRegReadWrite},
	{Name: "cntvoff_el2", Asm: "CNTVOFF_EL2", Access: SysRegReadWrite},
	{Name: "elr_el2", Asm: "ELR_EL2", Access: SysRegReadWrite},
	{Name: "spsr_el2", Asm: "SPSR_EL2", Access: SysRegReadWrite},
	{Name: "vbar_el2", Asm: "VBAR_EL2", Access: SysRegReadWrite},

	{Name: "cntv_ctl_el0", Asm: "CNTV_CTL_EL0", Access: SysRegReadWrite},
	{Name: "cntv_cval_el0", Asm: "CNTV_CVAL_EL0", Access: SysRegReadWrite},
	{Name: "sp_el1", Asm: "SP_EL1", Access: SysRegReadWrite},
	{Name: "sctlr_el1", Asm: "SCTLR_EL1", Access: SysRegReadWrite},
	{Name: "ttbr0_el1", Asm: "TTBR0_EL1", Access: SysRegReadWrite},
	{Name: "tcr_el1", Asm: "TCR_EL1", Access: SysRegReadWrite},
	{Name: "vbar_el1", Asm: "VBAR_EL1", Access: SysRegReadWrite},
}

// Arm64SysRegs returns the fixed catalog by value. Callers cannot mutate the
// authoritative table and no heap allocation is required to enumerate it.
func Arm64SysRegs() [len(arm64SysRegs)]SysRegSpec { return arm64SysRegs }

func LookupArm64SysRegMember(member string) (SysRegSpec, bool, bool) {
	// returns (spec, found, write)
	for i := range arm64SysRegs {
		s := arm64SysRegs[i]
		if member == s.ReadMember() {
			return s, true, false
		}
		if s.Access.CanWrite() && member == s.WriteMember() {
			return s, true, true
		}
	}
	return SysRegSpec{}, false, false
}
