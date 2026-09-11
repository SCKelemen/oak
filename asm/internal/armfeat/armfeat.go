// Package armfeat decides which encodings of Arm's A64 ISA XML the Apple
// M-series implements (docs/spec/94-assembler.md §9): Armv8.7-A, the
// extensions LLVM enables for apple-m4, and the Scalable Matrix Extension
// family the M4 has (SME, SME2, SME_F64F64, SME_I16I64) — with streaming
// SVE reached through SME, never non-streaming SVE.
//
// It is shared by the table generator (asm/internal/isagen) and the XML
// audits (asm/isa_xml_test.go) so both read one architecture profile.
package armfeat

import (
	"regexp"
	"strconv"
	"strings"
)

// Present lists the optional features the M-series implements beyond the
// Armv8.7-A base (LLVM's apple-m4 target features, and the SME family).
var Present = map[string]bool{
	"FEAT_SME": true, "FEAT_SME2": true, "FEAT_SME_F64F64": true, "FEAT_SME_I16I64": true,
	"FEAT_AES": true, "FEAT_PMULL": true, "FEAT_SHA1": true, "FEAT_SHA256": true, "FEAT_SHA512": true, "FEAT_SHA3": true,
	"FEAT_CRC32": true, "FEAT_LSE": true, "FEAT_RDM": true, "FEAT_FP16": true, "FEAT_FHM": true, "FEAT_DotProd": true,
	"FEAT_FCMA": true, "FEAT_JSCVT": true, "FEAT_LRCPC": true, "FEAT_LRCPC2": true, "FEAT_PAuth": true, "FEAT_FPAC": true,
	"FEAT_BF16": true, "FEAT_I8MM": true, "FEAT_FlagM": true, "FEAT_FlagM2": true, "FEAT_FRINTTS": true, "FEAT_SB": true,
	"FEAT_SPECRES": true, "FEAT_DIT": true, "FEAT_BTI": true, "FEAT_WFxT": true,
}

// Absent lists optional features of Armv8.x up to 8.7 the M-series does not
// implement, with the reason shown by the audits.
var Absent = map[string]string{
	"FEAT_MTE": "memory tagging", "FEAT_MTE2": "memory tagging", "FEAT_MTE4": "memory tagging", "FEAT_MTE_TAGGED_FAR": "memory tagging", "FEAT_MTETC": "memory tagging",
	"FEAT_SVE": "non-streaming SVE (the M4 reaches SVE only through SME's streaming mode)", "FEAT_SVE2": "non-streaming SVE2",
	"FEAT_LS64": "64-byte loads and stores", "FEAT_LS64_V": "64-byte loads and stores", "FEAT_LS64_ACCDATA": "64-byte loads and stores",
	"FEAT_TME": "transactional memory", "FEAT_RNG": "random number instructions", "FEAT_SM3": "SM3 crypto", "FEAT_SM4": "SM4 crypto",
	"FEAT_SPE": "statistical profiling", "FEAT_TRBE": "trace buffer", "FEAT_BRBE": "branch record buffer", "FEAT_TRF": "self-hosted trace",
	"FEAT_RME": "realm management", "FEAT_XS": "XS barriers and TLBI variants", "FEAT_LRCPC3": "RCpc3",
	"FEAT_HBC": "hinted conditional branches", "FEAT_MOPS": "memory copy and set", "FEAT_CSSC": "common short sequence compression",
	"FEAT_PACQARMA3": "QARMA3", "FEAT_CONSTPACFIELD": "constant PAC field",
	"FEAT_AMUv1": "activity monitors", "FEAT_ECV": "enhanced counter virtualization", "FEAT_HCX": "HCRX_EL2",
	"FEAT_D128": "128-bit descriptors", "FEAT_TLBID": "TLBI domains", "FEAT_TLBIRANGE": "range TLBI", "FEAT_TLBIOS": "outer-shareable TLBI",
	"FEAT_TLBIW": "TLBI VMALL for dirty state", "FEAT_PRFMSLC": "system-level-cache prefetch", "FEAT_ATS1A": "address translation without permission checks",
	"FEAT_OCCMO": "outer cacheable CMOs", "FEAT_PoPS": "point of physical storage", "FEAT_PCDPHINT": "producer-consumer data placement hints",
	"FEAT_PAN": "privileged access never (system register only)", "FEAT_PAN2": "AT S1E1RP/WP", "FEAT_UAO": "user access override (system register only)",
	"FEAT_SSBS":     "MSR SSBS (system register only)",
	"FEAT_FAMINMAX": "famax/famin (v9.5)", "FEAT_LSUI": "unprivileged load/store pairs (v9.6)", "FEAT_LUT": "lookup-table instructions (v9.5)",
}

var versionRe = regexp.MustCompile(`^v(\d+)Ap(\d+)$`)

// scalable reports the SVE/SME-family feature names: those not in Present
// are absent from the M4 whatever architecture version names them.
func scalable(name string) bool {
	for _, prefix := range []string{"FEAT_SVE", "FEAT_SME", "FEAT_SSVE", "FEAT_F32MM", "FEAT_F64MM", "FEAT_FP8", "FEAT_SVE_"} {
		if strings.HasPrefix(name, prefix) {
			return true
		}
	}
	return false
}

// versionAdmitted evaluates an arch_variant name — `v8Ap2`, `v9Ap3`,
// `(v8Ap2 && PROFILE_A) || (v9Ap2 && PROFILE_A)` — as whether some named
// version is one the M-series implements (≤ 8.7). An empty name admits.
func versionAdmitted(name string) bool {
	name = strings.TrimSpace(name)
	if name == "" {
		return true
	}
	return eval(name, func(atom string) bool {
		if m := versionRe.FindStringSubmatch(atom); m != nil {
			major, _ := strconv.Atoi(m[1])
			minor, _ := strconv.Atoi(m[2])
			return major < 8 || (major == 8 && minor <= 7)
		}
		return true // PROFILE_A and the like
	})
}

// Has reports whether the M-series has an arch_variant: its feature
// expression (`FEAT_SVE || FEAT_SME`, `FEAT_SME2 && (sz == '0' ||
// FEAT_SME_I16I64)`) holds, where a feature holds when Present names it,
// fails when Absent or the scalable family names it, and otherwise holds
// when the variant's architecture version is one the M-series implements.
func Has(variantName, featureExpr string) bool {
	admitted := versionAdmitted(variantName)
	featureExpr = strings.TrimSpace(featureExpr)
	if featureExpr == "" {
		return admitted
	}
	return eval(featureExpr, func(atom string) bool {
		if !strings.HasPrefix(atom, "FEAT_") {
			return true // field conditions such as sz == '0', PROFILE_A
		}
		if Present[atom] {
			return true
		}
		if _, absent := Absent[atom]; absent || scalable(atom) {
			return false
		}
		return admitted
	})
}

// eval evaluates a boolean expression of atoms joined by `||`, `&&`, and
// parentheses. Comparison atoms (`sz == '0'`) are passed whole.
func eval(expr string, atom func(string) bool) bool {
	p := &parser{s: strings.NewReplacer("&amp;", "&").Replace(expr), atom: atom}
	v := p.or()
	return v
}

type parser struct {
	s    string
	i    int
	atom func(string) bool
}

func (p *parser) skip() {
	for p.i < len(p.s) && p.s[p.i] == ' ' {
		p.i++
	}
}

func (p *parser) or() bool {
	v := p.and()
	for {
		p.skip()
		if strings.HasPrefix(p.s[p.i:], "||") {
			p.i += 2
			w := p.and()
			v = v || w
			continue
		}
		return v
	}
}

func (p *parser) and() bool {
	v := p.unit()
	for {
		p.skip()
		if strings.HasPrefix(p.s[p.i:], "&&") {
			p.i += 2
			w := p.unit()
			v = v && w
			continue
		}
		return v
	}
}

func (p *parser) unit() bool {
	p.skip()
	if p.i < len(p.s) && p.s[p.i] == '(' {
		p.i++
		v := p.or()
		p.skip()
		if p.i < len(p.s) && p.s[p.i] == ')' {
			p.i++
		}
		return v
	}
	start := p.i
	for p.i < len(p.s) && p.s[p.i] != '(' && p.s[p.i] != ')' && !strings.HasPrefix(p.s[p.i:], "||") && !strings.HasPrefix(p.s[p.i:], "&&") {
		p.i++
	}
	return p.atom(strings.TrimSpace(p.s[start:p.i]))
}
