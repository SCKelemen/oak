package main

import (
	"fmt"
	"regexp"
	"strings"
	"testing"
)

// bv_decide uses Lean's native LRAT checker in this toolchain. Admit only
// the reviewed generated dependencies, not arbitrary native_decide axioms.
var lratNativeAxioms = map[string]bool{
	"propext": true, "Classical.choice": true, "Quot.sound": true,
	"Oak.LRATNativeGuards.rv_fits_width._native.bv_decide.ax_1_5":  true,
	"Oak.LRATNativeGuards.rv_alloc_width._native.bv_decide.ax_1_5": true,
	"Oak.LRATARM64Bytes.fits_result._native.bv_decide.ax_1_13":     true,
	"Oak.LRATARM64Bytes.ls_compare._native.bv_decide.ax_1_6":       true,
	"Oak.LRATARM64Bytes.alloc_result._native.bv_decide.ax_1_13":    true,
	"Oak.RiscVCallExecution.wide_pair._native.bv_decide.ax_1_16":   true,
	"Oak.RiscVCallExecution.wide_pair._native.bv_decide.ax_1_8":    true,
}

func lratAuditNativeAxioms(output string) error {
	pattern := regexp.MustCompile(`(?s)depends on axioms: \[([^\]]*)\]`)
	matches := pattern.FindAllStringSubmatch(output, -1)
	if strings.Count(output, "depends on axioms: [") != len(matches) {
		return fmt.Errorf("unterminated axiom report")
	}
	for _, m := range matches {
		for _, entry := range strings.Split(m[1], ",") {
			name := strings.TrimSpace(entry)
			if !lratNativeAxioms[name] {
				return fmt.Errorf("unexpected native guard axiom: %s", name)
			}
		}
	}
	return nil
}

func TestLRATNativeAxiomAudit(t *testing.T) {
	for _, tc := range []struct {
		report string
		reject bool
	}{
		{"'safe' does not depend on any axioms", false},
		{"'safe' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]", false},
		{"'bad' depends on axioms: [propext,\n sorryAx]", true},
		{"'bad' depends on axioms: [propext,\n arbitrary._native.bv_decide.ax_1_5]", true},
		{"'bad' depends on axioms: [propext,", true},
	} {
		if err := lratAuditNativeAxioms(tc.report); (err != nil) != tc.reject {
			t.Fatalf("audit %q: %v", tc.report, err)
		}
	}
}
