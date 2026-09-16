package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

var coldEntryHexWord = regexp.MustCompile(`0x([0-9a-fA-F]{8})(?:#32)?`)

func parseColdEntryHexWords(text string) ([]uint32, error) {
	matches := coldEntryHexWord.FindAllStringSubmatch(text, -1)
	words := make([]uint32, 0, len(matches))
	for _, match := range matches {
		word, err := strconv.ParseUint(match[1], 16, 32)
		if err != nil {
			return nil, err
		}
		words = append(words, uint32(word))
	}
	return words, nil
}

func uniqueDelimitedBlock(text, begin, end string) (string, error) {
	if strings.Count(text, begin) != 1 || strings.Count(text, end) != 1 {
		return "", fmt.Errorf("marker counts for %q/%q are %d/%d, want 1/1",
			begin, end, strings.Count(text, begin), strings.Count(text, end))
	}
	start := strings.Index(text, begin) + len(begin)
	finish := strings.Index(text[start:], end)
	if finish < 0 {
		return "", fmt.Errorf("end marker %q precedes begin marker", end)
	}
	return text[start : start+finish], nil
}

// The exact words stated and kernel-checked by Lean must remain the complete
// nine-word native prefix: DAIFSet followed by eight register writes. This gate
// makes the proof list and executable-code oracle fail closed on mutual drift,
// including the previously skipped first word.
func TestColdEntryRegisterSequenceMatchesNativePrefix(t *testing.T) {
	leanBytes, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "AArch64ColdEntry.lean"))
	if err != nil {
		t.Fatal(err)
	}
	leanBlock, err := uniqueDelimitedBlock(string(leanBytes),
		"OAK_COLD_ENTRY_REGISTER_SEQUENCE_BEGIN",
		"OAK_COLD_ENTRY_REGISTER_SEQUENCE_END")
	if err != nil {
		t.Fatal(err)
	}
	leanWords, err := parseColdEntryHexWords(leanBlock)
	if err != nil {
		t.Fatal(err)
	}

	compilerBytes, err := os.ReadFile(filepath.Join("..", "compiler", "e2e_native_barrier_words_test.go"))
	if err != nil {
		t.Fatal(err)
	}
	prefix := regexp.MustCompile(`(?s)var coldEntryRegisterPrefix = \[\]uint32\{(.*?)\n\}`).FindAllStringSubmatch(string(compilerBytes), -1)
	if len(prefix) != 1 {
		t.Fatalf("native cold-entry prefix block count = %d, want 1", len(prefix))
	}
	nativeWords, err := parseColdEntryHexWords(prefix[0][1])
	if err != nil {
		t.Fatal(err)
	}
	if len(nativeWords) != 9 {
		t.Fatalf("native cold-entry prefix has %d words, want DAIFSet plus 8 writes", len(nativeWords))
	}
	if len(leanWords) != 9 {
		t.Fatalf("Lean cold-entry sequence has %d numeric words, want DAIFSet plus 8 writes", len(leanWords))
	}
	for i := range leanWords {
		if leanWords[i] != nativeWords[i] {
			t.Fatalf("cold-entry prefix word %d = %#08x in Lean, %#08x in native prefix",
				i, leanWords[i], nativeWords[i])
		}
	}
}

// The local Sail composition is generated into Lean and proved equal to
// Oak's fold. Pin its single-pass decoder and the ordered eight component-body
// calls here as a source-level guard against accidentally weakening that seam.
func TestSailColdEntryRegisterSequenceProjection(t *testing.T) {
	projectionBytes, err := os.ReadFile(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	if err != nil {
		t.Fatal(err)
	}
	projection := string(projectionBytes)

	targetBody, err := sailFunctionBody(projection, "system_register_cold_entry_target_pure")
	if err != nil {
		t.Fatal(err)
	}
	compactTarget := strings.Join(strings.Fields(targetBody), "")
	wantTarget := "ifo0==0b1&op1==0b100&CRn==0x1&CRm==0x1&op2==0b000then" +
		"{(true,SystemRegisterWriteTarget_HCR_EL2,Rt)}else" +
		"ifo0==0b1&op1==0b100&CRn==0x2&CRm==0x1&op2==0b000then" +
		"{(true,SystemRegisterWriteTarget_VTTBR_EL2,Rt)}else" +
		"ifo0==0b1&op1==0b100&CRn==0x2&CRm==0x1&op2==0b010then" +
		"{(true,SystemRegisterWriteTarget_VTCR_EL2,Rt)}else" +
		"ifo0==0b1&op1==0b100&CRn==0xE&CRm==0x1&op2==0b000then" +
		"{(true,SystemRegisterWriteTarget_CNTHCTL_EL2,Rt)}else" +
		"ifo0==0b1&op1==0b100&CRn==0xE&CRm==0x0&op2==0b011then" +
		"{(true,SystemRegisterWriteTarget_CNTVOFF_EL2,Rt)}else" +
		"ifo0==0b1&op1==0b100&CRn==0x4&CRm==0x1&op2==0b000then" +
		"{(true,SystemRegisterWriteTarget_SP_EL1,Rt)}else" +
		"ifo0==0b1&op1==0b100&CRn==0x4&CRm==0x0&op2==0b001then" +
		"{(true,SystemRegisterWriteTarget_ELR_EL2,Rt)}else" +
		"ifo0==0b1&op1==0b100&CRn==0x4&CRm==0x0&op2==0b000then" +
		"{(true,SystemRegisterWriteTarget_SPSR_EL2,Rt)}else" +
		"{(false,SystemRegisterWriteTarget_HCR_EL2,Rt)}"
	if compactTarget != wantTarget {
		t.Fatalf("local unified target decoder drifted:\n--- have\n%s\n--- want\n%s",
			compactTarget, wantTarget)
	}

	decodeBody, err := sailFunctionBody(projection, "decode64_cold_entry_system_write_pure")
	if err != nil {
		t.Fatal(err)
	}
	wantDecodeBody := "letRt:bits(5)=slice(op_code,0,5);" +
		"letop2:bits(3)=slice(op_code,5,3);" +
		"letCRm:bits(4)=slice(op_code,8,4);" +
		"letCRn:bits(4)=slice(op_code,12,4);" +
		"letop1:bits(3)=slice(op_code,16,3);" +
		"leto0:bits(1)=slice(op_code,19,1);" +
		"if(op_code&0xFFF00000)==0xD5100000then" +
		"{system_register_cold_entry_target_pure(o0,op1,CRn,CRm,op2,Rt)}else" +
		"{(false,SystemRegisterWriteTarget_HCR_EL2,Rt)}"
	if compact := strings.Join(strings.Fields(decodeBody), ""); compact != wantDecodeBody {
		t.Fatalf("local unified general-MSR decoder drifted:\n--- have\n%s\n--- want\n%s",
			compact, wantDecodeBody)
	}

	sequenceBody, err := sailFunctionBody(projection, "aarch64_cold_entry_register_sequence_at_el2_pure")
	if err != nil {
		t.Fatal(err)
	}
	last := -1
	for _, call := range []string{
		"aarch64_sysregwrite_hcr_el2_pure(false",
		"aarch64_sysregwrite_vttbr_el2_pure(false",
		"aarch64_sysregwrite_vtcr_el2_pure(false",
		"aarch64_sysregwrite_cnthctl_el2_pure(inputs.cnthctl_el2)",
		"aarch64_sysregwrite_cntvoff_el2_pure(false",
		"aarch64_sysregwrite_sp_el1_pure(false",
		"aarch64_sysregwrite_elr_el2_pure(inputs.elr_el2)",
		"aarch64_sysregwrite_spsr_el2_pure(inputs.spsr_el2)",
	} {
		if count := strings.Count(sequenceBody, call); count != 1 {
			t.Fatalf("sequence call %q count = %d, want 1", call, count)
		}
		at := strings.Index(sequenceBody, call)
		if at <= last {
			t.Fatalf("sequence call %q is out of order", call)
		}
		last = at
	}
	for i, target := range []string{
		"HCR_EL2", "VTTBR_EL2", "VTCR_EL2", "CNTHCTL_EL2",
		"CNTVOFF_EL2", "SP_EL1", "ELR_EL2", "SPSR_EL2",
	} {
		want := fmt.Sprintf("write%d = SystemRegisterWriteTarget_%s", i, target)
		if count := strings.Count(sequenceBody, want); count != 1 {
			t.Fatalf("ordered Sail log field %q count = %d, want 1", want, count)
		}
	}
	for _, bit := range []string{"old_state.hcr_el2[42]", "old_state.hcr_el2[45]", "old_state.hcr_el2[27]"} {
		if count := strings.Count(sequenceBody, bit); count != 1 {
			t.Fatalf("old HCR predicate projection %q count = %d, want 1", bit, count)
		}
	}
}
