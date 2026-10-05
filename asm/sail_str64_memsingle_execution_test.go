package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailSTRMemSingleCuts = []struct{ file, name string }{
	{"aarch_mem.sail", "AArch64_TranslateAddress"},
	{"aarch_mem.sail", "AArch64_Abort"},
	{"aarch64.sail", "ProcessorID"},
	{"aarch64.sail", "ClearExclusiveByAddress"},
	{"aarch_mem.sail", "CreateAccessDescriptor"},
	{"aarch_mem.sail", "AccessIsTagChecked"},
	{"aarch_mem.sail", "TransformTag"},
	{"aarch_mem.sail", "CheckTag"},
	{"aarch_mem.sail", "TagCheckFail"},
	{"aarch_mem.sail", "aset__Mem"},
}

// Whole-declaration fidelity and explicit cuts are necessary, not sufficient,
// for semantic preservation. In particular this does not certify Sail's Lean
// backend, instantiate translation, or connect sequential state to Arm CAT.
func auditSailSTRMemSingleExecution(source string, originals map[string]string) error {
	exact := func(kind, name, want string) error {
		got, err := sailSTRExecutionDeclaration(source, kind, name)
		if err != nil {
			return err
		}
		gotTokens, err := sailSTRExecutionTokens(got)
		if err != nil {
			return err
		}
		wantTokens, err := sailSTRExecutionTokens(want)
		if err != nil {
			return err
		}
		if gotTokens != wantTokens {
			return fmt.Errorf("changed MemSingle declaration: %s %s", kind, name)
		}
		return nil
	}
	for _, entry := range []struct{ file, kind, name string }{
		{"aarch64.sail", "val", "AArch64_aset_MemSingle"},
		{"aarch64.sail", "function", "AArch64_aset_MemSingle"},
		{"aarch_mem.sail", "val", "IsFault"},
		{"aarch_mem.sail", "function", "IsFault"},
		{"aarch_types.sail", "enum", "MemType"},
		{"aarch_types.sail", "enum", "DeviceType"},
		{"aarch_types.sail", "enum", "Fault"},
		{"aarch_types.sail", "struct", "MemAttrHints"},
		{"aarch_types.sail", "struct", "MemoryAttributes"},
		{"aarch_types.sail", "struct", "FullAddress"},
		{"aarch_types.sail", "struct", "FaultRecord"},
		{"aarch_types.sail", "struct", "MPAMinfo"},
		{"aarch_types.sail", "struct", "AddressDescriptor"},
		{"aarch_types.sail", "struct", "AccessDescriptor"},
	} {
		want, err := sailSTRExecutionDeclaration(originals[entry.file], entry.kind, entry.name)
		if err != nil {
			return err
		}
		if err := exact(entry.kind, entry.name, want); err != nil {
			return err
		}
	}
	active, err := stripSailComments(source)
	if err != nil {
		return err
	}
	for _, cut := range sailSTRMemSingleCuts {
		decl, err := sailSTRExecutionDeclaration(originals[cut.file], "val", cut.name)
		if err != nil {
			return err
		}
		marker := "val " + cut.name + " :"
		if strings.Count(decl, marker) != 1 {
			return fmt.Errorf("ambiguous MemSingle boundary: %s", cut.name)
		}
		want := strings.Replace(decl, marker, "val "+cut.name+` = impure { lean: "single.`+cut.name+`" } :`, 1)
		if err := exact("val", cut.name, want); err != nil {
			return err
		}
		if regexp.MustCompile(`(?m)^[ \t]*function[ \t]+(?:clause[ \t]+)?` + regexp.QuoteMeta(cut.name) + `(?:[ \t\r\n]|\()`).MatchString(active) {
			return fmt.Errorf("MemSingle callback %s replaced by a local body", cut.name)
		}
	}
	if err := exact("overload", "_Mem", "overload _Mem = {aset__Mem}"); err != nil {
		return err
	}
	return auditSailSTRMemoryExecution(source, originals)
}

func TestSailSTRExecutionMemSingleExactAndMutated(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "spec", "sail", "str_execution.sail"))
	if err != nil {
		t.Fatal(err)
	}
	source := string(data)
	originals := map[string]string{}
	for _, file := range []string{"aarch64.sail", "aarch_mem.sail", "aarch_types.sail"} {
		originals[file] = readSailSTRExecutionModel(t, file)
	}
	// Resolve every required declaration uniquely in the full upstream files
	// once. Mutants change only the local export: reparsing multi-megabyte
	// originals for each mutant adds cost without adding a new check.
	full := originals
	originals = map[string]string{}
	seen := map[[3]string]bool{}
	retain := func(file, kind, name string) {
		t.Helper()
		key := [3]string{file, kind, name}
		if seen[key] {
			return
		}
		decl, err := sailSTRExecutionDeclaration(full[file], kind, name)
		if err != nil {
			t.Fatal(err)
		}
		originals[file] += decl + "\n"
		seen[key] = true
	}
	for _, name := range []string{"AArch64_aset_MemSingle", "aset_Mem", "aget_X", "MakeLSInstructionSyndrome", "AArch64_SetLSInstructionSyndrome"} {
		for _, kind := range []string{"val", "function"} {
			retain("aarch64.sail", kind, name)
		}
	}
	for _, kind := range []string{"val", "function"} {
		retain("aarch_mem.sail", kind, "IsFault")
	}
	for _, name := range []string{"MemType", "DeviceType", "Fault"} {
		retain("aarch_types.sail", "enum", name)
	}
	for _, name := range []string{"MemAttrHints", "MemoryAttributes", "FullAddress", "FaultRecord", "MPAMinfo", "AddressDescriptor", "AccessDescriptor"} {
		retain("aarch_types.sail", "struct", name)
	}
	for _, cuts := range [][]struct{ file, name string }{sailSTRMemSingleCuts, sailSTRMemoryCuts, sailSTRExecutionCuts} {
		for _, cut := range cuts {
			retain(cut.file, "val", cut.name)
		}
	}
	if err := auditSailSTRMemSingleExecution(source, originals); err != nil {
		t.Fatal(err)
	}
	body, err := sailSTRExecutionDeclaration(source, "function", "AArch64_aset_MemSingle")
	if err != nil {
		t.Fatal(err)
	}
	mutants := map[string]string{}
	for _, m := range []sailMemoryMutation{
		{"drop_size_assertion", "assert(size == 1 | size == 2 | size == 4 | size == 8 | size == 16)", "()"},
		{"drop_alignment_assertion", "assert(address == Align(address, size))", "()"},
		{"wrong_translation_address", "AArch64_TranslateAddress(address, acctype, iswrite, wasaligned, size)", "AArch64_TranslateAddress(0x0000000000000000, acctype, iswrite, wasaligned, size)"},
		{"translation_not_write", "let iswrite = true", "let iswrite = false"},
		{"assume_wasaligned", "acctype, iswrite, wasaligned, size", "acctype, iswrite, true, size"},
		{"ignore_fault", "if IsFault(memaddrdesc)", "if false"},
		{"drop_abort", "AArch64_Abort(address, memaddrdesc.fault)", "()"},
		{"force_abort_to_stop", "AArch64_Abort(address, memaddrdesc.fault)", "AArch64_Abort(address, memaddrdesc.fault); return()"},
		{"ignore_shareability", "if memaddrdesc.memattrs.shareable", "if false"},
		{"wrong_processor", "ProcessorID()", "0"},
		{"wrong_exclusive_size", "memaddrdesc.paddress, ProcessorID(), size", "memaddrdesc.paddress, ProcessorID(), 1"},
		{"wrong_descriptor_type", "CreateAccessDescriptor(acctype)", "CreateAccessDescriptor(AccType_IFETCH)"},
		{"skip_mte", "if HaveMTEExt()", "if false"},
		{"skip_tag_predicate", "AccessIsTagChecked(ZeroExtend(address, 64), acctype)", "false"},
		{"wrong_transform_input", "TransformTag(ZeroExtend(address, 64))", "TransformTag(address)"},
		{"invert_tag_result", "if ~(CheckTag(memaddrdesc, ptag, iswrite))", "if CheckTag(memaddrdesc, ptag, iswrite)"},
		{"drop_tag_failure", "TagCheckFail(ZeroExtend(address, 64), iswrite)", "()"},
		{"force_tag_failure_to_stop", "TagCheckFail(ZeroExtend(address, 64), iswrite)", "TagCheckFail(ZeroExtend(address, 64), iswrite); return()"},
		{"drop_store", "_Mem(memaddrdesc, size, accdesc) = value_name", "()"},
		{"wrong_store_size", "_Mem(memaddrdesc, size, accdesc)", "_Mem(memaddrdesc, 1, accdesc)"},
		{"store_trailing_effect", "return()", "return(); throw()"},
	} {
		changed := strings.Replace(body, m.old, m.replacement, 1)
		mutants[m.name] = strings.Replace(source, body, changed, 1)
	}
	for _, entry := range []struct{ kind, name string }{
		{"val", "AArch64_aset_MemSingle"}, {"function", "AArch64_aset_MemSingle"},
		{"val", "IsFault"}, {"function", "IsFault"},
		{"enum", "MemType"}, {"enum", "DeviceType"}, {"enum", "Fault"},
		{"struct", "MemAttrHints"}, {"struct", "MemoryAttributes"}, {"struct", "FullAddress"},
		{"struct", "FaultRecord"}, {"struct", "MPAMinfo"}, {"struct", "AddressDescriptor"}, {"struct", "AccessDescriptor"},
	} {
		decl, err := sailSTRExecutionDeclaration(source, entry.kind, entry.name)
		if err != nil {
			t.Fatal(err)
		}
		prefix := entry.kind + "_" + entry.name
		mutants[prefix+"_duplicate"] = source + "\n" + decl
		mutants[prefix+"_commented"] = strings.Replace(source, decl, "/*\n"+decl+"*/\n", 1)
	}
	for _, cut := range sailSTRMemSingleCuts {
		decl, err := sailSTRExecutionDeclaration(source, "val", cut.name)
		if err != nil {
			t.Fatal(err)
		}
		mutants[cut.name+"_wrong_callback"] = strings.Replace(source, `"single.`+cut.name+`"`, `"single.wrong"`, 1)
		mutants[cut.name+"_pure"] = strings.Replace(source, decl, strings.Replace(decl, " = impure ", " = pure ", 1), 1)
		mutants[cut.name+"_duplicate"] = source + "\n" + decl
		mutants[cut.name+"_stub"] = source + "\nfunction " + cut.name + " () = { () }\n"
	}
	for _, m := range []sailMemoryMutation{
		{"truncate_pa", "address : bits(52)", "address : bits(48)"},
		{"drop_ns", "NS : bits(1)", "NS : bits(0)"},
		{"widen_tag", "tagged : bool", "tagged : bits(1)"},
		{"wrong_isfault", "addrdesc.fault.typ != Fault_None", "addrdesc.fault.typ == Fault_None"},
		{"bypass_cut", "overload _Mem = {aset__Mem}", "overload _Mem = {oak_instruction_aset_Mem}"},
		{"bypass_single_alias", "overload MemSingle = {oak_memory_aset_MemSingle}", "overload MemSingle = {AArch64_aset_MemSingle}"},
	} {
		mutants[m.name] = strings.Replace(source, m.old, m.replacement, 1)
	}
	for name, mutant := range mutants {
		t.Run(name, func(t *testing.T) {
			if mutant == source {
				t.Fatal("mutation did not change source")
			}
			if err := auditSailSTRMemSingleExecution(mutant, originals); err == nil {
				t.Fatal("changed MemSingle body, types, or wiring admitted")
			}
		})
	}
}
