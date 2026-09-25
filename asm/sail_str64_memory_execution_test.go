package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailSTRMemoryCuts = []struct{ file, name string }{
	{"aarch_mem.sail", "HaveNV2Ext"},
	{"aarch64.sail", "BigEndian"},
	{"aarch_mem.sail", "BigEndianReverse"},
	{"aarch64.sail", "AArch64_CheckAlignment"},
	{"aarch_mem.sail", "Align__1"},
	{"aarch64.sail", "AArch64_aset_MemSingle"},
}

// This audits exact source retention and closure wiring, not translation,
// callback refinement, architectural events, or a memory-ordering theorem.
func auditSailSTRMemoryExecution(source string, originals map[string]string) error {
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
			return fmt.Errorf("changed memory declaration: %s %s", kind, name)
		}
		return nil
	}
	for _, kind := range []string{"val", "function"} {
		want, err := sailSTRExecutionDeclaration(originals["aarch64.sail"], kind, "aset_Mem")
		if err != nil {
			return err
		}
		if err := exact(kind, "aset_Mem", want); err != nil {
			return err
		}
	}
	if err := exact("register", "SCTLR_EL2", "register SCTLR_EL2 : bits(64)"); err != nil {
		return err
	}
	active, err := stripSailComments(source)
	if err != nil {
		return err
	}
	for _, cut := range sailSTRMemoryCuts {
		original, err := sailSTRExecutionDeclaration(originals[cut.file], "val", cut.name)
		if err != nil {
			return err
		}
		marker := "val " + cut.name + " :"
		if strings.Count(original, marker) != 1 {
			return fmt.Errorf("ambiguous original memory boundary: %s", cut.name)
		}
		want := strings.Replace(original, marker, "val "+cut.name+` = impure { lean: "memory.`+cut.name+`" } :`, 1)
		if err := exact("val", cut.name, want); err != nil {
			return err
		}
		if regexp.MustCompile(`(?m)^[ \t]*function[ \t]+(?:clause[ \t]+)?` + regexp.QuoteMeta(cut.name) + `(?:[ \t\r\n]|\()`).MatchString(active) {
			return fmt.Errorf("memory callback %s was replaced with a local body", cut.name)
		}
	}
	for _, binding := range []struct{ name, body string }{
		{"Align", "overload Align = {Align__1}"},
		{"MemSingle", "overload MemSingle = {AArch64_aset_MemSingle}"},
		{"Mem", "overload Mem = {aget_Mem, oak_instruction_aset_Mem}"},
	} {
		if err := exact("overload", binding.name, binding.body); err != nil {
			return err
		}
	}
	return auditSailSTRExecutionCutWiring(source, originals)
}

func TestSailSTRExecutionMemoryExactAndMutated(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "spec", "sail", "str_execution.sail"))
	if err != nil {
		t.Fatal(err)
	}
	source := string(data)
	originals := map[string]string{
		"aarch64.sail":   readSailSTRExecutionModel(t, "aarch64.sail"),
		"aarch_mem.sail": readSailSTRExecutionModel(t, "aarch_mem.sail"),
	}
	// Independently retain the existing upstream function pin as well as
	// the new complete-declaration comparison (which includes trailing code).
	requirePinnedSailFunction(t, pinnedSailFunction{
		name: "aset_Mem", source: originals["aarch64.sail"],
		header:     "valaset_Mem:forall'size,8*'size>=0&'sizein{1,2,4,8,16}.(bits(64),int('size),AccType,bits(8*'size))->uniteffect{escape,rmem,rreg,undef,wmem,wreg}functionaset_Mem(address,size,acctype,value_name__arg)={",
		bodySHA256: "a4eb17ddec75f15fad56f8802ab7d5dba226ab37df2426b8f708fe713cfecf7c",
	})
	if err := auditSailSTRMemoryExecution(source, originals); err != nil {
		t.Fatal(err)
	}
	mutants := map[string]string{}
	for _, mutation := range []sailMemoryMutation{
		{"skip_nv2_query", "HaveNV2Ext()", "false"},
		{"skip_endian_query", "| BigEndian()", "| false"},
		{"wrong_register_bit", "SCTLR_EL2[25]", "SCTLR_EL2[24]"},
		{"skip_conversion", "value_name = BigEndianReverse(value_name)", "value_name = value_name"},
		{"assume_alignment", "aligned = AArch64_CheckAlignment(address, size, acctype, iswrite)", "aligned = true"},
		{"alignment_read_not_write", "let iswrite = true;", "let iswrite = false;"},
		{"wrong_atomic_guard", "if ~(atomic) then {", "if atomic then {"},
		{"drop_first_byte", "MemSingle(address, 1, acctype, aligned) = slice(value_name, 0, 8)", "()"},
		{"skip_unpredictable", "c = ConstrainUnpredictable(Unpredictable_DEVPAGE2)", "c = Constraint_NONE"},
		{"reverse_byte_order", "address + i", "address - i"},
		{"short_split", "(size - 1)", "(size - 2)"},
		{"wrong_whole_value_size", "MemSingle(address, size, acctype, aligned) = value_name", "MemSingle(address, 1, acctype, aligned) = slice(value_name, 0, 8)"},
		{"instruction_cut_bypassed", "overload Mem = {aget_Mem, oak_instruction_aset_Mem}", "overload Mem = {aget_Mem, aset_Mem}"},
		{"wrong_mem_single", "overload MemSingle = {AArch64_aset_MemSingle}", "overload MemSingle = {oak_instruction_aset_Mem}"},
		{"wrong_register_width", "register SCTLR_EL2 : bits(64)", "register SCTLR_EL2 : bits(32)"},
	} {
		mutants[mutation.name] = strings.Replace(source, mutation.old, mutation.replacement, 1)
	}
	for _, kind := range []string{"val", "function"} {
		decl, err := sailSTRExecutionDeclaration(source, kind, "aset_Mem")
		if err != nil {
			t.Fatal(err)
		}
		mutants[kind+"_duplicate"] = source + "\n" + decl
		mutants[kind+"_commented"] = strings.Replace(source, decl, "/*\n"+decl+"*/\n", 1)
		mutants[kind+"_trailing_effect"] = strings.Replace(source, decl, strings.TrimSpace(decl)+";\nthrow()\n", 1)
	}
	for _, cut := range sailSTRMemoryCuts {
		decl, err := sailSTRExecutionDeclaration(source, "val", cut.name)
		if err != nil {
			t.Fatal(err)
		}
		mutants[cut.name+"_wrong_callback"] = strings.Replace(source, `"memory.`+cut.name+`"`, `"memory.wrong"`, 1)
		mutants[cut.name+"_duplicate"] = source + "\n" + decl
		mutants[cut.name+"_local_stub"] = source + "\nfunction " + cut.name + " () = { () }\n"
	}
	for name, mutant := range mutants {
		t.Run(name, func(t *testing.T) {
			if mutant == source {
				t.Fatal("mutation did not change source")
			}
			if err := auditSailSTRMemoryExecution(mutant, originals); err == nil {
				t.Fatal("changed retained memory body or callback wiring admitted")
			}
		})
	}
}
