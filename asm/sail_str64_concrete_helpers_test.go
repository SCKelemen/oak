package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

var sailSTRConcreteDeclarations = []struct{ file, kind, name string }{
	{"aarch_types.sail", "enum", "ArchVersion"},
	{"aarch_mem.sail", "register configuration", "__v81_implemented"},
	{"aarch_mem.sail", "register configuration", "__v82_implemented"},
	{"aarch_mem.sail", "register configuration", "__v83_implemented"},
	{"aarch_mem.sail", "register configuration", "__v84_implemented"},
	{"aarch_mem.sail", "register configuration", "__v85_implemented"},
	{"aarch_mem.sail", "val", "HasArchVersion"},
	{"aarch_mem.sail", "function", "HasArchVersion"},
	{"aarch_mem.sail", "val", "HaveNV2Ext"},
	{"aarch_mem.sail", "function", "HaveNV2Ext"},
	{"aarch_mem.sail", "val", "ZeroExtend__0"},
	{"aarch_mem.sail", "function", "ZeroExtend__0"},
}

// Exact original source does not establish old/new configuration semantics:
// the modern export represents these configuration inputs as state registers.
// The Lean rules must require their actual initialization, not infer hardware
// features or a state-independent query from the original pure signature.
func auditSailSTRConcreteHelpers(source string, originals map[string]string) error {
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
			return fmt.Errorf("changed concrete helper declaration: %s %s", kind, name)
		}
		return nil
	}
	for _, d := range sailSTRConcreteDeclarations {
		want, err := sailSTRExecutionDeclaration(originals[d.file], d.kind, d.name)
		if err != nil {
			return err
		}
		if err := exact(d.kind, d.name, want); err != nil {
			return err
		}
	}
	active, err := stripSailComments(source)
	if err != nil {
		return err
	}
	for _, cut := range []struct{ name, local, target, overload string }{
		{"HaveNV2Ext", "oak_memory_HaveNV2Ext", "memory.HaveNV2Ext", "HaveNV2Ext"},
		{"ZeroExtend__0", "oak_instruction_ZeroExtend__0", "boundaries.ZeroExtend__0", "ZeroExtend"},
	} {
		decl, err := sailSTRExecutionDeclaration(originals["aarch_mem.sail"], "val", cut.name)
		if err != nil {
			return err
		}
		marker := "val " + cut.name + " :"
		if strings.Count(decl, marker) != 1 {
			return fmt.Errorf("ambiguous original helper boundary: %s", cut.name)
		}
		want := strings.Replace(decl, marker, "val "+cut.local+` = impure { lean: "`+cut.target+`" } :`, 1)
		if err := exact("val", cut.local, want); err != nil {
			return err
		}
		if err := exact("overload", cut.overload, "overload "+cut.overload+" = {"+cut.local+"}"); err != nil {
			return err
		}
		if regexp.MustCompile(`(?m)^[ \t]*function[ \t]+(?:clause[ \t]+)?` + regexp.QuoteMeta(cut.local) + `(?:[ \t\r\n]|\()`).MatchString(active) {
			return fmt.Errorf("helper callback %s replaced by local implementation", cut.local)
		}
	}
	// Sail resolves the earlier memory-body call through this overload, before
	// the separately retained concrete function is declared. Do not silently
	// turn the old arbitrary boundary theorem into a concrete-helper theorem.
	overload := strings.Index(active, "overload HaveNV2Ext =")
	memory := strings.Index(active, "function aset_Mem ")
	helper := strings.Index(active, "function HaveNV2Ext ")
	if overload < 0 || memory <= overload || helper <= memory {
		return fmt.Errorf("HaveNV2Ext cut/concrete declaration ordering changed")
	}
	return nil
}

func TestSailSTRExecutionConcreteHelpersExactAndMutated(t *testing.T) {
	data, err := os.ReadFile(filepath.Join("..", "spec", "sail", "str_execution.sail"))
	if err != nil {
		t.Fatal(err)
	}
	source := string(data)
	full := map[string]string{
		"aarch_types.sail": readSailSTRExecutionModel(t, "aarch_types.sail"),
		"aarch_mem.sail":   readSailSTRExecutionModel(t, "aarch_mem.sail"),
	}
	originals := map[string]string{}
	for _, d := range sailSTRConcreteDeclarations {
		decl, err := sailSTRExecutionDeclaration(full[d.file], d.kind, d.name)
		if err != nil {
			t.Fatal(err)
		}
		originals[d.file] += decl + "\n"
	}
	if err := auditSailSTRConcreteHelpers(source, originals); err != nil {
		t.Fatal(err)
	}
	mutants := map[string]string{}
	for _, d := range sailSTRConcreteDeclarations {
		decl, err := sailSTRExecutionDeclaration(source, d.kind, d.name)
		if err != nil {
			t.Fatal(err)
		}
		key := d.kind + "_" + d.name
		mutants[key+"_duplicate"] = source + "\n" + decl
		mutants[key+"_commented"] = strings.Replace(source, decl, "/*\n"+decl+"*/\n", 1)
		mutants[key+"_tail"] = strings.Replace(source, decl, strings.TrimSpace(decl)+";\nthrow()\n", 1)
		if d.kind == "register configuration" {
			mutants[key+"_false_default"] = strings.Replace(source, decl, strings.Replace(decl, "= true", "= false", 1), 1)
			mutants[key+"_ordinary_register"] = strings.Replace(source, decl, strings.Replace(decl, "register configuration", "register", 1), 1)
		}
	}
	for _, m := range []sailMemoryMutation{
		{"wrong_nv_version", "HasArchVersion(ARMv8p4)", "HasArchVersion(ARMv8p3)"},
		{"wrong_config_flag", "version == ARMv8p4 & __v84_implemented", "version == ARMv8p4 & __v85_implemented"},
		{"wrong_base_version", "version == ARMv8p0 |", "version == ARMv8p1 |"},
		{"drop_width_assertion", "assert(N >= 'M)", "()"},
		{"reject_equal_width", "assert(N >= 'M)", "assert(N > 'M)"},
		{"reverse_width_guard", "assert(N >= 'M)", "assert(N <= 'M)"},
		{"wrong_padding", "Zeros(N - 'M) @ x", "Zeros(N) @ x"},
		{"reverse_concat", "Zeros(N - 'M) @ x", "x @ Zeros(N - 'M)"},
		{"bypass_nv_cut", "overload HaveNV2Ext = {oak_memory_HaveNV2Ext}", "overload HaveNV2Ext = {HaveNV2Ext}"},
		{"bypass_extension_cut", "overload ZeroExtend = {oak_instruction_ZeroExtend__0}", "overload ZeroExtend = {ZeroExtend__0}"},
		{"misroute_nv_cut", `lean: "memory.HaveNV2Ext"`, `lean: "memory.BigEndian"`},
		{"misroute_extension_cut", `lean: "boundaries.ZeroExtend__0"`, `lean: "boundaries.SignExtend__0"`},
	} {
		mutants[m.name] = strings.Replace(source, m.old, m.replacement, 1)
	}
	for _, name := range []string{"oak_memory_HaveNV2Ext", "oak_instruction_ZeroExtend__0"} {
		decl, err := sailSTRExecutionDeclaration(source, "val", name)
		if err != nil {
			t.Fatal(err)
		}
		mutants[name+"_duplicate"] = source + "\n" + decl
		mutants[name+"_pure"] = strings.Replace(source, decl, strings.Replace(decl, " = impure ", " = pure ", 1), 1)
		mutants[name+"_stub"] = source + "\nfunction " + name + " () = { () }\n"
	}
	nvOverload, err := sailSTRExecutionDeclaration(source, "overload", "HaveNV2Ext")
	if err != nil {
		t.Fatal(err)
	}
	mutants["late_nv_overload"] = strings.Replace(source, nvOverload, "", 1) + "\n" + nvOverload
	for name, mutant := range mutants {
		t.Run(name, func(t *testing.T) {
			if mutant == source {
				t.Fatal("mutation did not change source")
			}
			if err := auditSailSTRConcreteHelpers(mutant, originals); err == nil {
				t.Fatal("changed helper/configuration/cut admitted")
			}
		})
	}
}
