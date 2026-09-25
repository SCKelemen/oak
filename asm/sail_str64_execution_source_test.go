package asm

import (
	"crypto/sha256"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

// This gate checks complete source declarations, not instruction reachability.
// The earlier STR request gate stops at the STORE arm; this one additionally
// retains the other arms, post-Mem writeback, PostDecode, and feature queries.
// These hashes are of the pinned original model, never of a success stub or
// a handwritten reduced instruction. The exported instruction declaration is
// checked separately against the very same pin; feature helpers stay external
// cut callbacks in that fragment, and are pinned only in the official source.
//
// This is deliberately not a transitive dependency closure. Exception entry
// (AArch64_BranchTargetException), ConstrainUnpredictable/EndOfInstruction,
// CheckSPAlignment/SP, register setters, integer/bit helpers, Mem and its
// translation/tag/exclusive/device routes are not pinned by THIS gate. The
// existing register, syndrome, and memory gates cover their separate seams.
// Non-MTE IMPDEF query configuration inputs are also not pinned here, though
// the complete IMPDEF map body (including its fallback exception) is pinned.
type sailSTRExecutionFunctionPin struct {
	file, name, sha256 string
}

var sailSTRExecutionFunctionPins = []sailSTRExecutionFunctionPin{
	{"aarch64.sail", "memory_single_general_immediate_signed_postidx", "4149a46ca2f7fdf0e97ac3744ab3316086ad9201511dcf798ebbf7dab03e22df"},
	{"aarch64.sail", "__PostDecode", "d95d7cbd8596fbc22228084b102b0de9cd064e4aab4cd52664e05709ffb83cd1"},
	{"aarch64.sail", "BranchTargetCheck", "3eb61e8ae46fb3dd1ffaa6b17cf2182524d310c529cefe16c2407cbb2b5310b1"},
	{"aarch64.sail", "SetNotTagCheckedInstruction", "dd681b5b90ac6d9f731002a224da819808016240bde366d637115f0aa9fa4877"},
	{"aarch64.sail", "AArch64_ExecutingBTIInstr", "70288d4fa1472b58c8dfba423bb3f9e96d7b32651af70eb4028a02c94a1eb84c"},
	{"aarch64.sail", "AArch64_ExecutingBROrBLROrRetInstr", "39f9c3423180a1e977b491a84e7392762d68e84c8b9c688e9b3ca9496faed3aa"},
	{"aarch_mem.sail", "HaveBTIExt", "2805c7ad46b863ecb05196376661e09ff5a108867a0f73bb00ab26a5f2153965"},
	{"aarch_mem.sail", "HaveMTEExt", "a9ef968e85c1dee70ec4df6af9fc916c7745b1239861bb7e1ec7e3faf6d49944"},
	{"aarch_mem.sail", "HasArchVersion", "2adfad63bca6e740d2a968610fb14ccdec63a7768c1cf42ba14f789c169b0d02"},
	{"aarch_mem.sail", "__IMPDEF_boolean", "6e8ae819bd5b17369cef77c6aee870db69d84588294327045a8b94433b61741c"},
	{"aarch_mem.sail", "__IMPDEF_boolean_map", "720bc584ce9cc4ebc2b5b8432a8c04cce08e4591527c377ad5ee130a2debaee1"},
	{"aarch_mem.sail", "UsingAArch32", "ffc9cb56a4875d2931c4417e194f462edf5efe0150904629bbd2ade86331152c"},
	{"aarch_mem.sail", "HaveAnyAArch32", "2fc8514d75fadcfc5f8e3644d33e1b07318c4d451cd57fe71c2aca9a7f93236d"},
	{"aarch_mem.sail", "HighestELUsingAArch32", "95d6a69e7f8240f2ad63d1d8a7c42fb6d4ee0f00615aa3981457f8c196fcd714"},
	{"aarch_mem.sail", "ThisInstr", "e996dd1311352218a8d094d40d2f63d0fe678bbcd6e201d8dee1902b2370654e"},
	{"aarch_mem.sail", "ThisInstrAddr", "bf7983820c87e4063132c64f9ab66658d94bff962dcfbd2b44557c844f4bffd5"},
	{"aarch_mem.sail", "Halted", "4469b2de91691426e8e4082cc47322f62130a2904bd9ef71ac922b1177452aa8"},
}

var sailSTRExecutionCuts = []struct{ file, name string }{
	{"aarch_mem.sail", "HaveMTEExt"},
	{"aarch64.sail", "SetNotTagCheckedInstruction"},
	{"aarch_mem.sail", "ConstrainUnpredictable"},
	{"aarch_mem.sail", "EndOfInstruction"},
	{"aarch64.sail", "CheckSPAlignment"},
	{"aarch64.sail", "aget_SP"},
	{"aarch64.sail", "aset_SP"},
	{"aarch64.sail", "aset_X"},
	{"aarch64.sail", "aset_Mem"},
	{"aarch64.sail", "aget_Mem"},
	{"aarch64.sail", "Prefetch"},
	{"aarch_mem.sail", "SignExtend__0"},
	{"aarch_mem.sail", "ZeroExtend__0"},
}

var sailSTRExecutionOverloads = []struct{ name, text string }{
	{"X", "overload X = {aget_X, aset_X}"},
	{"SP", "overload SP = {aget_SP, aset_SP}"},
	{"Mem", "overload Mem = {aget_Mem, oak_instruction_aset_Mem}"},
	{"SignExtend", "overload SignExtend = {SignExtend__0}"},
	{"ZeroExtend", "overload ZeroExtend = {oak_instruction_ZeroExtend__0}"},
}

// Keep string contents and token boundaries: compactSail alone would erase
// the meaningful spaces in the IMPDEF key "Has MTE extension". This small
// lexical fingerprint is not a Sail parser or a typechecking substitute.
func sailSTRExecutionTokens(source string) (string, error) {
	active, err := stripSailComments(source)
	if err != nil {
		return "", err
	}
	word := func(c byte) bool {
		return c >= 'a' && c <= 'z' || c >= 'A' && c <= 'Z' ||
			c >= '0' && c <= '9' || c == '_' || c == '\''
	}
	operator := func(c byte) bool { return strings.ContainsRune("!#$%&*+-./:<=>?@^|~", rune(c)) }
	var tokens []string
	for at := 0; at < len(active); {
		if strings.ContainsRune(" \t\r\n", rune(active[at])) {
			at++
			continue
		}
		start := at
		if active[at] == '"' {
			at++
			closed := false
			for at < len(active) {
				if active[at] == '\\' {
					at += 2
					continue
				}
				if active[at] == '"' {
					at++
					closed = true
					break
				}
				at++
			}
			if !closed {
				return "", fmt.Errorf("unterminated Sail string")
			}
		} else if word(active[at]) {
			for at < len(active) && word(active[at]) {
				at++
			}
		} else if operator(active[at]) {
			for at < len(active) && operator(active[at]) {
				at++
			}
		} else {
			at++
		}
		tokens = append(tokens, active[start:at])
	}
	return strings.Join(tokens, "\x00"), nil
}

// Return the whole declaration, including any trailing expression after its
// closing brace. The model's top-level declarations begin at column zero.
// Duplicate detection also sees indented copies; no brace-only extraction is
// used. Strings are masked for locating declarations, but not fingerprinting.
func sailSTRExecutionDeclaration(source, kind, name string) (string, error) {
	active, err := stripSailComments(source)
	if err != nil {
		return "", err
	}
	if _, err := sailSTRExecutionTokens(active); err != nil {
		return "", err
	}
	mask := []byte(active)
	inString := false
	for at := 0; at < len(mask); at++ {
		if inString {
			if mask[at] == '\\' && at+1 < len(mask) {
				mask[at], mask[at+1] = ' ', ' '
				at++
				continue
			}
			if mask[at] == '"' {
				inString = false
			}
			if mask[at] != '\n' && mask[at] != '\r' {
				mask[at] = ' '
			}
		} else if mask[at] == '"' {
			inString = true
			mask[at] = ' '
		}
	}
	pattern := regexp.MustCompile(`(?m)^[ \t]*` + regexp.QuoteMeta(kind) + `[ \t]+` +
		regexp.QuoteMeta(name) + `(?:[ \t\r\n]|\()`)
	starts := pattern.FindAllIndex(mask, -1)
	if len(starts) != 1 {
		return "", fmt.Errorf("%s %s declaration count = %d, want 1", kind, name, len(starts))
	}
	start, tail := starts[0][0], starts[0][1]
	next := regexp.MustCompile(`(?m)^(?:val|function|register|type|enum|struct|overload|let|union)[ \t]`).FindIndex(mask[tail:])
	end := len(active)
	if next != nil {
		end = tail + next[0]
	}
	return active[start:end], nil
}

func auditSailSTRExecutionFunction(source string, pin sailSTRExecutionFunctionPin) error {
	signature, err := sailSTRExecutionDeclaration(source, "val", pin.name)
	if err != nil {
		return err
	}
	body, err := sailSTRExecutionDeclaration(source, "function", pin.name)
	if err != nil {
		return err
	}
	canonical, err := sailSTRExecutionTokens(signature + "\n" + body)
	if err != nil {
		return err
	}
	if got := fmt.Sprintf("%x", sha256.Sum256([]byte(canonical))); got != pin.sha256 {
		return fmt.Errorf("%s complete declaration hash = %s, want %s", pin.name, got, pin.sha256)
	}
	return nil
}

func readSailSTRExecutionModel(t *testing.T, file string) string {
	t.Helper()
	contents, err := os.ReadFile(filepath.Join(filepath.Dir(sailArmModel), file))
	if err != nil {
		requireOracle(t, "official STR execution source unavailable: "+err.Error())
	}
	return string(contents)
}

func TestSailArmSTR64ExecutionDeclarationsExactAndMutated(t *testing.T) {
	for _, pin := range sailSTRExecutionFunctionPins {
		t.Run(pin.name, func(t *testing.T) {
			source := readSailSTRExecutionModel(t, pin.file)
			if err := auditSailSTRExecutionFunction(source, pin); err != nil {
				t.Fatal(err)
			}
			for _, kind := range []string{"val", "function"} {
				declaration, err := sailSTRExecutionDeclaration(source, kind, pin.name)
				if err != nil {
					t.Fatal(err)
				}
				mutants := map[string]string{
					"duplicate":          source + "\n" + declaration,
					"indented_duplicate": source + "\n  " + declaration,
					"commented_only":     strings.Replace(source, declaration, "/*\n"+declaration+"\n*/", 1),
					"trailing_effect":    strings.Replace(source, declaration, strings.TrimSpace(declaration)+";\nthrow()\n\n", 1),
				}
				for name, mutant := range mutants {
					t.Run(kind+"_"+name, func(t *testing.T) {
						if err := auditSailSTRExecutionFunction(mutant, pin); err == nil {
							t.Fatal("changed complete declaration was admitted")
						}
					})
				}
				// Inactive duplicate spellings are harmless, unlike missing
				// active declarations. Braces in nested comments are ignored.
				commented := "/* { /* nested */\n" + declaration + "\n} */\n" + source
				if err := auditSailSTRExecutionFunction(commented, pin); err != nil {
					t.Fatalf("inactive declaration changed the source audit: %v", err)
				}
			}
		})
	}
}

func TestSailArmSTR64ExecutionFragmentExactAndMutated(t *testing.T) {
	contents, err := os.ReadFile(filepath.Join("..", "spec", "sail", "str_execution.sail"))
	if err != nil {
		t.Fatal(err)
	}
	source := string(contents)
	for _, pin := range sailSTRExecutionFunctionPins {
		if pin.name != "memory_single_general_immediate_signed_postidx" {
			continue
		}
		if err := auditSailSTRExecutionFunction(source, pin); err != nil {
			t.Fatal(err)
		}
		// The local exported instruction has exactly the same full source
		// pin, with neither callback substitutions nor effect erasure inside
		// this declaration. Dependency val bindings are intentionally cut.
		for _, kind := range []string{"val", "function"} {
			declaration, err := sailSTRExecutionDeclaration(source, kind, pin.name)
			if err != nil {
				t.Fatal(err)
			}
			for name, mutant := range map[string]string{
				"duplicate":       source + "\n" + declaration,
				"commented_only":  strings.Replace(source, declaration, "/*\n"+declaration+"\n*/", 1),
				"trailing_effect": strings.Replace(source, declaration, strings.TrimSpace(declaration)+";\nthrow()\n\n", 1),
			} {
				t.Run(kind+"_"+name, func(t *testing.T) {
					if mutant == source {
						t.Fatal("mutation did not change local instruction")
					}
					if err := auditSailSTRExecutionFunction(mutant, pin); err == nil {
						t.Fatal("changed local instruction was admitted")
					}
				})
			}
		}
		for _, mutation := range []sailMemoryMutation{
			{"feature_query", "if HaveMTEExt() then {", "if false then {"},
			{"skip_mem", "Mem(address, datasize / 8, acctype) = data", "()"},
			{"extra_mem_before_syndrome", "AArch64_SetLSInstructionSyndrome(datasize / 8, false, t, regsize == 64, false)", "Mem(address, datasize / 8, acctype) = data; AArch64_SetLSInstructionSyndrome(datasize / 8, false, t, regsize == 64, false)"},
			{"writeback_guard", "if wback then {", "if true then {"},
			{"writeback_target", "X(n) = address", "X(t) = address"},
		} {
			t.Run(mutation.name, func(t *testing.T) {
				mutant := strings.Replace(source, mutation.old, mutation.replacement, 1)
				if mutant == source {
					t.Fatal("mutation did not change local instruction")
				}
				if err := auditSailSTRExecutionFunction(mutant, pin); err == nil {
					t.Fatal("changed local instruction control flow was admitted")
				}
			})
		}
		return
	}
	t.Fatal("complete original instruction pin missing")
}

func auditSailSTRExecutionCutWiring(source string, originals map[string]string) error {
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
			return fmt.Errorf("local %s %s differs from original boundary contract", kind, name)
		}
		return nil
	}
	active, err := stripSailComments(source)
	if err != nil {
		return err
	}
	for _, cut := range sailSTRExecutionCuts {
		local := sailSTRInstructionCutName(cut.name)
		signature, err := sailSTRExecutionDeclaration(originals[cut.file], "val", cut.name)
		if err != nil {
			return err
		}
		marker := "val " + cut.name + " :"
		if strings.Count(signature, marker) != 1 {
			return fmt.Errorf("unexpected original cut signature: %s", cut.name)
		}
		want := strings.Replace(signature, marker,
			"val "+local+` = impure { lean: "boundaries.`+cut.name+`" } :`, 1)
		if err := exact("val", local, want); err != nil {
			return err
		}
		// No empty, successful, or other local implementation may silently
		// replace an explicit cut; also reject multiple/scattered bodies.
		body := regexp.MustCompile(`(?m)^[ \t]*function[ \t]+(?:clause[ \t]+)?` +
			regexp.QuoteMeta(local) + `(?:[ \t\r\n]|\()`)
		if body.MatchString(active) {
			return fmt.Errorf("explicit cut %s has a local implementation", cut.name)
		}
	}
	for _, overload := range sailSTRExecutionOverloads {
		if err := exact("overload", overload.name, overload.text); err != nil {
			return err
		}
	}
	for _, name := range []string{"aget_X", "MakeLSInstructionSyndrome", "AArch64_SetLSInstructionSyndrome"} {
		for _, kind := range []string{"val", "function"} {
			want, err := sailSTRExecutionDeclaration(originals["aarch64.sail"], kind, name)
			if err != nil {
				return err
			}
			if err := exact(kind, name, want); err != nil {
				return err
			}
		}
	}
	return nil
}

func sailSTRInstructionCutName(name string) string {
	if name == "aset_Mem" {
		return "oak_instruction_aset_Mem"
	}
	if name == "ZeroExtend__0" {
		return "oak_instruction_ZeroExtend__0"
	}
	return name
}

func TestSailArmSTR64ExecutionCutWiringExactAndMutated(t *testing.T) {
	contents, err := os.ReadFile(filepath.Join("..", "spec", "sail", "str_execution.sail"))
	if err != nil {
		t.Fatal(err)
	}
	source := string(contents)
	originals := map[string]string{
		"aarch64.sail":   readSailSTRExecutionModel(t, "aarch64.sail"),
		"aarch_mem.sail": readSailSTRExecutionModel(t, "aarch_mem.sail"),
	}
	if err := auditSailSTRExecutionCutWiring(source, originals); err != nil {
		t.Fatal(err)
	}
	for _, cut := range sailSTRExecutionCuts {
		local := sailSTRInstructionCutName(cut.name)
		declaration, err := sailSTRExecutionDeclaration(source, "val", local)
		if err != nil {
			t.Fatal(err)
		}
		for name, mutant := range map[string]string{
			"wrong_callback":   strings.Replace(source, `"boundaries.`+cut.name+`"`, `"boundaries.aset_Mem_wrong"`, 1),
			"commented_only":   strings.Replace(source, declaration, "/*\n"+declaration+"\n*/", 1),
			"duplicate_val":    source + "\n" + declaration,
			"local_body":       source + "\nfunction " + local + " () = { () }\n",
			"two_local_bodies": source + "\nfunction " + local + " () = { () }\nfunction " + local + " () = { () }\n",
		} {
			t.Run(cut.name+"/"+name, func(t *testing.T) {
				if mutant == source {
					t.Fatal("mutation did not change cut declaration")
				}
				if err := auditSailSTRExecutionCutWiring(mutant, originals); err == nil {
					t.Fatal("changed cut wiring was admitted")
				}
			})
		}
	}
	for _, overload := range sailSTRExecutionOverloads {
		for name, replacement := range map[string]string{
			"wrong_target":   "overload " + overload.name + " = {wrong_callback}",
			"commented_only": "/* " + overload.text + " */",
			"duplicate":      overload.text + "\n" + overload.text,
		} {
			t.Run(overload.name+"/"+name, func(t *testing.T) {
				mutant := strings.Replace(source, overload.text, replacement, 1)
				if mutant == source {
					t.Fatal("mutation did not change overload")
				}
				if err := auditSailSTRExecutionCutWiring(mutant, originals); err == nil {
					t.Fatal("changed overload was admitted")
				}
			})
		}
	}
	for _, mutation := range []sailMemoryMutation{
		{"reduced_store_domain", "8 * 'size >= 0 & 'size in {1, 2, 4, 8, 16}", "8 * 'size >= 0 & 'size in {8}"},
		{"erased_mte_effect", "unit -> bool effect {escape}", "unit -> bool"},
		{"wrong_getter", "slice(_R[n], 0, width)", "slice(_R[0], 0, width)"},
		{"wrong_syndrome", "PSTATE.EL == EL0 | PSTATE.EL == EL1", "true"},
	} {
		t.Run(mutation.name, func(t *testing.T) {
			mutant := strings.Replace(source, mutation.old, mutation.replacement, 1)
			if mutant == source {
				t.Fatal("mutation did not change source")
			}
			if err := auditSailSTRExecutionCutWiring(mutant, originals); err == nil {
				t.Fatal("changed callback contract or concrete dependency was admitted")
			}
		})
	}
}

func TestSailArmSTR64ExecutionControlFlowMutations(t *testing.T) {
	mutations := map[string][]sailMemoryMutation{
		"memory_single_general_immediate_signed_postidx": {
			{"skip_feature_query", "if HaveMTEExt() then {", "if false then {"},
			{"tag_check_argument", "SetNotTagCheckedInstruction((is_load_store & n == 31) & ~(wback))", "SetNotTagCheckedInstruction(true)"},
			{"unknown_rt", "rt_unknown : bool = false;", "rt_unknown : bool = true;"},
			{"offset_direction", "address = address + offset", "address = address - offset"},
			{"wrong_store_register", "data = X(t)", "data = X(n)"},
			{"drop_syndrome", "AArch64_SetLSInstructionSyndrome(datasize / 8, false, t, regsize == 64, false)", "()"},
			{"mem_before_syndrome", "AArch64_SetLSInstructionSyndrome(datasize / 8, false, t, regsize == 64, false)", "Mem(address, datasize / 8, acctype) = data; AArch64_SetLSInstructionSyndrome(datasize / 8, false, t, regsize == 64, false)"},
			{"drop_mem", "Mem(address, datasize / 8, acctype) = data", "()"},
			{"writeback_unconditional", "if wback then {", "if true then {"},
			{"writeback_wrong_target", "X(n) = address", "X(t) = address"},
			{"writeback_postindex", "if postindex then {", "if ~(postindex) then {"},
			{"writeback_extra_effect", "X(n) = address", "X(n) = address; Mem(address, 8, acctype) = Zeros(64)"},
		},
		"__PostDecode": {
			{"skip_bti", "if HaveBTIExt() & ~(UsingAArch32()) then {", "if false then {"},
			{"reverse_query_order", "HaveBTIExt() & ~(UsingAArch32())", "~(UsingAArch32()) & HaveBTIExt()"},
			{"skip_branch_check", "BranchTargetCheck()", "()"},
		},
		"BranchTargetCheck": {
			{"drop_assert", "assert(HaveBTIExt() & ~(UsingAArch32()));", ""},
			{"ignore_guarded_page", "InGuardedPage & PSTATE.BTYPE", "true & PSTATE.BTYPE"},
			{"drop_exception", "AArch64_BranchTargetException(slice(pc, 0, 52))", "()"},
			{"wrong_next_type", "BTypeNext = 0b00", "BTypeNext = 0b01"},
		},
		"SetNotTagCheckedInstruction": {
			{"unconditional", "if unchecked then {", "if true then {"},
			{"wrong_pc", "sp_rel_access_pc = ThisInstrAddr()", "sp_rel_access_pc = Zeros(64)"},
		},
		"HaveBTIExt": {{"wrong_version", "ARMv8p5", "ARMv8p4"}},
		"HaveMTEExt": {
			{"wrong_version", "ARMv8p5", "ARMv8p4"},
			{"constant_feature", `__IMPDEF_boolean("Has MTE extension")`, "true"},
			{"query_string_whitespace", `"Has MTE extension"`, `"HasMTEextension"`},
		},
		"HasArchVersion":   {{"wrong_feature", "version == ARMv8p5 & __v85_implemented", "version == ARMv8p5 & __v84_implemented"}},
		"__IMPDEF_boolean": {{"bypass_map", "__IMPDEF_boolean_map(x)", "true"}},
		"__IMPDEF_boolean_map": {
			{"wrong_mte_input", "return(__mte_implemented)", "return(false)"},
			{"query_string_whitespace", `"Has MTE extension"`, `"HasMTEextension"`},
			{"erase_unknown_query_failure", `throw(Error_Implementation_Defined("Unrecognized IMPLEMENTATION_DEFINED boolean"))`, "return(false)"},
		},
		"UsingAArch32": {
			{"wrong_mode", "PSTATE.nRW == 0b1", "PSTATE.nRW == 0b0"},
			{"drop_assertion", "assert(~(aarch32))", "()"},
		},
		"HaveAnyAArch32":                     {{"wrong_el3_config", "CFG_ID_AA64PFR0_EL1_EL3 == 0x2", "CFG_ID_AA64PFR0_EL1_EL3 == 0x1"}},
		"HighestELUsingAArch32":              {{"constant_mode", "__highest_el_aarch32", "false"}},
		"ThisInstr":                          {{"wrong_instruction", "__currentInstr", "0xf900001f"}},
		"ThisInstrAddr":                      {{"wrong_address", "slice(_PC, 0, 'N)", "slice(_PC, 1, 'N)"}},
		"Halted":                             {{"wrong_status", "0b000001", "0b000011"}},
		"AArch64_ExecutingBTIInstr":          {{"wrong_opcode", "0b1101010100", "0b1101010101"}},
		"AArch64_ExecutingBROrBLROrRetInstr": {{"wrong_opcode", "0b1101011", "0b1101010"}},
	}
	for _, pin := range sailSTRExecutionFunctionPins {
		source := readSailSTRExecutionModel(t, pin.file)
		body, err := sailSTRExecutionDeclaration(source, "function", pin.name)
		if err != nil {
			t.Fatal(err)
		}
		for _, mutation := range mutations[pin.name] {
			t.Run(pin.name+"/"+mutation.name, func(t *testing.T) {
				changed := strings.Replace(body, mutation.old, mutation.replacement, 1)
				if changed == body {
					t.Fatal("mutation did not change the intended function")
				}
				mutant := strings.Replace(source, body, changed, 1)
				if mutant == source {
					t.Fatal("mutation did not change source")
				}
				if err := auditSailSTRExecutionFunction(mutant, pin); err == nil {
					t.Fatal("changed control flow was admitted")
				}
			})
		}
	}
}

func TestSailArmSTR64ExecutionFeatureStateExactAndMutated(t *testing.T) {
	// These are model defaults/types, not a claim about Apple hardware's
	// enabled features. In particular, BTI and MTE default to enabled here.
	declarations := []struct{ file, kind, name, text string }{
		{"aarch_types.sail", "enum", "ArchVersion", "enum ArchVersion = {ARMv8p0, ARMv8p1, ARMv8p2, ARMv8p3, ARMv8p4, ARMv8p5}"},
		{"aarch64.sail", "register", "BTypeNext", "register BTypeNext : bits(2)"},
		{"aarch64.sail", "register", "BTypeCompatible", "register BTypeCompatible : bool"},
		{"aarch_mem.sail", "register", "InGuardedPage", "register InGuardedPage : bool"},
		{"aarch_mem.sail", "register", "__highest_el_aarch32", "register __highest_el_aarch32 : bool"},
		{"aarch_mem.sail", "register", "__currentInstr", "register __currentInstr : bits(32)"},
		{"aarch_mem.sail", "register", "_PC", "register _PC : bits(64)"},
		{"aarch_mem.sail", "register", "EDSCR", "register EDSCR : bits(32)"},
		{"aarch_mem.sail", "register configuration", "sp_rel_access_pc", "register configuration sp_rel_access_pc : bits(64) = Ones(64)"},
	}
	for _, name := range []string{"__v81_implemented", "__v82_implemented", "__v83_implemented", "__v84_implemented", "__v85_implemented", "__mte_implemented"} {
		declarations = append(declarations, struct{ file, kind, name, text string }{
			"aarch_mem.sail", "register configuration", name, "register configuration " + name + " : bool = true"})
	}
	for el := 0; el < 4; el++ {
		name := fmt.Sprintf("CFG_ID_AA64PFR0_EL1_EL%d", el)
		declarations = append(declarations, struct{ file, kind, name, text string }{
			"aarch_mem.sail", "register configuration", name, "register configuration " + name + " : bits(4) = 0x2"})
	}
	for _, declaration := range declarations {
		t.Run(declaration.name, func(t *testing.T) {
			source := readSailSTRExecutionModel(t, declaration.file)
			want, err := sailSTRExecutionTokens(declaration.text)
			if err != nil {
				t.Fatal(err)
			}
			audit := func(source string) error {
				text, err := sailSTRExecutionDeclaration(source, declaration.kind, declaration.name)
				if err != nil {
					return err
				}
				got, err := sailSTRExecutionTokens(text)
				if err != nil {
					return err
				}
				if got != want {
					return fmt.Errorf("changed feature/state declaration: %s", declaration.name)
				}
				return nil
			}
			if err := audit(source); err != nil {
				t.Fatal(err)
			}
			changed := declaration.text + " unexpected_tail"
			if strings.Contains(declaration.text, "= true") {
				changed = strings.Replace(declaration.text, "= true", "= false", 1)
			} else if strings.Contains(declaration.text, "bits(") {
				changed = strings.Replace(declaration.text, "bits(", "bits(1 + ", 1)
			}
			for name, replacement := range map[string]string{
				"changed_value_or_type": changed,
				"commented_only":        "/* " + declaration.text + " */",
				"duplicate":             declaration.text + "\n" + declaration.text,
			} {
				t.Run(name, func(t *testing.T) {
					mutant := strings.Replace(source, declaration.text, replacement, 1)
					if mutant == source {
						t.Fatal("mutation did not change source")
					}
					if err := audit(mutant); err == nil {
						t.Fatal("changed feature/state declaration was admitted")
					}
				})
			}
		})
	}
}

func TestSailArmSTR64ExecutionLexicalFingerprint(t *testing.T) {
	canonical := func(source string) string {
		t.Helper()
		result, err := sailSTRExecutionTokens(source)
		if err != nil {
			t.Fatal(err)
		}
		return result
	}
	if canonical(`f ( "Has MTE extension" ) /* { /* nested */ } */`) != canonical(`f("Has MTE extension")`) {
		t.Fatal("cosmetic whitespace/comments changed fingerprint")
	}
	for _, pair := range [][2]string{
		{`f("Has MTE extension")`, `f("HasMTEextension")`},
		{`if feature`, `iffeature`},
		{`x != y`, `x ! = y`},
		{`f("a\"b")`, `f("a b")`},
	} {
		if canonical(pair[0]) == canonical(pair[1]) {
			t.Fatalf("meaningful token distinction erased: %q and %q", pair[0], pair[1])
		}
	}
	for _, source := range []string{`f("unterminated)`, "/* unterminated"} {
		if _, err := sailSTRExecutionTokens(source); err == nil {
			t.Fatal("unterminated lexical construct accepted")
		}
	}
	// Declaration-shaped text in a quoted string cannot supply a header.
	if _, err := sailSTRExecutionDeclaration("let text = \"\nfunction fake () = {}\n\"\n", "function", "fake"); err == nil {
		t.Fatal("declaration discovered only inside a string")
	}
}
