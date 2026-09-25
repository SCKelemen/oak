//go:build ignore

// Regenerate the original-instruction / explicit-callee-boundary slice.
// Run from any directory: go run spec/sail/str_execution_regen.go [--output-dir DIR].
package main

import (
	"context"
	"crypto/sha256"
	"flag"
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"runtime"
	"strings"
	"time"
)

const instruction = "memory_single_general_immediate_signed_postidx"

func must(err error) {
	if err != nil {
		panic(err)
	}
}

func read(path string) string {
	b, err := os.ReadFile(path)
	must(err)
	return string(b)
}

func replaceOne(s, from, to string) string {
	if strings.Count(s, from) != 1 {
		panic(fmt.Sprintf("expected one occurrence of %q", from))
	}
	return strings.Replace(s, from, to, 1)
}

// Sail 0.20.2 preserves short-circuiting in its interpreter/Lem backend, but
// its Lean exporter emits nested actions in Boolean operands; Lean lifts
// those actions eagerly. Normalize exactly these three audited expressions.
// The whole raw output pin below makes additional effectful sites fail closed.
const rawSyndromeCondition = `if ((((← readReg PSTATE).EL == EL0) || ((← readReg PSTATE).EL == EL1)) : Bool)`

const guardedSyndromeCondition = `if ((← do
    if ((← readReg PSTATE).EL == EL0) then pure true
    else pure ((← readReg PSTATE).EL == EL1)) : Bool)`

const rawMemoryCondition = `if (((((← (memory.HaveNV2Ext ())) && (acctype == AccType_NV2REGISTER)) && ((BitVec.join1 [(BitVec.access
                 (← readReg SCTLR_EL2) 25)]) == 1#1)) || (← (memory.BigEndian ()))) : Bool)`

const guardedMemoryCondition = `if ((← do
      let nvEndian ← do
        if (← memory.HaveNV2Ext ()) then
          if (acctype == AccType_NV2REGISTER) then
            pure ((BitVec.join1 [(BitVec.access (← readReg SCTLR_EL2) 25)]) == 1#1)
          else pure false
        else pure false
      if nvEndian then pure true else memory.BigEndian ()) : Bool)`

const rawArchVersionExpression = `(pure ((((((version == ARMv8p0) || ((version == ARMv8p1) && (← readReg __v81_implemented))) || ((version == ARMv8p2) && (← readReg __v82_implemented))) || ((version == ARMv8p3) && (← readReg __v83_implemented))) || ((version == ARMv8p4) && (← readReg __v84_implemented))) || ((version == ARMv8p5) && (← readReg __v85_implemented))))`

const guardedArchVersionExpression = `(do
    let through1 ← do
      if version == ARMv8p0 then pure true
      else if version == ARMv8p1 then readReg __v81_implemented else pure false
    let through2 ← do
      if through1 then pure true
      else if version == ARMv8p2 then readReg __v82_implemented else pure false
    let through3 ← do
      if through2 then pure true
      else if version == ARMv8p3 then readReg __v83_implemented else pure false
    let through4 ← do
      if through3 then pure true
      else if version == ARMv8p4 then readReg __v84_implemented else pure false
    if through4 then pure true
    else if version == ARMv8p5 then readReg __v85_implemented else pure false)`

// Sources are hashed before this extractor runs. Declarations must be unique;
// the next top-level declaration (not a closing brace) determines their end.
func declaration(source, kind, name string) string {
	start := regexp.MustCompile(`(?m)^`+kind+`[ \t]+`+regexp.QuoteMeta(name)+`(?:[ \t\r\n:(=]|$)`).FindAllStringIndex(source, -1)
	if len(start) != 1 {
		panic(fmt.Sprintf("%s %s: %d declarations", kind, name, len(start)))
	}
	end := len(source)
	next := regexp.MustCompile(`(?m)^(?:val|function|register|type|enum|struct|overload|let|union)[ \t]`).FindStringIndex(source[start[0][1]:])
	if next != nil {
		end = start[0][1] + next[0]
	}
	return strings.TrimSpace(source[start[0][0]:end]) + "\n\n"
}

func main() {
	_, file, _, ok := runtime.Caller(0)
	if !ok {
		panic("cannot locate generator")
	}
	here := filepath.Dir(file)
	output := flag.String("output-dir", here, "output root (fragment plus lean/STRExecution generated files)")
	sail := flag.String("sail", "sail", "Sail 0.20.2 executable")
	flag.Parse()
	ctx, cancel := context.WithTimeout(context.Background(), 2*time.Minute)
	defer cancel()
	version, err := exec.CommandContext(ctx, *sail, "--version").CombinedOutput()
	must(err)
	if !regexp.MustCompile(`^Sail 0\.20\.2(?: \([^\n]*\))?$`).MatchString(strings.TrimSpace(string(version))) {
		panic("this export is pinned to Sail 0.20.2")
	}
	sailDir, err := exec.CommandContext(ctx, *sail, "--dir").Output()
	must(err)
	vector := read(filepath.Join(strings.TrimSpace(string(sailDir)), "lib/vector.sail"))
	if fmt.Sprintf("%x", sha256.Sum256([]byte(vector))) != "73855de7cdfbef3cc5ba22b64478d1ae031ad56fdc80a4dedc8fdfbb4db1218b" {
		panic("pinned Sail vector prelude changed")
	}
	rawVector := vector
	vector = replaceOne(vector, "val signed = pure", "val oak_signed_compat = pure")
	model := filepath.Join(here, "../../external/sail-arm/arm-v8.5-a/model")
	pins := map[string]string{
		"aarch64.sail":     "9cdcf786f76223fb4bb0ca1fc52dbef3b62d7b2f3a4e22ab118935e03d4dd6bc",
		"aarch_types.sail": "f87f0dda7183442c253cd3e3cd4073999911c858702e099151bf313df428769a",
		"aarch_mem.sail":   "5764f0a9282825f63edf30b5fd50811ae5c85ab2a3f6104334e00d26cf6d5592",
		"prelude.sail":     "c372a54eb3a4cb43da6f09d989690048f6778db79783a0a13ae2884538cb03fc",
	}
	sources := map[string]string{}
	for name, pin := range pins {
		s := read(filepath.Join(model, name))
		if fmt.Sprintf("%x", sha256.Sum256([]byte(s))) != pin {
			panic("pinned source changed: " + name)
		}
		sources[name] = s
	}
	var fragment strings.Builder
	// Preserve the original Arm license in the derived source distribution.
	license := sources["aarch64.sail"]
	license = license[:strings.Index(license, "\nval println")]
	fragment.WriteString(license + "\n\n" + fragmentPrelude)
	add := func(source, kind, name string) {
		fragment.WriteString(declaration(sources[source], kind, name))
	}
	for _, name := range []string{"AccType", "Unpredictable", "Constraint", "MemOp"} {
		add("aarch_types.sail", "enum", name)
	}
	for _, name := range []string{"MemType", "DeviceType", "Fault"} {
		add("aarch_types.sail", "enum", name)
	}
	for _, name := range []string{"MemAttrHints", "MemoryAttributes", "FullAddress", "FaultRecord", "MPAMinfo", "AddressDescriptor", "AccessDescriptor"} {
		add("aarch_types.sail", "struct", name)
	}
	add("prelude.sail", "union", "exception")
	add("aarch_types.sail", "struct", "ProcState")
	for _, name := range []string{"_R", "PSTATE", "__LSISyndrome", "SCTLR_EL2"} {
		add("aarch_mem.sail", "register", name)
	}
	for _, name := range []string{"EL0", "EL1"} {
		add("aarch_mem.sail", "let", name)
	}
	for _, name := range []string{"aget_X", "MakeLSInstructionSyndrome", "AArch64_SetLSInstructionSyndrome"} {
		add("aarch64.sail", "val", name)
		add("aarch64.sail", "function", name)
	}
	for _, cut := range []struct{ source, name string }{
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
	} {
		spec := declaration(sources[cut.source], "val", cut.name)
		local := cut.name
		if local == "aset_Mem" {
			// Keep the instruction's explicit cut while also exporting the
			// original callee body under its original name in the same state.
			local = "oak_instruction_aset_Mem"
		}
		if local == "ZeroExtend__0" {
			local = "oak_instruction_ZeroExtend__0"
		}
		fragment.WriteString(replaceOne(spec, "val "+cut.name+" :", "val "+local+" = impure { lean: \"boundaries."+cut.name+"\" } :"))
	}
	fragment.WriteString("overload X = {aget_X, aset_X}\noverload SP = {aget_SP, aset_SP}\noverload Mem = {aget_Mem, oak_instruction_aset_Mem}\noverload SignExtend = {SignExtend__0}\noverload ZeroExtend = {oak_instruction_ZeroExtend__0}\n\n")
	add("aarch64.sail", "val", instruction)
	add("aarch64.sail", "function", instruction)
	for _, cut := range []struct{ source, name string }{
		{"aarch_mem.sail", "HaveNV2Ext"},
		{"aarch64.sail", "BigEndian"},
		{"aarch_mem.sail", "BigEndianReverse"},
		{"aarch64.sail", "AArch64_CheckAlignment"},
		{"aarch_mem.sail", "Align__1"},
		{"aarch64.sail", "AArch64_aset_MemSingle"},
	} {
		spec := declaration(sources[cut.source], "val", cut.name)
		local := cut.name
		if local == "AArch64_aset_MemSingle" {
			local = "oak_memory_aset_MemSingle"
		}
		if local == "HaveNV2Ext" {
			local = "oak_memory_HaveNV2Ext"
		}
		fragment.WriteString(replaceOne(spec, "val "+cut.name+" :", "val "+local+" = impure { lean: \"memory."+cut.name+"\" } :"))
	}
	fragment.WriteString("overload Align = {Align__1}\noverload MemSingle = {oak_memory_aset_MemSingle}\noverload HaveNV2Ext = {oak_memory_HaveNV2Ext}\n\n")
	add("aarch64.sail", "val", "aset_Mem")
	add("aarch64.sail", "function", "aset_Mem")
	add("aarch_mem.sail", "val", "IsFault")
	add("aarch_mem.sail", "function", "IsFault")
	for _, cut := range []struct{ source, name string }{
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
	} {
		spec := declaration(sources[cut.source], "val", cut.name)
		fragment.WriteString(replaceOne(spec, "val "+cut.name+" :", "val "+cut.name+" = impure { lean: \"single."+cut.name+"\" } :"))
	}
	fragment.WriteString("overload _Mem = {aset__Mem}\n\n")
	add("aarch64.sail", "val", "AArch64_aset_MemSingle")
	add("aarch64.sail", "function", "AArch64_aset_MemSingle")
	// Keep existing callers on their explicit cuts. These later declarations
	// export the actual callees for separately proved record instantiations.
	add("aarch_types.sail", "enum", "ArchVersion")
	for _, name := range []string{"__v85_implemented", "__v84_implemented", "__v83_implemented", "__v82_implemented", "__v81_implemented"} {
		add("aarch_mem.sail", "register configuration", name)
	}
	for _, name := range []string{"HasArchVersion", "HaveNV2Ext", "ZeroExtend__0"} {
		add("aarch_mem.sail", "val", name)
		add("aarch_mem.sail", "function", name)
	}
	fragmentSource := strings.TrimRight(fragment.String(), "\n") + "\n"
	tmp, err := os.MkdirTemp("", "oak-str-execution-")
	must(err)
	defer os.RemoveAll(tmp) // Only this freshly allocated temporary directory.
	must(os.WriteFile(filepath.Join(tmp, "str_execution.sail"), []byte(fragmentSource), 0644))
	must(os.WriteFile(filepath.Join(tmp, "str_execution_vector.sail"), []byte(vector), 0644))
	cmd := exec.CommandContext(ctx, *sail, "str_execution.sail", "--lean", "--lean-single-file", "--lean-output-dir", tmp,
		"--lean-lib-path", filepath.Clean(filepath.Join(here, "../../../external/lean-sail")))
	cmd.Dir = tmp
	cmd.Stdout, cmd.Stderr = os.Stdout, os.Stderr
	must(cmd.Run())
	defs := read(filepath.Join(tmp, "out/Out/Defs.lean"))
	rawDefs := defs
	defs = replaceOne(defs, "import Sail\n", "import Sail\n\nnamespace STRExecution\n") + "\nend STRExecution\n"
	generated := read(filepath.Join(tmp, "out/Out.lean"))
	rawGenerated := generated
	// A new compiler output needs an explicit re-audit of every Boolean site;
	// matching only the known expressions would silently admit another site.
	if fmt.Sprintf("%x", sha256.Sum256([]byte(rawGenerated))) != "232dab067cacb31824c8a2ac5a5f76435f7ecb5db9f7e328e5fb2626494ffb62" {
		panic("pinned raw STR execution Lean output changed")
	}
	generated = replaceOne(generated, rawSyndromeCondition, guardedSyndromeCondition)
	generated = replaceOne(generated, rawMemoryCondition, guardedMemoryCondition)
	generated = replaceOne(generated, rawArchVersionExpression, guardedArchVersionExpression)
	generated = replaceOne(generated, "import Out.Defs\nimport Out.Specialization\nimport Out.FakeReal\n",
		"import STRExecution.Defs\nimport STRExecution.Interface\n")
	generated = replaceOne(generated, "namespace Out.Functions", "namespace STRExecution.Functions\n\nopen PreSail")
	generated = replaceOne(generated, "end Out.Functions", "end STRExecution.Functions")
	generated = replaceOne(generated, "def "+instruction+" ", "def "+instruction+" (boundaries : Boundaries) ")
	generated = replaceOne(generated, "def aset_Mem ", "def aset_Mem (boundaries : Boundaries) (memory : MemoryBoundaries) ")
	generated = replaceOne(generated, "def AArch64_aset_MemSingle ", "def AArch64_aset_MemSingle (boundaries : Boundaries) (memory : MemoryBoundaries) (single : MemSingleBoundaries) ")
	outputs := map[string]string{
		"str_execution.sail":               fragmentSource,
		"str_execution_vector.sail":        vector,
		"lean/STRExecution/Defs.lean":      defs,
		"lean/STRExecution/Generated.lean": generated,
	}
	if filepath.Clean(*output) != filepath.Clean(here) {
		outputs["raw/Out.lean"] = rawGenerated
		outputs["raw/Out/Defs.lean"] = rawDefs
		outputs["raw/vector.sail"] = rawVector
	}
	for name, data := range outputs {
		path := filepath.Join(*output, name)
		must(os.MkdirAll(filepath.Dir(path), 0755))
		must(os.WriteFile(path, []byte(data), 0644))
		fmt.Println("regenerated", path)
	}
}

const fragmentPrelude = `/* Generated by str_execution_regen.go from the pinned original model.
 * The instruction, aset_Mem, AArch64_aset_MemSingle, types, exceptions, reads and syndrome functions
 * are copied intact. Unimplemented callees are EXPLICIT arbitrary impure
 * Lean callbacks, not implementations, success stubs, or architecture axioms.
 * Lean framing adds callback parameters and normalizes three pinned Boolean
 * conditions to preserve short-circuiting. This is not full architectural execution.
 * UInt/Zeros/__GetSlice_int adapt the original old prelude to modern Sail.
 * The pinned modern vector prelude renames only its unused signed function
 * declaration to oak_signed_compat, avoiding a clash with Arm's signed local.
 */
default Order dec
$include <flow.sail>
$include "str_execution_vector.sail"
$include <arith.sail>
$include <option.sail>
$include <string.sail>
overload ~ = {not_bool, not_vec}
val ediv_nat = pure { lean: "Nat.div" } : forall 'n 'm, 'n >= 0 & 'm > 0.
  (int('n), int('m)) -> int(div('n, 'm))
overload operator / = {ediv_nat}
val eq_anything = pure { lean: "_lean_beq" } : forall ('a : Type). ('a, 'a) -> bool
val neq_anything = pure { lean: "_lean_bne" } : forall ('a : Type). ('a, 'a) -> bool
overload operator == = {eq_anything}
overload operator != = {neq_anything}
val UInt : forall 'n. bits('n) -> {'m, 0 <= 'm <= 2 ^ 'n - 1. int('m)}
function UInt(x) = unsigned(x)
val Zeros : forall 'n, 'n >= 0. int('n) -> bits('n)
function Zeros(n) = sail_zeros(n)
val __GetSlice_int : forall 'n, 'n >= 0. (int('n), int, int) -> bits('n)
function __GetSlice_int(n, m, o) = get_slice_int(n, m, o)

`
