package asm

// Certificate obligations for the first native-equivalence audit slice.
// This file deliberately does not check LRAT: prove imports asm, so importing
// prove here would create a cycle. ExportNativeEqualityCNF independently
// rebuilds the exact inequivalence formula which a higher layer must pass to
// its certificate checker.

import (
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
)

// ExportNativeEqualityCNF regenerates the exact result-inequality obligation
// for a closed native scalar function. The accepted v1 slice has only fixed
// integer/Bool parameters and one result, permits local control flow and stack
// spills, and rejects calls, loops, externally visible memory, traps, domains,
// result-relevant float/vector semantics, aggregates, and term operations
// outside the bit blaster. decl must be the checked declaration paired with fn.
//
// The reference is the body the verifier judges: fn.Body for a materialized
// rewrite candidate, otherwise decl.Body. An UNSAT certificate for Text proves
// only this regenerated term-level obligation; machine execution, Oak lowering,
// clause generation, and their formal correspondence remain separate links.
func ExportNativeEqualityCNF(fn *Function, decl *ast.FunctionStatement) (CNF, string, bool) {
	refuse := func(format string, args ...interface{}) (CNF, string, bool) {
		return CNF{}, fmt.Sprintf(format, args...), false
	}
	if fn == nil || decl == nil {
		return refuse("the native function or Oak declaration is missing")
	}
	if fn.Signature == nil {
		return refuse("the native function signature is missing")
	}
	if fn.Signature.Name == nil || decl.Name == nil {
		return refuse("the native function or Oak declaration name is missing")
	}
	if fn.Name == "" || fn.Name != fn.Signature.Name.Value || fn.Name != decl.Name.Value {
		return refuse("native function identity mismatch: unit %q, signature %q, declaration %q",
			fn.Name, fn.Signature.Name.Value, decl.Name.Value)
	}
	for _, parameters := range [][]*ast.FunctionParameter{fn.Signature.Parameters, decl.Parameters} {
		for _, param := range parameters {
			if param == nil || param.Name == nil || param.Type == nil {
				return refuse("a malformed scalar parameter is outside the native certificate slice")
			}
		}
	}
	if fn.Arch != ArchArm64 && fn.Arch != ArchRV64 {
		return refuse("architecture %q is outside the native certificate slice", fn.Arch)
	}
	if fn.System {
		return refuse("system-capability bodies are outside the native certificate slice")
	}
	if decl.Receiver != nil || len(decl.TypeParams) != 0 {
		return refuse("methods or unspecialized generic declarations are outside the native certificate slice")
	}
	if findings := Check(fn, decl, nil); len(findings) != 0 {
		return refuse("the assembler seam checker refused the body: %s", strings.Join(findings, "; "))
	}
	// RV64's seam pass derives these markers, so this check must follow Check.
	if fn.VectorFile || fn.FloatFile {
		return refuse("floating-point or vector register files are outside the native certificate slice")
	}
	for _, param := range decl.Parameters {
		if !nativeCertificateScalar(param.Type) {
			return refuse("parameter types outside fixed integers and Bool are not certificate-enabled")
		}
	}
	if !nativeCertificateScalar(decl.ReturnType) {
		return refuse("result type %s is outside fixed integers and Bool", typeText(decl.ReturnType))
	}
	if _, _, isComposite := resultComposite(fn, decl); isComposite {
		return refuse("aggregate results are outside the native certificate slice")
	}

	reference := decl.Body
	if fn.Body != nil {
		reference = fn.Body
	}
	if reference == nil {
		return refuse("the exact Oak reference body is missing")
	}
	if nativeCertificateHasLoop(reference) {
		return refuse("source loops are outside the native certificate slice")
	}

	// Calls must refuse instead of being summarized. The shallow copy keeps all
	// exact machine metadata while withholding the callee table from both sides.
	closed := *fn
	closed.Callees = nil
	asmTerm, exec, reason, ok := executeBody(&closed, decl, nil)
	if !ok {
		return refuse("machine execution is outside the native certificate slice: %s", reason)
	}
	if exec == nil || !exec.hasResult || asmTerm == nil || asmTerm == trapPath {
		return refuse("the machine body does not produce one scalar result")
	}
	if len(exec.loopExits) != 0 || len(exec.loops) != 0 {
		return refuse("machine loops are outside the native certificate slice")
	}
	if len(exec.summarized) != 0 || exec.callSites != 0 {
		return refuse("machine calls are outside the native certificate slice")
	}
	if exec.trap != nil {
		return refuse("machine trap paths are outside the native certificate slice")
	}
	if len(exec.cells) != 0 || len(exec.writes) != 0 {
		return refuse("externally visible machine effects are outside the native certificate slice")
	}

	lowering := prepareLowering(&closed, decl, nil)
	lowering.trapsTracked = true
	if exec.notes != nil {
		lowering.shiftGuardMax = exec.notes.shiftGuardMax
	}
	for name, width := range exec.freshSyms {
		lowering.fresh[name] = width
	}
	oakTerm, width, reason, ok := lowering.resultTerm(&closed, decl, reference)
	if !ok {
		return refuse("Oak lowering is outside the native certificate slice: %s", reason)
	}
	if len(lowering.loops) != 0 {
		return refuse("lowered Oak loops are outside the native certificate slice")
	}
	if len(lowering.traps) != 0 || lowering.machineTrap != nil {
		return refuse("Oak trap obligations are outside the native certificate slice")
	}
	if len(lowering.cells) != 0 || len(lowering.writes) != 0 {
		return refuse("externally visible Oak effects are outside the native certificate slice")
	}
	if lowering.domainCondition() != nil {
		return refuse("restricted input domains are outside the native certificate slice")
	}

	asmTerm = truncate(asmTerm, width)
	oakTerm = adaptWidth(oakTerm, width)
	mentioned := map[string]bool{}
	collectParams(asmTerm, mentioned)
	collectParams(oakTerm, mentioned)
	names := make([]string, 0, len(mentioned))
	widths := make(map[string]int, len(mentioned))
	for name := range mentioned {
		declared, scalar := lowering.params[name]
		if !scalar {
			declared, scalar = lowering.fresh[name]
		}
		if !scalar || declared < 1 || declared > 64 {
			return refuse("symbolic input %q is outside the declared or modeled scalar contract", name)
		}
		names = append(names, name)
		widths[name] = declared
	}
	sort.Strings(names)
	if reason := nativeCertificateTermReason(asmTerm, widths); reason != "" {
		return refuse("machine result uses %s", reason)
	}
	if reason := nativeCertificateTermReason(oakTerm, widths); reason != "" {
		return refuse("Oak result uses %s", reason)
	}

	claim := truncate(cmpTerm("eq", asmTerm, oakTerm), 1)
	return exportTermCNF("oak native equality: "+fn.Arch+":"+fn.Name, names, widths, claim, nil)
}

func nativeCertificateScalar(expr ast.Expression) bool {
	switch typeText(expr) {
	case "Bool", "byte", "rune", "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64":
		return true
	}
	return false
}

func nativeCertificateHasLoop(node ast.Node) bool {
	found := false
	walkASTNodes(node, func(node ast.Node) {
		if _, isLoop := node.(*ast.WhileStatement); isLoop {
			found = true
		}
	})
	return found
}

func nativeCertificateTermReason(root *term, widths map[string]int) string {
	seen := map[*term]bool{}
	var visit func(*term) string
	visit = func(t *term) string {
		if t == nil {
			return "a missing term"
		}
		if seen[t] {
			return ""
		}
		seen[t] = true
		if t.width < 1 || t.width > 64 {
			return fmt.Sprintf("a %d-bit term", t.width)
		}
		switch t.kind {
		case termParam:
			if _, known := widths[t.name]; !known {
				return fmt.Sprintf("an undeclared symbolic input %q", t.name)
			}
			return ""
		case termConst:
			return ""
		case termBinary:
			switch t.op {
			case "and", "or", "xor", "add", "sub", "shl", "shr", "sar", "mul", "ror", "rev", "rev16", "rev32", "rbit", "clz", "cnt", "cls":
			default:
				return fmt.Sprintf("unsupported operation %q", t.op)
			}
		case termCmp:
			flags, condition := splitFlagsKind(t.op)
			if _, known := problemFlagKinds[flags]; !known {
				return fmt.Sprintf("unsupported flag kind %q", flags)
			}
			if _, known := problemConditionCodes[condition]; !known {
				return fmt.Sprintf("unsupported condition %q", condition)
			}
		case termIte:
			// All three children are checked below.
		default:
			return fmt.Sprintf("term kind %d outside pure scalar bit operations", t.kind)
		}
		if t.kind == termIte {
			if reason := visit(t.cond); reason != "" {
				return reason
			}
		}
		if reason := visit(t.left); reason != "" {
			return reason
		}
		return visit(t.right)
	}
	return visit(root)
}
