package codegen

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/layout"
	"github.com/SCKelemen/oak/parser"
	"github.com/SCKelemen/oak/scanner"
	"github.com/SCKelemen/oak/typechecker"
)

// Translation validation of the trusted core (docs/spec/126-verification-chain.md
// §5, item 2): the prelude's total-arithmetic helpers — the text
// Oak.ArithmeticRefinement proves equal to Oak's operators — and the
// conversion helpers Oak.ConversionRefinement proves are compiled by the
// system C compiler to assembly, and that assembly is run through the
// assembler verifier as a unit whose Oak body is the helper's
// specification. The verifier decides the machine code against the Oak
// operator exactly as it decides a hand-written unit, so for these
// functions the C compiler's output is checked rather than trusted. A
// helper the verifier cannot decide (division has a trap path and no
// power-of-two constant, a shift has a variable count) is reported
// trusted and must not be a mismatch; one that the verifier does decide
// must be proven.
//
// arm64 through clang (aarch64-none-elf, AAPCS64), rv64 through
// riscv64-elf-gcc (LP64) when present.

// The verdict a helper must reach: `proofRequired` for the linear and
// bit-level helpers, `witnessRequired` for multiplication (the bit-level
// decision exceeds the node budget, so the verifier's evidence is the
// witness set), `mismatchForbidden` for the helpers whose Oak body is
// outside the lowering's subset (division and remainder by a variable).
type verdictBar int

const (
	proofRequired verdictBar = iota
	witnessRequired
	mismatchForbidden
)

type validatedHelper struct {
	name    string // the unit and C wrapper name
	decl    string // Oak signature
	spec    string // Oak body: the helper's specification
	cSource string // C wrapper calling the prelude helper
	bar     verdictBar
	// outside names the lanes whose compiler emits a shape the verifier's
	// unit language does not have, with the reason; the helper is reported
	// outside the decided subset there (a mismatch still fails) and held to
	// bar on the other lanes.
	outside map[string]string
}

func translationValidationHelpers() []validatedHelper {
	var helpers []validatedHelper
	types := []string{"u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64"}
	for _, ty := range types {
		binary := func(op, oakOp string, bar verdictBar) {
			name := "tv_" + op + "_" + ty
			helpers = append(helpers, validatedHelper{
				name:    name,
				decl:    fmt.Sprintf("%s: (a, b: %s) -> %s", name, ty, ty),
				spec:    "a " + oakOp + " b",
				cSource: fmt.Sprintf("%s %s(%s a, %s b) { return oak_%s_%s(a, b); }\n", ty, name, ty, ty, op, ty),
				bar:     bar,
			})
		}
		binary("add", "+", proofRequired)
		binary("sub", "-", proofRequired)
		binary("mul", "*", witnessRequired)
		binary("div", "/", witnessRequired)
		binary("rem", "%", witnessRequired)
		name := "tv_neg_" + ty
		helpers = append(helpers, validatedHelper{
			name:    name,
			decl:    fmt.Sprintf("%s: (a: %s) -> %s", name, ty, ty),
			spec:    "-a",
			cSource: fmt.Sprintf("%s %s(%s a) { return oak_neg_%s(a); }\n", ty, name, ty, ty),
			bar:     proofRequired,
		})
	}
	// The checked shifts under a constant count: the count is below the
	// width, so the trap check folds away and the verifier's Oak side admits
	// the constant shift (a variable count it refuses: Oak traps where the
	// machine wraps).
	for _, ty := range []string{"u8", "u16", "u32", "u64"} {
		width := typechecker.PrimitiveBits(ty)
		for _, count := range []int{1, 3, width - 1} {
			for _, op := range []struct{ name, oak string }{{"shl", "<<"}, {"shr", ">>"}} {
				name := fmt.Sprintf("tv_%s%d_%s", op.name, count, ty)
				helpers = append(helpers, validatedHelper{
					name:    name,
					decl:    fmt.Sprintf("%s: (v: %s) -> %s", name, ty, ty),
					spec:    fmt.Sprintf("v %s %d", op.oak, count),
					cSource: fmt.Sprintf("%s %s(%s v) { return oak_%s_%s(v, %d); }\n", ty, name, ty, op.name, ty, count),
					bar:     proofRequired,
				})
			}
		}
	}
	// The guarded element read (`oak_index`): the bounds check is a trap
	// path, the read itself a span load the verifier decides against the
	// Oak element read.
	for _, ty := range []string{"u8", "u16", "u32", "u64"} {
		name := "tv_index_" + ty
		helpers = append(helpers, validatedHelper{
			name:    name,
			decl:    fmt.Sprintf("%s: (v: []%s, i: u32) -> %s", name, ty, ty),
			spec:    "v[i]",
			cSource: fmt.Sprintf("%s %s(const %s *base, u32 len, u32 i) { return oak_index(base, len, i); }\n", ty, name, ty),
			bar:     proofRequired,
		})
	}
	// The guarded element write (`oak_store`): a unit helper whose effect
	// is the store; the verifier proves the span memory it writes against
	// the Oak assignment (asm/effects.go).
	for _, ty := range []string{"u8", "u16", "u32", "u64"} {
		name := "tv_store_" + ty
		helpers = append(helpers, validatedHelper{
			name:    name,
			decl:    fmt.Sprintf("%s: (v: [*]%s, i: u32, x: %s) -> ()", name, ty, ty),
			spec:    "{ v[i] = x }",
			cSource: fmt.Sprintf("void %s(%s *base, u32 len, u32 i, %s x) { oak_store(base, len, i, x); }\n", name, ty, ty),
			bar:     proofRequired,
		})
	}
	// The strong compare-exchange helper on a cell reached through a span
	// element under the index guard: the value observed and the guarded
	// store (docs/spec/65-machine-memory.md section 7a). clang spells it as
	// the exclusive loop (armv8.0) or `casal` (LSE); GCC spells it as the
	// RV64 `lr.w`/`sc.w` loop the unit language verifies below.
	helpers = append(helpers, validatedHelper{
		name:    "tv_cas_u32",
		decl:    "tv_cas_u32: (v: [*]Atomic[u32], i: u32, expected, desired: u32) -> u32",
		spec:    "atomic_compare_exchange_acq_rel_acquire(v[i], expected, desired)",
		cSource: "u32 tv_cas_u32(_Atomic(u32) *base, u32 len, u32 i, u32 expected, u32 desired) { if ((u64)(i) >= (u64)(len)) { __builtin_trap(); } return __oak_cas_u32_acq_rel_acquire(base + i, expected, desired); }\n",
		bar:     proofRequired,
	})
	for _, conv := range []string{"u8_trunc_u32", "u16_trunc_u64", "u32_trunc_u64", "i8_trunc_i32", "i16_trunc_i64", "i32_trunc_i64", "i32_bits_u32", "u32_bits_i32", "u64_bits_i64", "i64_bits_u64", "u8_trunc_i32", "i8_trunc_u64"} {
		target, _, source, ok := typechecker.ConversionParts(conv)
		if !ok {
			panic(conv)
		}
		name := "tv_" + conv
		helpers = append(helpers, validatedHelper{
			name:    name,
			decl:    fmt.Sprintf("%s: (x: %s) -> %s", name, source, target),
			spec:    conv + "(x)",
			cSource: fmt.Sprintf("%s %s(%s x) { return %s(x); }\n", target, name, source, conversionHelperName(conv)),
			bar:     proofRequired,
		})
	}
	return helpers
}

// casHelperText is the prelude's strong compare-exchange helper for u32 at
// acq_rel/acquire, as `generateC` emits it (the text
// spec/lean/Oak/CompareExchangeRefinement.lean transliterates).
const casHelperText = "static inline u32 __oak_cas_u32_acq_rel_acquire(_Atomic(u32) *cell, u32 expected, u32 desired) {\n" +
	"  u32 observed = expected;\n" +
	"  (void)atomic_compare_exchange_strong_explicit(cell, &observed, desired, OAK_ORDER_CAS_ACQ_REL, memory_order_acquire);\n" +
	"  return observed;\n" +
	"}\n"

// guardMacroLines are the prelude's guarded element read and checked
// shift helpers, pinned to the emitted text like arithmeticMacroLines:
// these are the lines the validated units are compiled from.
var guardMacroLines = []string{
	`static inline u64 oak_bounds_trap(void) { __builtin_trap(); return 0; }`,
	`#define oak_index(base, len, i) ((u64)(i) < (u64)(len) ? (base)[(i)] : (base)[oak_bounds_trap()])`,
	`#define OAK_SHIFT_HELPERS(T, W) \`,
	`  static inline T oak_shl_##T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v << n); } \`,
	`  static inline T oak_shr_##T(T v, T n) { if (n >= W) { __builtin_trap(); } return (T)(v >> n); }`,
	`OAK_SHIFT_HELPERS(u8, 8u) OAK_SHIFT_HELPERS(u16, 16u) OAK_SHIFT_HELPERS(u32, 32u) OAK_SHIFT_HELPERS(u64, 64u)`,
	`#define oak_store(base, len, i, v) do { if ((u64)(i) >= (u64)(len)) { __builtin_trap(); } (base)[(i)] = (v); } while (0)`,
}

func TestGuardMacrosMatchValidatedText(t *testing.T) {
	output := generateC(t, "package main\n\nmain: (): i32 {\n  a: u32 = u32(3)\n  i32_bits_u32(a << 2)\n}\n")
	for _, line := range guardMacroLines {
		if !strings.Contains(output, line+"\n") {
			t.Fatalf("emitted prelude lacks the pinned line\n%s\n— update guardMacroLines (codegen/translation_validation_test.go); output:\n%s", line, output)
		}
	}
	// The compare-exchange helper and the order macros, from a program
	// that uses the helper.
	withCAS := generateC(t, "package main\n\ncell: Atomic[u32]\n\nmain: (): i32 {\n  atomic_store_relaxed(cell, u32(1))\n  seen: u32 = atomic_compare_exchange_acq_rel_acquire(cell, u32(1), u32(2))\n  i32_bits_u32(atomic_load_acquire(cell) - seen - u32(1))\n}\n")
	if !strings.Contains(withCAS, casHelperText) {
		t.Fatalf("emitted C lacks the pinned compare-exchange helper\n%s\n— update casHelperText (codegen/translation_validation_test.go); output:\n%s", casHelperText, withCAS)
	}
	if !strings.Contains(withCAS, atomicOrderMacros) {
		t.Fatalf("emitted C lacks the atomic order macros; output:\n%s", withCAS)
	}
}

// translationValidationC is a freestanding C translation unit: the prelude
// helpers as the backend emits them, and one exported wrapper per helper.
func translationValidationC(helpers []validatedHelper) string {
	var b strings.Builder
	b.WriteString("typedef __UINT8_TYPE__ u8; typedef __UINT16_TYPE__ u16; typedef __UINT32_TYPE__ u32; typedef __UINT64_TYPE__ u64;\n")
	b.WriteString("typedef __INT8_TYPE__ i8; typedef __INT16_TYPE__ i16; typedef __INT32_TYPE__ i32; typedef __INT64_TYPE__ i64;\n")
	b.WriteString("#define INT8_MIN (-128)\n#define INT16_MIN (-32768)\n#define INT32_MIN (-2147483647-1)\n#define INT64_MIN (-9223372036854775807LL-1)\n")
	b.WriteString(strings.Join(arithmeticMacroLines, "\n") + "\n")
	b.WriteString(strings.Join(guardMacroLines, "\n") + "\n")
	b.WriteString("#include <stdatomic.h>\n")
	b.WriteString(atomicOrderMacros)
	b.WriteString(casHelperText)
	seen := map[string]bool{}
	for _, h := range helpers {
		if strings.HasPrefix(h.name, "tv_") && strings.Contains(h.name, "_trunc_") || strings.Contains(h.name, "_bits_") {
			conv := strings.TrimPrefix(h.name, "tv_")
			if !seen[conv] {
				seen[conv] = true
				b.WriteString(conversionHelperSource(conv))
			}
		}
	}
	for _, h := range helpers {
		b.WriteString(h.cSource)
	}
	return b.String()
}

var (
	tvGlobalLabel                 = regexp.MustCompile(`^(tv_[A-Za-z0-9_]+):`)
	tvLocalLabel                  = regexp.MustCompile(`^\.L([A-Za-z0-9_]+):$`)
	tvLocalRef                    = regexp.MustCompile(`\.L([A-Za-z0-9_]+)`)
	tvNumericLabelWithInstruction = regexp.MustCompile(`^([0-9]+):[ \t]*(.+)$`)
	tvArm64Reg                    = regexp.MustCompile(`\b([wx](?:[12]?[0-9]|30)|wzr|xzr)\b`)
	tvRV64Reg                     = regexp.MustCompile(`\b(a[0-7]|t[0-6]|s(?:[0-9]|1[01])|ra|gp|tp)\b`)
)

// assemblyFunctions splits compiler assembly into the instruction lines of
// each tv_ function: directives dropped, comments stripped, local labels
// renamed from the assembler's `.L` form to plain identifiers. GCC 13 emits
// an RV64 compare-exchange template as semicolon-separated statements on one
// physical line, so statements are split before labels are classified.
func assemblyFunctions(assembly string, comment string) map[string][]string {
	functions := map[string][]string{}
	var current string
	for _, raw := range strings.Split(assembly, "\n") {
		physicalLine := raw
		if comment != "" {
			if i := strings.Index(physicalLine, comment); i >= 0 {
				physicalLine = physicalLine[:i]
			}
		}
		for _, statement := range strings.Split(physicalLine, ";") {
			line := strings.TrimSpace(statement)
			if m := tvGlobalLabel.FindStringSubmatch(line); m != nil {
				current = m[1]
				continue
			}
			if current == "" || line == "" {
				continue
			}
			if strings.HasPrefix(line, ".Lfunc_end") || strings.HasPrefix(line, ".size") || strings.HasPrefix(line, ".cfi_endproc") {
				current = ""
				continue
			}
			if m := tvLocalLabel.FindStringSubmatch(line); m != nil {
				functions[current] = append(functions[current], "L"+m[1]+":")
				continue
			}
			if m := tvNumericLabelWithInstruction.FindStringSubmatch(line); m != nil {
				functions[current] = append(functions[current], "N"+m[1]+":")
				line = strings.TrimSpace(m[2])
			}
			if m := tvNumericLabel.FindStringSubmatch(line); m != nil {
				// GCC's numeric local labels (`1:`, referenced as `1b`/`1f`):
				// kept as markers, resolved below.
				functions[current] = append(functions[current], "N"+m[1]+":")
				continue
			}
			if strings.HasPrefix(line, ".") || strings.HasSuffix(line, ":") {
				continue
			}
			functions[current] = append(functions[current], tvLocalRef.ReplaceAllString(line, "L$1"))
		}
	}
	for name, lines := range functions {
		functions[name] = resolveNumericLabels(lines)
	}
	return functions
}

var (
	tvNumericLabel = regexp.MustCompile(`^([0-9]+):$`)
	tvNumericRef   = regexp.MustCompile(`\b([0-9]+)([bf])\b`)
)

// resolveNumericLabels gives every numeric local label a unique name and
// rewrites its backward (`Nb`, the nearest definition before) and forward
// (`Nf`, the nearest after) references to it.
func resolveNumericLabels(lines []string) []string {
	out := make([]string, len(lines))
	for i, line := range lines {
		if m := tvNumericLabel.FindStringSubmatch(strings.TrimPrefix(line, "N")); m != nil && strings.HasPrefix(line, "N") {
			out[i] = fmt.Sprintf("N%s_%d:", m[1], i)
			continue
		}
		out[i] = tvNumericRef.ReplaceAllStringFunc(line, func(ref string) string {
			m := tvNumericRef.FindStringSubmatch(ref)
			number, direction := m[1], m[2]
			if direction == "b" {
				for j := i - 1; j >= 0; j-- {
					if lines[j] == "N"+number+":" {
						return fmt.Sprintf("N%s_%d", number, j)
					}
				}
			} else {
				for j := i + 1; j < len(lines); j++ {
					if lines[j] == "N"+number+":" {
						return fmt.Sprintf("N%s_%d", number, j)
					}
				}
			}
			return ref
		})
	}
	return out
}

func TestAssemblyFunctionsKeepsGCC13PackedRV64CAS(t *testing.T) {
	assembly := `.text
.globl tv_cas_u32
tv_cas_u32:
  bgeu a2,a1,.Ltrap
  slli a5,a2,32
  srli a2,a5,30
  add a5,a0,a2
  .option push; .option norvc
  1: lr.w.aqrl a0,0(a5); bne a0,a3,1f; sc.w.rl a2,a4,0(a5); bnez a2,1b; 1: # atomic template
  .option pop
  sext.w a0,a0
  ret
.Ltrap:
  ebreak
.size tv_cas_u32, .-tv_cas_u32
  addi a0,a0,99
`
	want := []string{
		"bgeu a2,a1,Ltrap",
		"slli a5,a2,32",
		"srli a2,a5,30",
		"add a5,a0,a2",
		"N1_4:",
		"lr.w.aqrl a0,0(a5)",
		"bne a0,a3,N1_9",
		"sc.w.rl a2,a4,0(a5)",
		"bnez a2,N1_4",
		"N1_9:",
		"sext.w a0,a0",
		"ret",
		"Ltrap:",
		"ebreak",
	}
	got := assemblyFunctions(assembly, "#")["tv_cas_u32"]
	if strings.Join(got, "\n") != strings.Join(want, "\n") {
		t.Fatalf("GCC 13 packed RV64 CAS extraction:\n--- have\n%s\n--- want\n%s",
			strings.Join(got, "\n"), strings.Join(want, "\n"))
	}
	var helper validatedHelper
	found := false
	for _, candidate := range translationValidationHelpers() {
		if candidate.name == "tv_cas_u32" {
			helper, found = candidate, true
			break
		}
	}
	if !found {
		t.Fatal("translation-validation catalogue does not contain tv_cas_u32")
	}
	signature := parseOakSpec(t, helper.decl)
	specification := parseOakSpec(t, helper.decl+" = "+helper.spec)
	unitText := unitFor(asm.ArchRV64, helper, signature, got)
	unit, errs := asm.ParseUnit("gcc13.rv64.oakasm", unitText)
	if len(errs) != 0 {
		t.Fatalf("extracted GCC 13 CAS does not parse: %v\n%s", errs, unitText)
	}
	if findings := asm.Check(unit.Functions[0], signature, nil); len(findings) != 0 {
		t.Fatalf("extracted GCC 13 CAS checker findings: %v\n%s", findings, unitText)
	}
	verdict := asm.Verify(unit.Functions[0], signature, specification.Body)
	if verdict.Kind != asm.VerdictProven {
		t.Fatalf("extracted GCC 13 CAS verdict = %s: %s\n%s",
			verdict.Kind, verdict.Message, unitText)
	}
}

func parseOakSpec(t *testing.T, source string) *ast.FunctionStatement {
	t.Helper()
	p := parser.New(layout.New(scanner.New(source)))
	program := p.ParseProgram()
	if errs := p.Errors(); len(errs) != 0 {
		t.Fatalf("%s: %v", source, errs)
	}
	fn, ok := program.Statements[0].(*ast.FunctionStatement)
	if !ok {
		t.Fatalf("%s: not a function", source)
	}
	return fn
}

// unitFor builds the .oakasm unit text for one compiled helper: the
// parameters bound to their ABI registers, every other register the body
// touches declared a clobber, then the compiler's instructions.
func unitFor(arch string, h validatedHelper, sig *ast.FunctionStatement, body []string) string {
	var b strings.Builder
	b.WriteString(h.decl + " = {\n")
	bound := map[string]bool{}
	index := 0
	for _, param := range sig.Parameters {
		if isSpanType(param.Type) {
			// A span or view is its base and length: two argument registers
			// (AAPCS64: x0, w1; LP64: a0, a1).
			if arch == asm.ArchRV64 {
				fmt.Fprintf(&b, "  bind a%d, a%d = %s\n", index, index+1, param.Name.Value)
				bound[fmt.Sprintf("a%d", index)] = true
				bound[fmt.Sprintf("a%d", index+1)] = true
			} else {
				fmt.Fprintf(&b, "  bind x%d, w%d = %s\n", index, index+1, param.Name.Value)
				for _, r := range []string{fmt.Sprintf("x%d", index), fmt.Sprintf("w%d", index), fmt.Sprintf("x%d", index+1), fmt.Sprintf("w%d", index+1)} {
					bound[r] = true
				}
			}
			index += 2
			continue
		}
		bits := typechecker.PrimitiveBits(paramTypeName(param.Type))
		var reg string
		if arch == asm.ArchRV64 {
			reg = fmt.Sprintf("a%d", index)
		} else if bits <= 32 {
			reg = fmt.Sprintf("w%d", index)
			bound[fmt.Sprintf("x%d", index)] = true
		} else {
			reg = fmt.Sprintf("x%d", index)
			bound[fmt.Sprintf("w%d", index)] = true
		}
		bound[reg] = true
		fmt.Fprintf(&b, "  bind %s = %s\n", reg, param.Name.Value)
		index++
	}
	regs := tvArm64Reg
	if arch == asm.ArchRV64 {
		regs = tvRV64Reg
	}
	var clobbers []string
	seen := map[string]bool{}
	for _, line := range body {
		if strings.HasSuffix(line, ":") {
			continue
		}
		for _, reg := range regs.FindAllString(line, -1) {
			if reg == "wzr" || reg == "xzr" || bound[reg] || seen[reg] {
				continue
			}
			if arch != asm.ArchRV64 && (reg == "w0" || reg == "x0") {
				continue // the result register
			}
			seen[reg] = true
			clobbers = append(clobbers, reg)
		}
	}
	if len(clobbers) > 0 {
		fmt.Fprintf(&b, "  clobber %s\n", strings.Join(clobbers, ", "))
	}
	for _, line := range body {
		if strings.HasSuffix(line, ":") {
			b.WriteString(line + "\n")
		} else {
			b.WriteString("  " + line + "\n")
		}
	}
	b.WriteString("}\n")
	return b.String()
}

// isSpanType recognizes `[]T` and `[*]T` parameter types.
func isSpanType(expr ast.Expression) bool {
	index, ok := expr.(*ast.IndexExpression)
	if !ok || index.Dot {
		return false
	}
	marker, isMarker := index.Index.(*ast.Identifier)
	return isMarker && (marker.Value == "" || marker.Value == "*")
}

func paramTypeName(expr ast.Expression) string {
	if ident, ok := expr.(*ast.Identifier); ok {
		return ident.Value
	}
	return expr.String()
}

// validateTranslation compiles the helpers for one lane and verifies each
// against its specification, returning the verdicts by helper name.
func validateTranslation(t *testing.T, arch string, compile func(cPath, sPath string) error, comment string) {
	t.Helper()
	helpers := translationValidationHelpers()
	dir := t.TempDir()
	cPath := filepath.Join(dir, "helpers.c")
	sPath := filepath.Join(dir, "helpers.s")
	source := translationValidationC(helpers)
	if err := os.WriteFile(cPath, []byte(source), 0o600); err != nil {
		t.Fatal(err)
	}
	if err := compile(cPath, sPath); err != nil {
		t.Fatalf("compile the prelude helpers for %s: %v\n--- C ---\n%s", arch, err, source)
	}
	assembly, err := os.ReadFile(sPath)
	if err != nil {
		t.Fatal(err)
	}
	functions := assemblyFunctions(string(assembly), comment)
	proven, witnessed, trusted := 0, 0, 0
	for _, h := range helpers {
		body, found := functions[h.name]
		if !found {
			t.Errorf("%s: %s not found in the compiler's assembly", arch, h.name)
			continue
		}
		sig := parseOakSpec(t, h.decl)
		spec := parseOakSpec(t, h.decl+" = "+h.spec)
		if reason, isOutside := h.outside[arch]; isOutside {
			t.Logf("%s %s: %s", arch, h.name, reason)
			h.bar = mismatchForbidden
		}
		unitText := unitFor(arch, h, sig, body)
		unit, errs := asm.ParseUnit("helpers."+arch+".oakasm", unitText)
		if len(errs) != 0 {
			if h.bar != mismatchForbidden {
				t.Errorf("%s %s: the unit does not parse: %v\n%s", arch, h.name, errs, unitText)
			} else {
				t.Logf("%s %s: outside the unit language (%v)", arch, h.name, errs[0])
				trusted++
			}
			continue
		}
		if findings := asm.Check(unit.Functions[0], sig, nil); len(findings) != 0 {
			if h.bar != mismatchForbidden {
				t.Errorf("%s %s: checker: %v\n%s", arch, h.name, findings, unitText)
			} else {
				t.Logf("%s %s: checker refuses (%s)", arch, h.name, findings[0])
				trusted++
			}
			continue
		}
		verdict := asm.Verify(unit.Functions[0], sig, spec.Body)
		switch {
		case verdict.Kind == asm.VerdictMismatch:
			t.Errorf("%s %s: the compiler's code disagrees with %s: %s\n%s", arch, h.name, h.spec, verdict.Message, unitText)
		case h.bar == proofRequired && verdict.Kind != asm.VerdictProven:
			t.Errorf("%s %s: must be proven against %s, got %s: %s\n%s", arch, h.name, h.spec, verdict.Kind, verdict.Message, unitText)
		case h.bar == witnessRequired && verdict.Kind != asm.VerdictProven && verdict.Kind != asm.VerdictWitnessed:
			t.Errorf("%s %s: must be at least witnessed against %s, got %s: %s\n%s", arch, h.name, h.spec, verdict.Kind, verdict.Message, unitText)
		case verdict.Kind == asm.VerdictProven:
			proven++
		case verdict.Kind == asm.VerdictWitnessed:
			witnessed++
		default:
			t.Logf("%s %s: %s", arch, h.name, verdict.Message)
			trusted++
		}
	}
	t.Logf("%s: %d helpers proven against their Oak specification, %d witnessed, %d outside the decided subset", arch, proven, witnessed, trusted)
}

func TestTranslationValidationArm64(t *testing.T) {
	clang, err := exec.LookPath("clang")
	if err != nil {
		t.Skip("clang is required to compile the prelude helpers for arm64")
	}
	validateTranslation(t, asm.ArchArm64, func(cPath, sPath string) error {
		out, err := exec.Command(clang, "--target=aarch64-none-elf", "-std=c11", "-O1", "-ffreestanding",
			"-fno-asynchronous-unwind-tables", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-S", cPath, "-o", sPath).CombinedOutput()
		if err != nil {
			return fmt.Errorf("%v\n%s", err, out)
		}
		return nil
	}, "//")
}

// The Apple M-series lane: what the Apple cores' compilers emit (LSE
// atomics, `ldapr` for an acquire load, the same guards); `-mcpu=apple-m1`
// is what a darwin/arm64 build of Oak's C compiles with.
func TestTranslationValidationArm64Apple(t *testing.T) {
	clang, err := exec.LookPath("clang")
	if err != nil {
		t.Skip("clang is required to compile the prelude helpers for arm64")
	}
	validateTranslation(t, asm.ArchArm64, func(cPath, sPath string) error {
		out, err := exec.Command(clang, "--target=aarch64-none-elf", "-mcpu=apple-m1", "-std=c11", "-O1", "-ffreestanding",
			"-fno-asynchronous-unwind-tables", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-S", cPath, "-o", sPath).CombinedOutput()
		if err != nil {
			return fmt.Errorf("%v\n%s", err, out)
		}
		return nil
	}, "//")
}

// The LSE lane: armv8.1-a spells the atomics as single instructions
// (`casal`) where armv8.0 loops on the exclusives; both are decided.
func TestTranslationValidationArm64LSE(t *testing.T) {
	clang, err := exec.LookPath("clang")
	if err != nil {
		t.Skip("clang is required to compile the prelude helpers for arm64")
	}
	validateTranslation(t, asm.ArchArm64, func(cPath, sPath string) error {
		out, err := exec.Command(clang, "--target=aarch64-none-elf", "-march=armv8.1-a", "-std=c11", "-O1", "-ffreestanding",
			"-fno-asynchronous-unwind-tables", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-S", cPath, "-o", sPath).CombinedOutput()
		if err != nil {
			return fmt.Errorf("%v\n%s", err, out)
		}
		return nil
	}, "//")
}

func TestTranslationValidationRV64(t *testing.T) {
	// The RISC-V GNU toolchain under any of its prefixes (Homebrew's
	// riscv64-elf-, Debian's riscv64-unknown-elf-, riscv64-linux-gnu-);
	// OAK_REQUIRE_RV64_GCC=1 turns the skip into a failure where CI
	// installs it (the packages shard), so the rung is never silently absent.
	var gcc string
	for _, prefix := range []string{"riscv64-elf-", "riscv64-unknown-elf-", "riscv64-linux-gnu-"} {
		if path, err := exec.LookPath(prefix + "gcc"); err == nil {
			gcc = path
			break
		}
	}
	if gcc == "" {
		if os.Getenv("OAK_REQUIRE_RV64_GCC") != "" {
			t.Fatal("a riscv64 GCC (riscv64-elf-gcc / riscv64-unknown-elf-gcc) is required to compile the prelude helpers for rv64 and OAK_REQUIRE_RV64_GCC is set")
		}
		t.Skip("a riscv64 GCC (riscv64-elf-gcc / riscv64-unknown-elf-gcc) is required to compile the prelude helpers for rv64")
	}
	validateTranslation(t, asm.ArchRV64, func(cPath, sPath string) error {
		out, err := exec.Command(gcc, "-march=rv64gc", "-mabi=lp64d", "-std=c11", "-O1", "-ffreestanding",
			"-fno-asynchronous-unwind-tables", "-Wall", "-Wextra", "-Werror", "-Wno-unused-function", "-S", cPath, "-o", sPath).CombinedOutput()
		if err != nil {
			return fmt.Errorf("%v\n%s", err, out)
		}
		return nil
	}, "#")
}
