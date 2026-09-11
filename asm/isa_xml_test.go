package asm

import (
	"encoding/xml"
	"fmt"
	"github.com/SCKelemen/oak/asm/internal/armfeat"
	"html"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"testing"
)

// Audit of the instruction table against Arm's machine-readable A64 ISA XML
// (docs/spec/94-assembler.md §8, grounding stage 1, operand forms).
//
// Arm publishes the A64 instruction set as XML: one file per instruction
// with its encodings, each carrying an assembler template (`ADD <Wd>, <Wn>,
// <Wm>{, <shift> #<amount>}`), the architecture features it needs, and an
// explanation of every operand symbol (including the size tables behind
// `<V>`). This test reads that release from `external/isa-a64` beside the
// checkout (Arm's notice forbids redistribution, so nothing from it is
// committed) and checks the table two ways:
//
//  1. Operand forms: every template of a mnemonic the table carries, on
//     features the Apple M-series has, is translated to our operand-form
//     vocabulary, and the table must admit it. A template Arm spells that
//     we refuse is a completeness gap; a table form no template spells is
//     reported as suspect. Forms through `sp` beyond the frame discipline
//     are counted, not required.
//  2. Mnemonic coverage: every base or FP/SIMD mnemonic whose features the
//     M-series has (Armv8.7-A and the extensions LLVM enables for apple-m4)
//     must be in the table or on the reasoned exclusion list.
//
// The test skips when the release is absent.

var isaXMLGlob = filepath.Join("..", "..", "external", "isa-a64", "ISA_A64_xml_A_profile-*")

// xmlInstruction mirrors the parts of an instruction file the audit reads.
type xmlInstruction struct {
	Classes struct {
		IClass []struct {
			ArchVariants []struct {
				Feature string `xml:"feature,attr"`
				Name    string `xml:"name,attr"`
			} `xml:"arch_variants>arch_variant"`
			Encodings []struct {
				Name     string `xml:"name,attr"`
				Template struct {
					Inner string `xml:",innerxml"`
				} `xml:"asmtemplate"`
			} `xml:"encoding"`
		} `xml:"iclass"`
	} `xml:"classes"`
	Explanations []struct {
		EncList string `xml:"enclist,attr"`
		Symbol  string `xml:"symbol"`
		Intro   []struct {
			Text string `xml:",innerxml"`
		} `xml:"account>intro"`
		Rows []struct {
			Entries []struct {
				Class string `xml:"class,attr"`
				Text  string `xml:",chardata"`
			} `xml:"entry"`
		} `xml:"definition>table>tgroup>tbody>row"`
	} `xml:"explanations>explanation"`
}

// xmlEncoding is one assembler encoding: the template with its tags
// stripped, its features, and the size tables of its `<V>`-style symbols
// (bit pattern → letter).
type xmlEncoding struct {
	file, name string
	features   []xmlFeature
	template   string
	sizes      map[string]map[string]string
}

type xmlFeature struct {
	name    string // the arch_variant name: an architecture version expression (`v8Ap2`, `(v8Ap2 && PROFILE_A) || (v9Ap2 && PROFILE_A)`)
	feature string // e.g. FEAT_LSE (may be an expression)
	major   int    // architecture version the feature belongs to, -1 if none
	minor   int
}

var (
	xmlTags    = regexp.MustCompile(`<[^>]*>`)
	xmlVersion = regexp.MustCompile(`^v(\d+)Ap(\d+)$`)
)

// loadISAXML reads the base and FP/SIMD instruction files of the newest
// release under the glob.
func loadISAXML(t *testing.T) (string, []xmlEncoding) {
	candidates, _ := filepath.Glob(isaXMLGlob)
	var dirs []string
	for _, c := range candidates {
		if _, err := os.Stat(filepath.Join(c, "index.xml")); err == nil {
			dirs = append(dirs, c)
		}
	}
	if len(dirs) == 0 {
		t.Skip("Arm A64 ISA XML not present under external/isa-a64")
	}
	sort.Strings(dirs)
	dir := dirs[len(dirs)-1]
	var files []string
	for _, index := range []string{"index.xml", "fpsimdindex.xml", "sveindex.xml", "mortlachindex.xml"} {
		data, err := os.ReadFile(filepath.Join(dir, index))
		if err != nil {
			t.Fatal(err)
		}
		for _, m := range regexp.MustCompile(`iformfile="([^"]+)"`).FindAllStringSubmatch(string(data), -1) {
			files = append(files, m[1])
		}
	}
	var encodings []xmlEncoding
	for _, file := range files {
		data, err := os.ReadFile(filepath.Join(dir, file))
		if err != nil {
			t.Fatal(err)
		}
		var instr xmlInstruction
		if err := xml.Unmarshal(data, &instr); err != nil {
			t.Fatalf("%s: %v", file, err)
		}
		// Size tables per encoding: symbol → bit pattern → letter.
		sizes := map[string]map[string]map[string]string{}
		for _, ex := range instr.Explanations {
			symbol := strings.TrimSpace(html.UnescapeString(ex.Symbol))
			table := map[string]string{}
			if len(ex.Rows) == 0 {
				// A single-valued size symbol is explained in prose:
				// "Is the destination width specifier, H."
				if !xmlSizeSymbol.MatchString(symbol) || len(ex.Intro) == 0 {
					continue
				}
				text := strings.TrimSpace(html.UnescapeString(xmlTags.ReplaceAllString(ex.Intro[0].Text, "")))
				m := xmlSizeProse.FindStringSubmatch(text)
				if m == nil {
					continue
				}
				table[""] = m[1]
			}
			for _, row := range ex.Rows {
				var bits, letter string
				for _, entry := range row.Entries {
					switch entry.Class {
					case "bitfield":
						bits += strings.TrimSpace(entry.Text)
					case "symbol":
						letter = strings.TrimSpace(html.UnescapeString(entry.Text))
					}
				}
				if letter != "" && letter != "RESERVED" {
					table[bits] = letter
				}
			}
			for _, enc := range strings.Split(ex.EncList, ",") {
				enc = strings.TrimSpace(enc)
				if sizes[enc] == nil {
					sizes[enc] = map[string]map[string]string{}
				}
				sizes[enc][symbol] = table
			}
		}
		for _, class := range instr.Classes.IClass {
			var features []xmlFeature
			for _, v := range class.ArchVariants {
				f := xmlFeature{name: v.Name, feature: v.Feature, major: -1}
				if m := xmlVersion.FindStringSubmatch(v.Name); m != nil {
					f.major, _ = strconv.Atoi(m[1])
					f.minor, _ = strconv.Atoi(m[2])
				}
				features = append(features, f)
			}
			for _, enc := range class.Encodings {
				template := strings.Join(strings.Fields(html.UnescapeString(xmlTags.ReplaceAllString(enc.Template.Inner, ""))), " ")
				encodings = append(encodings, xmlEncoding{file: file, name: enc.Name, features: features, template: template, sizes: sizes[enc.Name]})
			}
		}
	}
	return dir, encodings
}

// readings expands a template's optional groups and size symbols into the
// concrete spellings it stands for, each as (table mnemonic, operand text).
func (e xmlEncoding) readings() [][2]string {
	var out [][2]string
	for _, t := range expandOptionals(e.template) {
		for _, sized := range e.expandSizes(t) {
			mnemonic, operands := sized, ""
			if i := strings.IndexByte(sized, ' '); i >= 0 {
				mnemonic, operands = sized[:i], strings.TrimSpace(sized[i+1:])
			}
			mnemonic = strings.ToLower(mnemonic)
			switch {
			case strings.HasPrefix(mnemonic, "b.<cond>"):
				mnemonic = "b."
			case strings.HasPrefix(mnemonic, "bc.<cond>"):
				mnemonic = "bc."
			}
			if strings.Contains(mnemonic, "<bt>") { // bfmlal<bt>: the bottom and top halves
				out = append(out, [2]string{strings.ReplaceAll(mnemonic, "<bt>", "b"), operands}, [2]string{strings.ReplaceAll(mnemonic, "<bt>", "t"), operands})
				continue
			}
			out = append(out, [2]string{mnemonic, operands})
		}
	}
	return out
}

var (
	xmlSizeSymbol = regexp.MustCompile(`<V[ab]?>`)
	xmlSizeProse  = regexp.MustCompile(`specifier, ([BHSDQ])\.?$`)
)

// expandSizes replaces the correlated scalar size symbols `<V>`, `<Va>`,
// `<Vb>` by the letters their tables give for each encoding bit pattern
// (so `<Va><d>, <Vb><n>` becomes `<Sd>, <Hn>` and `<Dd>, <Sn>`, never a
// pairing the encoding cannot express). Without a table every size is
// admitted.
func (e xmlEncoding) expandSizes(t string) []string {
	symbols := map[string]bool{}
	for _, s := range xmlSizeSymbol.FindAllString(t, -1) {
		// A symbol with one fixed letter is substituted outright.
		if table := e.sizes[s]; len(table) == 1 && table[""] != "" {
			t = strings.ReplaceAll(t, s+"<", "<"+table[""])
			continue
		}
		symbols[s] = true
	}
	if len(symbols) == 0 {
		return []string{t}
	}
	// Bit patterns every symbol's table defines.
	var patterns []string
	first := true
	for s := range symbols {
		table := e.sizes[s]
		if table == nil {
			continue
		}
		var keep []string
		for bits := range table {
			if first {
				keep = append(keep, bits)
				continue
			}
			for _, p := range patterns {
				if p == bits {
					keep = append(keep, bits)
				}
			}
		}
		patterns, first = keep, false
	}
	var out []string
	if first { // no tables: every letter, independently per symbol
		letters := []string{"B", "H", "S", "D"}
		out = []string{t}
		for s := range symbols {
			var next []string
			for _, r := range out {
				for _, l := range letters {
					next = append(next, strings.ReplaceAll(r, s+"<", "<"+l))
				}
			}
			out = next
		}
		return out
	}
	sort.Strings(patterns)
	for _, bits := range patterns {
		r := t
		for s := range symbols {
			letter := e.sizes[s][bits]
			if letter == "" {
				r = ""
				break
			}
			r = strings.ReplaceAll(r, s+"<", "<"+letter)
		}
		if r != "" {
			out = append(out, r)
		}
	}
	return out
}

// expandOptionals returns every reading of a template with optional groups
// (`{...}`) present or absent.
func expandOptionals(s string) []string {
	depth, start := 0, -1
	for i, r := range s {
		switch r {
		case '{':
			// `{ <Vt>.<T> }` (brace, space) is a register list, not an
			// optional group; leave it for the operand classifier.
			if depth == 0 && !(i+1 < len(s) && s[i+1] == ' ') {
				start = i
			}
			depth++
		case '}':
			depth--
			if depth == 0 && start >= 0 && s[start+1] != ' ' {
				inner := s[start+1 : i]
				with := s[:start] + inner + s[i+1:]
				without := s[:start] + s[i+1:]
				return append(expandOptionals(with), expandOptionals(without)...)
			}
		}
	}
	return []string{s}
}

// splitOperands splits at top-level commas (outside brackets and parens).
func splitOperands(s string) []string {
	var out []string
	depth := 0
	last := 0
	for i, r := range s {
		switch r {
		case '[', '(', '<', '{':
			depth++
		case ']', ')', '>', '}':
			depth--
		case ',':
			if depth == 0 {
				out = append(out, strings.TrimSpace(s[last:i]))
				last = i + 1
			}
		}
	}
	if rest := strings.TrimSpace(s[last:]); rest != "" {
		out = append(out, rest)
	}
	return out
}

var (
	xmlGPReg  = regexp.MustCompile(`^<([WX])(d|n|m|t|s|a|t1|t2|\(s\+1\)|\(t\+1\)|t\+1)(\|(W?SP))?>$`)
	xmlRReg   = regexp.MustCompile(`^<R><[a-z]>$`)
	xmlFPReg  = regexp.MustCompile(`^<([BHSDQ])(d|n|m|a|t|s|t1|t2)>$|^([BHSDQ])<[dnmats]>$`)
	xmlVecArr = regexp.MustCompile(`^<V[a-z0-9+]*>\.(<T[ab]?>|<Ts>|\d+[BHSD]|[BHSD]|2D|1Q)$`)
	xmlVecLn  = regexp.MustCompile(`^(<V[a-z0-9+]*>|V<[a-z]>)\.(<Ts>|<T>|[BHSD]|\d*[BHSD])\[(<index\d?>|\d+)\]$`)
	xmlSysReg = regexp.MustCompile(`^S<op0>_<op1>_<Cn>_<Cm>_<op2>$`)
	xmlOption = map[string]bool{"<option>": true, "<dc_op>": true, "<ic_op>": true, "<tlbi_op>": true, "<at_op>": true, "<prfop>": true, "<rprfop>": true, "<targets>": true, "<gsb_op>": true, "<policy>": true, "CSYNC": true, "DSYNC": true, "SY": true, "nXS": true, "<option>nXS": true}
)

// classifyOperand translates one template operand into our operand classes
// (several when the template admits alternatives). ok=false marks a shape
// the table has no class for; modifier=true marks a trailing shift/extend
// that attaches to the preceding operand.
func classifyOperand(mnemonic, op string) (classes []operandClass, modifier bool, ok bool) {
	switch {
	case strings.HasPrefix(op, "["):
		return []operandClass{opMem}, false, true
	case op == "<label>":
		return []operandClass{opSym}, false, true
	case op == "<cond>" || op == "<invcond>":
		return []operandClass{opCond}, false, true
	case op == "<systemreg>" || op == "<pstatefield>" || xmlSysReg.MatchString(op):
		return []operandClass{opSysReg}, false, true
	case xmlOption[op]:
		return []operandClass{opOption}, false, true
	case strings.HasPrefix(op, "<shift>") || strings.HasPrefix(op, "<extend>") || strings.HasPrefix(op, "LSL") || strings.HasPrefix(op, "MSL"):
		return nil, true, true
	case strings.HasPrefix(op, "#"):
		if strings.Contains(op, ".") || (mnemonic == "fmov" && op == "#<imm>") {
			return []operandClass{opFImm}, false, true
		}
		return []operandClass{opImm}, false, true
	case strings.HasPrefix(op, "{"):
		if strings.Contains(op, "}[") {
			return nil, false, false // structure lane lists
		}
		return []operandClass{opList}, false, true
	}
	if m := xmlGPReg.FindStringSubmatch(op); m != nil {
		class := opX
		if m[1] == "W" {
			class = opW
		}
		classes = []operandClass{class}
		if m[4] == "SP" {
			classes = append(classes, opSP)
		}
		return classes, false, true // wsp is not modeled; the W reading stands
	}
	if xmlRReg.MatchString(op) {
		return []operandClass{opW, opX}, false, true
	}
	if m := xmlFPReg.FindStringSubmatch(op); m != nil {
		letter := m[1] + m[3]
		return []operandClass{map[string]operandClass{"B": opFB, "H": opFH, "S": opFS, "D": opFD, "Q": opFQ}[letter]}, false, true
	}
	if xmlVecLn.MatchString(op) {
		return []operandClass{opVL}, false, true
	}
	if xmlVecArr.MatchString(op) {
		return []operandClass{opVA}, false, true
	}
	return nil, false, false
}

// deriveForms translates one reading's operand text into the operand forms
// it spells. untranslated reports operand shapes outside the vocabulary.
func deriveForms(mnemonic, text string) (forms []form, untranslated []string) {
	operands := splitOperands(text)
	// A post-indexed immediate belongs to the preceding memory operand; a
	// post-index by register is an addressing mode the table has no class for.
	if n := len(operands); n >= 2 && strings.HasPrefix(operands[n-2], "[") && strings.HasSuffix(operands[n-2], "]") {
		switch {
		case strings.HasPrefix(operands[n-1], "#") || operands[n-1] == "<imm>":
			operands = operands[:n-1]
		case xmlGPReg.MatchString(operands[n-1]):
			return nil, []string{"[...], " + operands[n-1] + " (post-index by register)"}
		}
	}
	// Alternatives (`(<prfop>|#<imm5>)`, `<option>|#<imm>`).
	alternatives := [][]string{nil}
	for _, op := range operands {
		choices := []string{op}
		if bare := strings.TrimSuffix(strings.TrimPrefix(op, "("), ")"); strings.Contains(bare, "|") && !strings.HasPrefix(op, "[") && !xmlGPReg.MatchString(op) {
			choices = strings.Split(bare, "|")
		}
		var next [][]string
		for _, prefix := range alternatives {
			for _, choice := range choices {
				next = append(next, append(append([]string{}, prefix...), strings.TrimSpace(choice)))
			}
		}
		alternatives = next
	}
	for _, ops := range alternatives {
		partial := [][]operandClass{{}}
		bad := false
		for _, op := range ops {
			classes, modifier, ok := classifyOperand(mnemonic, op)
			if !ok {
				untranslated = append(untranslated, op)
				bad = true
				break
			}
			if modifier {
				continue
			}
			var next [][]operandClass
			for _, p := range partial {
				for _, c := range classes {
					next = append(next, append(append([]operandClass{}, p...), c))
				}
			}
			partial = next
		}
		if bad {
			continue
		}
		for _, p := range partial {
			if len(p) == 0 {
				p = []operandClass{opNone}
			}
			forms = append(forms, form(p))
		}
	}
	return forms, untranslated
}

func formText(f form) string {
	names := map[operandClass]string{opX: "X", opW: "W", opSP: "SP", opImm: "imm", opMem: "mem", opSym: "label", opSysReg: "sysreg", opOption: "option", opCond: "cond", opNone: "-",
		opFB: "b", opFH: "h", opFS: "s", opFD: "d", opFQ: "q", opVA: "V.T", opVL: "V.T[i]", opList: "{list}", opFImm: "fimm"}
	parts := make([]string, len(f))
	for i, c := range f {
		if n, ok := names[c]; ok {
			parts[i] = n
		} else {
			parts[i] = fmt.Sprintf("op%d", c)
		}
	}
	return strings.Join(parts, ", ")
}

func sameForm(a, b form) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func hasClass(f form, class operandClass) bool {
	for _, c := range f {
		if c == class {
			return true
		}
	}
	return false
}

// mSeriesHas reports whether the Apple M-series has an encoding's features:
// no feature tag, or some arch_variant that holds on the shared profile
// (asm/internal/armfeat: Armv8.7-A, LLVM's apple-m4 extensions, and the
// SME family with streaming SVE).
func mSeriesHas(features []xmlFeature) bool {
	if len(features) == 0 {
		return true
	}
	for _, f := range features {
		if armfeat.Has(f.name, f.feature) {
			return true
		}
	}
	return false
}

// mSeriesAbsentFeatures names the optional features the M-series lacks,
// with the reason shown in reports.
var mSeriesAbsentFeatures = armfeat.Absent

// xmlExcluded lists M-series mnemonics the table leaves out by design.
var xmlExcluded = map[string]string{
	"dcps1": "debug-state entry", "dcps2": "debug-state entry", "dcps3": "debug-state entry", "drps": "debug-state return", "hlt": "halting breakpoint",
	"sys": "raw system operation: the aliases are the spelling", "sysl": "raw system operation with a result",
	"sysp": "128-bit system operation (FEAT_SYSREG128)", "mrrs": "128-bit system register read", "msrr": "128-bit system register write",
	"udf": "permanently undefined: never emitted", "bc.": "hinted conditional branch (FEAT_HBC, v8.8)",
	"chkfeat": "feature check hint (FEAT_CHK, v8.9)", "clrbhb": "branch-history clear (FEAT_CLRBHB, v8.9)",
	"movt": "ZT0 element move (the `zt0[<offs>]` operand is not modeled)", "psel": "predicate select by element index (the `<Pm>.<T>[<Wv>, <imm>]` operand is not modeled)",
}

// xmlFormsNotModeled: forms Arm spells for a table mnemonic that the table
// leaves out by design, with the reason.
var xmlFormsNotModeled = map[string]string{
	"ldr W, label": "literal loads: an asm unit has no data section to place a literal pool in",
	"ldr X, label": "literal loads", "ldr s, label": "literal loads", "ldr d, label": "literal loads", "ldr q, label": "literal loads",
	"ldrsw X, label": "literal loads", "prfm option, label": "literal prefetch", "prfm imm, label": "literal prefetch",
}

func TestISAXMLOperandForms(t *testing.T) {
	dir, encodings := loadISAXML(t)
	spelled := map[string][]form{}     // per table mnemonic: forms the XML spells
	spelledBy := map[string][]string{} // mnemonic+form → encodings
	untranslated := map[string][]string{}
	for _, e := range encodings {
		if !mSeriesHas(e.features) {
			continue
		}
		for _, reading := range e.readings() {
			name := reading[0]
			spec, inTable := instructionTable[name]
			if !inTable || scalableReading(spec, reading[1]) {
				continue // SVE/SME forms are the encoding table's readings (asm/isa_sme.go)
			}
			forms, bad := deriveForms(name, reading[1])
			for _, op := range bad {
				if len(untranslated[op]) < 3 {
					untranslated[op] = append(untranslated[op], e.name)
				}
			}
			for _, f := range forms {
				key := name + " " + formText(f)
				if len(spelledBy[key]) == 0 {
					spelled[name] = append(spelled[name], f)
				}
				spelledBy[key] = append(spelledBy[key], e.name)
			}
		}
	}
	var missing, spForms, extra []string
	for name, forms := range spelled {
		spec := instructionTable[name]
		for _, f := range forms {
			admitted := false
			for _, tf := range spec.forms {
				if sameForm(tf, f) {
					admitted = true
					break
				}
			}
			if admitted {
				continue
			}
			key := name + " " + formText(f)
			line := fmt.Sprintf("  %-8s %-24s (%s)", name, formText(f), strings.Join(dedupe(spelledBy[key]), ", "))
			switch {
			case xmlFormsNotModeled[key] != "":
			case hasClass(f, opSP):
				spForms = append(spForms, line)
			default:
				missing = append(missing, line)
			}
		}
		for _, tf := range spec.forms {
			spelledForm := false
			for _, f := range forms {
				if sameForm(tf, f) {
					spelledForm = true
					break
				}
			}
			if !spelledForm {
				extra = append(extra, fmt.Sprintf("  %-8s %s", name, formText(tf)))
			}
		}
	}
	sort.Strings(missing)
	sort.Strings(spForms)
	sort.Strings(extra)
	var shapes []string
	for op, examples := range untranslated {
		shapes = append(shapes, fmt.Sprintf("%q (%s)", op, strings.Join(examples, ", ")))
	}
	sort.Strings(shapes)
	t.Logf("%s: %d encodings; %d table mnemonics spelled by the XML", filepath.Base(dir), len(encodings), len(spelled))
	t.Logf("%d operand shapes outside the translator's vocabulary:\n  %s", len(shapes), strings.Join(shapes, "\n  "))
	t.Logf("%d forms through sp not modeled (the frame discipline admits `add/sub sp, sp, #imm`):\n%s", len(spForms), strings.Join(spForms, "\n"))
	t.Logf("%d table forms no template spells (forms to review):\n%s", len(extra), strings.Join(extra, "\n"))
	if len(missing) > 0 {
		t.Errorf("%d operand forms Arm spells that the table refuses:\n%s", len(missing), strings.Join(missing, "\n"))
	}
}

// scalableReading: a template of the scalable file (z, p, ZA, ZT0 operands,
// vector-length offsets), or any reading of a mnemonic whose forms are the
// encoding table's alone.
func scalableReading(spec instructionSpec, operands string) bool {
	if spec.tableForms && len(spec.forms) == 0 {
		return true
	}
	for _, marker := range []string{"<Z", "<P", "ZA", "ZT0", "MUL VL", "<pattern>"} {
		if strings.Contains(operands, marker) {
			return true
		}
	}
	return false
}

func dedupe(items []string) []string {
	seen := map[string]bool{}
	var out []string
	for _, item := range items {
		if !seen[item] {
			seen[item] = true
			out = append(out, item)
		}
	}
	return out
}

func TestISAXMLMnemonicCoverage(t *testing.T) {
	dir, encodings := loadISAXML(t)
	missing := map[string][]string{}
	covered := map[string]bool{}
	for _, e := range encodings {
		if !mSeriesHas(e.features) {
			continue
		}
		for _, reading := range e.readings() {
			name := reading[0]
			if _, inTable := instructionTable[name]; inTable {
				covered[e.name] = true
				continue
			}
			if _, excluded := xmlExcluded[name]; excluded {
				continue
			}
			var feats []string
			for _, f := range e.features {
				feats = append(feats, f.feature)
			}
			missing[name] = append(missing[name], e.name+" ["+strings.Join(feats, "|")+"]")
		}
	}
	t.Logf("%s: %d M-series encodings covered by the table", filepath.Base(dir), len(covered))
	if len(missing) > 0 {
		var names []string
		for name := range missing {
			names = append(names, name)
		}
		sort.Strings(names)
		var report strings.Builder
		for _, name := range names {
			fmt.Fprintf(&report, "  %-10s %s\n", name, strings.Join(dedupe(missing[name]), ", "))
		}
		t.Errorf("%d M-series mnemonics in Arm's XML are missing from the table:\n%s", len(missing), report.String())
	}
}
