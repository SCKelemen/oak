// Command isagen derives the AArch64 encoding table of the Oak assembler
// from Arm's machine-readable A64 ISA XML (docs/spec/94-assembler.md §9).
//
//	go run ./asm/internal/isagen -xml ../external/isa-a64/ISA_A64_xml_A_profile-2026-06 -o asm/encodings_gen.go
//
// For every encoding of the base and FP/SIMD instruction set on features the
// Apple M-series has, it writes the fixed bits, the named fields, and each
// assembler template reading with its operands mapped to fields: register
// operands to their register field, immediates with the range, scale, and
// offset Arm's operand explanation states, table-valued symbols (shift and
// extend kinds, conditions, barrier options, arrangements) with their value
// tables, labels with their scale, and alias encodings with the template of
// the instruction they stand for. Only these derived facts are written; none
// of Arm's prose is reproduced.
package main

import (
	"encoding/xml"
	"flag"
	"fmt"
	"html"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"

	"github.com/SCKelemen/oak/asm/internal/armfeat"
)

// ---- XML shapes -----------------------------------------------------------

type instructionFile struct {
	ID      string `xml:"id,attr"`
	Classes struct {
		IClass []iclass `xml:"iclass"`
	} `xml:"classes"`
	Explanations []explanation `xml:"explanations>explanation"`
	// The shared Execute pseudocode of the file: its Check* call states the
	// PSTATE.SM/ZA mode the instruction needs, and its NZCV writes whether
	// it sets the flags.
	Operation []struct {
		Section string `xml:"section,attr"`
		Inner   string `xml:",innerxml"`
	} `xml:"ps_section>ps>pstext"`
}

type iclass struct {
	ArchVariants []struct {
		Feature string `xml:"feature,attr"`
		Name    string `xml:"name,attr"`
	} `xml:"arch_variants>arch_variant"`
	Diagram struct {
		Boxes []box `xml:"box"`
	} `xml:"regdiagram"`
	Encodings []encoding `xml:"encoding"`
	Decode    []struct {
		Section string `xml:"section,attr"`
		Inner   string `xml:",innerxml"`
	} `xml:"ps_section>ps>pstext"`
}

type box struct {
	HiBit int    `xml:"hibit,attr"`
	Width int    `xml:"width,attr"`
	Name  string `xml:"name,attr"`
	Cells []struct {
		ColSpan int    `xml:"colspan,attr"`
		Text    string `xml:",chardata"`
	} `xml:"c"`
}

type encoding struct {
	Name     string `xml:"name,attr"`
	Boxes    []box  `xml:"box"`
	Template struct {
		Inner string `xml:",innerxml"`
	} `xml:"asmtemplate"`
	Equivalent struct {
		Template struct {
			Inner string `xml:",innerxml"`
		} `xml:"asmtemplate"`
		Cond string `xml:"aliascond"`
	} `xml:"equivalent_to"`
}

type explanation struct {
	EncList    string `xml:"enclist,attr"`
	Symbol     string `xml:"symbol"`
	Account    *body  `xml:"account"`
	Definition *body  `xml:"definition"`
}

type body struct {
	EncodedIn string `xml:"encodedin,attr"`
	Intro     struct {
		Inner string `xml:",innerxml"`
	} `xml:"intro"`
	Rows []struct {
		Entries []struct {
			Class string `xml:"class,attr"`
			Text  string `xml:",chardata"`
		} `xml:"entry"`
	} `xml:"table>tgroup>tbody>row"`
}

// ---- derived model ---------------------------------------------------------

type field struct {
	Name  string
	Hi    int
	Width int
}

type tableRow struct {
	Bits []string // one bit pattern per field in the symbol's field list ('x' wildcards allowed)
	Text string   // the symbol's spelling (upper case)
}

type operand struct {
	Sym      string
	Kind     string // gp, fp, vecarr, veclane, imm, fimm, label, table, sysreg, cond, mem, list, text, zreg, zlane, preg, pnreg, tile, slice, zlist, tilemask
	Fields   []string
	Width    int
	SP, ZR   bool
	Min, Max int64
	HasRange bool
	Scale    int64
	Offset   int64
	Table    []tableRow
	Sizes    []tableRow // vecarr/veclane: arrangement table; fp: <V> size table
	Sub      []operand  // memory: base, offset, index, extend, amount; slice: tile, hv, elem, idx, offs, group
	Mode     string     // memory: off, pre, post
	Text     string     // fixed token; zreg/preg/tile/slice: the fixed element size letter
	Special  string     // bitmask, wide, fp8, movi, index, shift-immh, fbits
	Count    int        // zlist: registers in the list; slice: consecutive slices named (offs1:offs2)
	Qual     string     // preg/pnreg: the fixed /M or /Z qualifier
}

type formDef struct {
	Operands []operand
	Defaults []fieldDefault // fields an omitted optional operand leaves at a stated default
}

type fieldDefault struct {
	Field string
	Value uint32
}

type encodingDef struct {
	Name, Mnemonic, Class string
	Mask, Value           uint32
	Fields                []field
	Forms                 []formDef
	Alias                 string
	AliasCond             string
	Mode                  string // "", sm, za, smza, nosm (docs/spec/94-assembler.md §9)
	Flags                 bool   // the Execute pseudocode writes NZCV
}

// isAlias is set while the encoding under construction is an alias (its
// computed immediates come from the equivalence template).
var isAlias bool

var (
	tags           = regexp.MustCompile(`<[^>]*>`)
	rangeRe        = regexp.MustCompile(`in the range (-?\d+) to (-?\d+)`)
	pmRangeRe      = regexp.MustCompile(`in the range \+/-(\d+)([KMG]B)`)
	multipleRe     = regexp.MustCompile(`a multiple of (\d+)`)
	divRe          = regexp.MustCompile(`as <[^>]+>/(\d+)`)
	timesRe        = regexp.MustCompile(`times (\d+)`)
	plusRe         = regexp.MustCompile(`encoded as "[^"]+"(?: field)?(?: times \d+)? plus (\d+)`)
	encodedTimesRe = regexp.MustCompile(`encoded as "[^"]+"(?: field)? times (\d+)`)
	minusRe        = regexp.MustCompile(`encoded as "[^"]+" minus (\d+)`)
	gpRegRe        = regexp.MustCompile(`^<([WX])(d|n|m|t|s|a|dn|t1|t2|\(s\+1\)|\(t\+1\)|t\+1)(\|(W?SP))?>$`)
	rRegRe         = regexp.MustCompile(`^<R><[a-z]+(\|SP)?>$`)
	// Scalable registers and the ZA array (SVE/SME templates).
	zRegRe      = regexp.MustCompile(`^<Z([a-z]+\d?)>(?:\.(<T[b]?>|[BHSDQ]))?$`)
	zLaneRe     = regexp.MustCompile(`^<Z([a-z]+\d?)>(?:\.(<T[b]?>|[BHSDQ]))?\[(<index\d?>|<imm\d?>|\d+)\]$`)
	pRegRe      = regexp.MustCompile(`^<P([a-z]+\d?)>(?:\.(<T>|[BHSDQ]))?(?:/(M|Z|<ZM>))?$`)
	pnRegRe     = regexp.MustCompile(`^<PN([a-z]+\d?)>(?:\.(<T>|[BHSDQ]))?(/Z)?(?:\[(<imm\d?>)\])?$`)
	tileRe      = regexp.MustCompile(`^(<ZA[a-z]*\d?>|ZA\d+)\.(<T>|[BHSDQ])$`)
	sliceRe     = regexp.MustCompile(`^(<ZA[a-z]*\d?>|ZA\d*)(<HV>)?(?:\.(<T>|[BHSDQ]))?\[(<W[a-z]+>), (<offs\d?>|<imm>)(?::(<offs\d>))?(?:, (VGx[24]))?\]$`)
	zRangeRe    = regexp.MustCompile(`^(<Z[a-z]+\d?>(?:\.(?:<T[b]?>|[BHSDQ]))?)-(<Z[a-z]+(\d)>(?:\.(?:<T[b]?>|[BHSDQ]))?)$`)
	pSliceRe    = regexp.MustCompile(`^<P[a-z]+\d?>\.<T>\[`)
	fpRegRe     = regexp.MustCompile(`^<([BHSDQ])(d|n|m|a|t|s|t1|t2)>$|^([BHSDQ])<[dnmats]>$`)
	vRegRe      = regexp.MustCompile(`^<V[ab]?><(dn|[dnmats])>$`)
	vecArrRe    = regexp.MustCompile(`^<V([a-z0-9+]*)>\.(<T[ab]?>|<Ts>|\d+[BHSD]|[BHSD]|2D|1Q)$`)
	vecLaneRe   = regexp.MustCompile(`^(<V[a-z0-9+]*>|V<[a-z]>)\.(<Ts>|<T>|[BHSD]|\d*[BHSD])\[(<index\d?>|\d+)\]$`)
	sysRegRe    = regexp.MustCompile(`^S<op0>_<op1>_<Cn>_<Cm>_<op2>$`)
	symbolRe    = regexp.MustCompile(`<[A-Za-z][A-Za-z0-9_|()+]*>`)
	sizeProseRe = regexp.MustCompile(`specifier, ([BHSDQ])\.?$`)
	encodedInRe = regexp.MustCompile(`encoded in the "([A-Za-z0-9_]+)" field`)
	defaultRe   = regexp.MustCompile(`[Dd]efault(?:s|ing) to '?(#?[A-Za-z0-9]+)'?`)
	undefNeRe   = regexp.MustCompile(`if (\w+)\s+!=\s+'([01]+)' then\s*(?:<a[^>]*>)?EndOfDecode(?:</a>)?\((?:<a[^>]*>)?Decode_UNDEF`)
	sub64Re     = regexp.MustCompile(`encoded as 64 minus`)
	optionSYRe  = regexp.MustCompile(`SY [^.]*encoded as CRm = 0b([01]+)`)
)

// mSeriesHas: some arch_variant of the class holds on the M-series
// profile (asm/internal/armfeat).
func mSeriesHas(class iclass) bool {
	if len(class.ArchVariants) == 0 {
		return true
	}
	for _, v := range class.ArchVariants {
		if armfeat.Has(v.Name, v.Feature) {
			return true
		}
	}
	return false
}

// modeOf derives the PSTATE mode an encoding needs from the Check* call of
// its pseudocode (the class's Decode section first, then the file's
// Execute): sm (streaming SVE mode), za (the ZA array enabled), smza
// (both), nosm (Advanced SIMD that is illegal in streaming mode), or ""
// (legal in either mode). On the M4, SVE exists only in streaming mode, so
// CheckSVEEnabled reads as sm.
func modeOf(texts ...string) string {
	for _, text := range texts {
		switch {
		case strings.Contains(text, "CheckStreamingSVEAndZAEnabled"):
			return "smza"
		case strings.Contains(text, "CheckSMEAndZAEnabled"), strings.Contains(text, "CheckSMEZT0Enabled"):
			return "za"
		case strings.Contains(text, "CheckStreamingSVEEnabled"), strings.Contains(text, "CheckSVEEnabled"):
			return "sm"
		case strings.Contains(text, "CheckFPAdvSIMDEnabled"):
			return "nosm"
		case strings.Contains(text, "CheckFPEnabled"), strings.Contains(text, "CheckSMEEnabled"):
			return ""
		}
	}
	return ""
}

var (
	nzcvRe  = regexp.MustCompile(`PSTATE\.(<N,Z,C,V>|\[N,Z,C,V\]|NZCV)\s*=`)
	checkRe = regexp.MustCompile(`Check[A-Za-z0-9]*Enabled`)
)

// currentDecode is the cleaned Decode pseudocode of the class under
// construction: the offset of an immediate the prose leaves implicit
// (`integer imm = UInt(imm4) + 1` for the count multipliers) is read here.
var currentDecode string

var (
	subRe     = regexp.MustCompile(`encoded as (\d+) minus "`)
	undefInRe = regexp.MustCompile(`if (\w+) (?:IN \{([^}]*)\}|(== '[01x]+')) then\s*EndOfDecode\(Decode_UNDEF`)
	quotedRe  = regexp.MustCompile(`'([01x]+)'`)
	commentRe = regexp.MustCompile(`//[^\n]*`)
)

// fixedByExclusion enumerates a field's values, removes those matching the
// excluded patterns ('x' wild), and reports the bits constant over the
// values that remain.
func fixedByExclusion(width int, patterns [][]string) (mask, value uint32, ok bool) {
	excluded := func(v uint32) bool {
		for _, p := range patterns {
			pat := p[1]
			if len(pat) != width {
				continue
			}
			match := true
			for i := 0; i < width; i++ {
				bit := (v >> uint(width-1-i)) & 1
				if pat[i] == 'x' || pat[i] == '1' && bit == 1 || pat[i] == '0' && bit == 0 {
					continue
				}
				match = false
				break
			}
			if match {
				return true
			}
		}
		return false
	}
	var allowed []uint32
	for v := uint32(0); v < 1<<uint(width); v++ {
		if !excluded(v) {
			allowed = append(allowed, v)
		}
	}
	if len(allowed) == 0 || len(allowed) == 1<<uint(width) {
		return 0, 0, false
	}
	all := uint32(1<<uint(width) - 1)
	mask, value = all, allowed[0]
	for _, v := range allowed[1:] {
		mask &^= v ^ allowed[0]
	}
	return mask, value & mask, mask != 0
}

// decodePlusRe matches the Decode's `= UInt(field) + N;`.
func decodePlusRe(field string) *regexp.Regexp {
	return regexp.MustCompile(`= UInt\(` + regexp.QuoteMeta(field) + `\) \+ (\d+);`)
}

// setsFlags reports an Execute section that writes the condition flags.
func setsFlags(texts ...string) bool {
	for _, text := range texts {
		if nzcvRe.MatchString(html.UnescapeString(tags.ReplaceAllString(text, ""))) {
			return true
		}
	}
	return false
}

func main() {
	xmlDir := flag.String("xml", "", "directory of the A64 ISA XML release")
	out := flag.String("o", "asm/encodings_gen.go", "output Go file")
	flag.Parse()
	if *xmlDir == "" {
		fmt.Fprintln(os.Stderr, "isagen: -xml is required")
		os.Exit(2)
	}
	var files []string
	seen := map[string]bool{}
	// The base and SIMD&FP sets, then SVE (its streaming-legal part) and SME.
	for _, index := range []string{"index.xml", "fpsimdindex.xml", "sveindex.xml", "mortlachindex.xml"} {
		data, err := os.ReadFile(filepath.Join(*xmlDir, index))
		if err != nil {
			fail(err)
		}
		for _, m := range regexp.MustCompile(`iformfile="([^"]+)"`).FindAllStringSubmatch(string(data), -1) {
			if !seen[m[1]] {
				seen[m[1]] = true
				files = append(files, m[1])
			}
		}
	}
	var defs []encodingDef
	skipped := map[string]int{}
	for _, file := range files {
		data, err := os.ReadFile(filepath.Join(*xmlDir, file))
		if err != nil {
			fail(err)
		}
		var instr instructionFile
		if err := xml.Unmarshal(data, &instr); err != nil {
			fail(fmt.Errorf("%s: %w", file, err))
		}
		var execute []string
		for _, ps := range instr.Operation {
			execute = append(execute, ps.Inner)
		}
		executeText := strings.Join(execute, "")
		for _, class := range instr.Classes.IClass {
			if !mSeriesHas(class) {
				continue
			}
			classMask, classValue, fields := diagramBits(class.Diagram.Boxes)
			var decode []string
			for _, ps := range class.Decode {
				decode = append(decode, ps.Inner)
			}
			decodeText := strings.Join(decode, "")
			// Non-streaming SVE is not on the M4: the class's Decode says so,
			// or the file's shared Execute does when the Decode says nothing.
			checked := decodeText
			if !checkRe.MatchString(decodeText) {
				checked = executeText
			}
			if strings.Contains(checked, "CheckNonStreamingSVEEnabled") && len(checkRe.FindAllString(checked, -1)) == strings.Count(checked, "CheckNonStreamingSVEEnabled") {
				// Unconditionally non-streaming (a conditional one, `if esize
				// == 128 then CheckNonStreamingSVEEnabled() else
				// CheckSVEEnabled()`, guards a variant the M4 lacks anyway).
				skipped["non-streaming SVE (not on the M4)"]++
				continue
			}
			mode := modeOf(decodeText, executeText)
			flags := setsFlags(decodeText, executeText)
			currentDecode = clean(decodeText)
			// Decode-time `if F != 'bits' then UNDEFINED` fixes a field; `if F
			// IN {'0x'} then UNDEFINED` (or `== 'bits'`) excludes patterns, and
			// the bits constant over what remains are fixed too.
			for _, ps := range class.Decode {
				if ps.Section != "Decode" {
					continue
				}
				for _, m := range undefNeRe.FindAllStringSubmatch(ps.Inner, -1) {
					for _, f := range fields {
						if f.Name == m[1] && len(m[2]) == f.Width {
							v, _ := strconv.ParseUint(m[2], 2, 32)
							low := uint(f.Hi - f.Width + 1)
							classMask |= uint32(1<<uint(f.Width)-1) << low
							classValue |= uint32(v) << low
						}
					}
				}
				// Only a top-level `if`: one nested under another condition
				// (`if cmode::op == '11111' then if Q == '0' then UNDEFINED`)
				// constrains nothing on its own.
				flat := commentRe.ReplaceAllString(tags.ReplaceAllString(ps.Inner, ""), "")
				for _, loc := range undefInRe.FindAllStringSubmatchIndex(flat, -1) {
					before := strings.TrimSpace(flat[:loc[0]])
					if before != "" && !strings.HasSuffix(before, ";") {
						continue
					}
					m := undefInRe.FindStringSubmatch(flat[loc[0]:loc[1]])
					patterns := quotedRe.FindAllStringSubmatch(m[2]+m[3], -1)
					for _, f := range fields {
						if f.Name != m[1] || f.Width > 6 {
							continue
						}
						mask, value, ok := fixedByExclusion(f.Width, patterns)
						if ok {
							low := uint(f.Hi - f.Width + 1)
							classMask |= mask << low
							classValue = classValue&^(mask<<low) | value<<low
						}
					}
				}
			}
			for _, enc := range class.Encodings {
				mask, value := classMask, classValue
				for _, b := range enc.Boxes {
					m, v, _ := boxBits(b)
					mask |= m
					value = value&^m | v
				}
				def := encodingDef{Name: enc.Name, Mask: mask, Value: value, Fields: fields, Mode: mode, Flags: flags}
				isAlias = clean(enc.Equivalent.Template.Inner) != ""
				template := clean(enc.Template.Inner)
				if template == "" {
					skipped["no template"]++
					continue
				}
				readings := expandOptionals(template)
				if strings.Contains(template, "<bt>") {
					var both []string
					for _, r := range readings {
						both = append(both, strings.Replace(r, "<bt>", "B", 1), strings.Replace(r, "<bt>", "T", 1))
					}
					readings = both
				}
				for _, r := range readings {
					mnemonic, ops := splitMnemonic(r)
					if def.Mnemonic == "" {
						def.Mnemonic = mnemonic
					}
					if mnemonic != def.Mnemonic {
						// A template whose mnemonic varies (FCVTL{2}) becomes two encodings.
						continue
					}
					form, why := buildForm(enc.Name, ops, instr.Explanations)
					if why != "" {
						skipped[why]++
						continue
					}
					form.Defaults = omittedDefaults(enc.Name, template, r, instr.Explanations)
					def.Forms = append(def.Forms, form)
				}
				// Mnemonic variants from optional groups in the mnemonic itself.
				extra := map[string]*encodingDef{}
				// `<bt>` (bfmlalb/bfmlalt) is a field value: its table names it.
				btMask, btValue := map[string]uint32{}, map[string]uint32{}
				if b := explain(enc.Name, "<bt>", instr.Explanations); b != nil {
					for _, row := range tableOf(b) {
						for i, f := range fieldsOf(b) {
							for _, fd := range fields {
								if fd.Name == f {
									v, _ := strconv.ParseUint(row.Bits[i], 2, 32)
									low := uint(fd.Hi - fd.Width + 1)
									btMask[row.Text] |= uint32(1<<uint(fd.Width)-1) << low
									btValue[row.Text] |= uint32(v) << low
								}
							}
						}
					}
				}
				if strings.Contains(template, "<bt>") && def.Mnemonic != "" {
					letter := strings.ToUpper(def.Mnemonic[len(def.Mnemonic)-1:])
					def.Mask |= btMask[letter]
					def.Value = def.Value&^btMask[letter] | btValue[letter]
				}
				for _, r := range readings {
					mnemonic, ops := splitMnemonic(r)
					if mnemonic == def.Mnemonic {
						continue
					}
					d := extra[mnemonic]
					if d == nil {
						copyDef := def
						copyDef.Forms = nil
						copyDef.Mnemonic = mnemonic
						copyDef.Name = enc.Name + "_" + strings.ToUpper(mnemonic)
						if strings.Contains(template, "<bt>") {
							letter := strings.ToUpper(mnemonic[len(mnemonic)-1:])
							copyDef.Mask = def.Mask&^btMask["B"]&^btMask["T"] | btMask[letter]
							copyDef.Value = def.Value&^btMask["B"]&^btMask["T"] | btValue[letter]
						}
						d = &copyDef
						extra[mnemonic] = d
					}
					form, why := buildForm(enc.Name, ops, instr.Explanations)
					if why != "" {
						skipped[why]++
						continue
					}
					form.Defaults = omittedDefaults(enc.Name, template, r, instr.Explanations)
					d.Forms = append(d.Forms, form)
				}
				if alias := clean(enc.Equivalent.Template.Inner); alias != "" {
					def.Alias = alias
					def.AliasCond = strings.TrimSpace(enc.Equivalent.Cond)
				}
				if len(def.Forms) > 0 {
					defs = append(defs, def)
				}
				var names []string
				for name := range extra {
					names = append(names, name)
				}
				sort.Strings(names)
				for _, name := range names {
					if len(extra[name].Forms) > 0 {
						defs = append(defs, *extra[name])
					}
				}
			}
		}
	}
	sort.Slice(defs, func(i, j int) bool {
		if defs[i].Mnemonic != defs[j].Mnemonic {
			return defs[i].Mnemonic < defs[j].Mnemonic
		}
		return defs[i].Name < defs[j].Name
	})
	if err := os.WriteFile(*out, []byte(render(filepath.Base(*xmlDir), defs)), 0o644); err != nil {
		fail(err)
	}
	var reasons []string
	for why, n := range skipped {
		reasons = append(reasons, fmt.Sprintf("%d %s", n, why))
	}
	sort.Strings(reasons)
	fmt.Fprintf(os.Stderr, "isagen: %d encodings written to %s; skipped readings: %s\n", len(defs), *out, strings.Join(reasons, "; "))
}

// omittedDefaults finds the symbols of the full template a reading omits
// and, when their explanation states a default ("Defaults to X30 if
// absent", "defaulting to 15", "defaulting to SY"), the field values that
// default implies.
func omittedDefaults(enc, full, reading string, explanations []explanation) []fieldDefault {
	present := map[string]bool{}
	for _, s := range symbolRe.FindAllString(reading, -1) {
		present[s] = true
	}
	var out []fieldDefault
	seen := map[string]bool{}
	for _, s := range symbolRe.FindAllString(full, -1) {
		if present[s] || seen[s] {
			continue
		}
		seen[s] = true
		b := explain(enc, s, explanations)
		if b == nil {
			continue
		}
		text := introText(b)
		m := defaultRe.FindStringSubmatch(text)
		if m == nil {
			continue
		}
		word := strings.TrimPrefix(m[1], "#")
		fields := fieldsOf(b)
		if len(fields) == 0 {
			continue
		}
		switch {
		case strings.Contains(m[0], "'"):
			n, err := strconv.ParseUint(word, 2, 32)
			if err == nil {
				out = append(out, fieldDefault{Field: fields[0], Value: uint32(n)})
			}
		case regexp.MustCompile(`^[XW]\d+$`).MatchString(word):
			n, _ := strconv.Atoi(word[1:])
			out = append(out, fieldDefault{Field: fields[0], Value: uint32(n)})
		case word == "XZR" || word == "WZR":
			out = append(out, fieldDefault{Field: fields[0], Value: 31})
		case regexp.MustCompile(`^\d+$`).MatchString(word):
			// The default value as the operand states it, encoded as its
			// explanation says ("encoded as imm4 minus 1": field = value - 1).
			n, _ := strconv.ParseInt(word, 10, 64)
			scale, offset := int64(1), int64(0)
			if sm := multipleRe.FindStringSubmatch(text); sm != nil {
				scale, _ = strconv.ParseInt(sm[1], 10, 64)
			}
			if sm := plusRe.FindStringSubmatch(text); sm != nil {
				offset, _ = strconv.ParseInt(sm[1], 10, 64)
			}
			if sm := minusRe.FindStringSubmatch(text); sm != nil {
				v, _ := strconv.ParseInt(sm[1], 10, 64)
				offset = -v
			}
			if offset == 0 && scale == 1 {
				if sm := decodePlusRe(fields[0]).FindStringSubmatch(currentDecode); sm != nil {
					offset, _ = strconv.ParseInt(sm[1], 10, 64) // the Decode's `UInt(imm4) + 1`
				}
			}
			if scale > 0 && n%scale == 0 && n/scale-offset >= 0 {
				out = append(out, fieldDefault{Field: fields[0], Value: uint32(n/scale - offset)})
			}
		default:
			for _, row := range tableOf(b) {
				if row.Text == strings.ToUpper(word) && len(row.Bits) == len(fields) {
					for i, f := range fields {
						if v, err := strconv.ParseUint(row.Bits[i], 2, 32); err == nil {
							out = append(out, fieldDefault{Field: f, Value: uint32(v)})
						}
					}
				}
			}
			if s == "<option>" {
				if om := optionSYRe.FindStringSubmatch(text); om != nil && strings.ToUpper(word) == "SY" {
					v, _ := strconv.ParseUint(om[1], 2, 32)
					out = append(out, fieldDefault{Field: fields[0], Value: uint32(v)})
				}
			}
		}
	}
	// A table row spelled `[absent]` states the omitted operand's bits
	// (smstart's mode: SM, ZA, or both when absent).
	for _, s := range symbolRe.FindAllString(full, -1) {
		if present[s] || !seen[s] {
			continue
		}
		b := explain(enc, s, explanations)
		if b == nil || defaultRe.MatchString(introText(b)) {
			continue
		}
		fields := fieldsOf(b)
		for _, row := range tableOf(b) {
			if row.Text == "[ABSENT]" && len(row.Bits) == len(fields) {
				for i, f := range fields {
					if v, err := strconv.ParseUint(row.Bits[i], 2, 32); err == nil {
						out = append(out, fieldDefault{Field: f, Value: uint32(v)})
					}
				}
			}
		}
	}
	return out
}

func fail(err error) {
	fmt.Fprintln(os.Stderr, "isagen:", err)
	os.Exit(1)
}

func clean(inner string) string {
	return strings.Join(strings.Fields(html.UnescapeString(tags.ReplaceAllString(inner, ""))), " ")
}

// diagramBits reads an instruction class diagram: fixed bits and named fields.
func diagramBits(boxes []box) (mask, value uint32, fields []field) {
	for _, b := range boxes {
		m, v, named := boxBits(b)
		mask |= m
		value |= v
		if named {
			fields = append(fields, field{Name: b.Name, Hi: b.HiBit, Width: widthOf(b)})
		}
	}
	return mask, value, fields
}

func widthOf(b box) int {
	if b.Width > 0 {
		return b.Width
	}
	return 1
}

// boxBits reads one box: cells spelling constant bits set mask/value bits
// (`(1)` counts as fixed); `x`, `N`, `!=` constraints, and empty cells are
// variable. named reports a field the templates may refer to.
func boxBits(b box) (mask, value uint32, named bool) {
	width := widthOf(b)
	pos := b.HiBit // current high bit of the next cell
	for _, cell := range b.Cells {
		span := cell.ColSpan
		if span == 0 {
			span = 1
		}
		text := strings.TrimSpace(cell.Text)
		if text == "(1)" {
			text = "1"
		}
		if len(text) == span && strings.Trim(text, "01x") == "" {
			for i, ch := range text {
				bit := pos - i
				if ch == 'x' {
					continue
				}
				mask |= 1 << uint(bit)
				if ch == '1' {
					value |= 1 << uint(bit)
				}
			}
		}
		pos -= span
	}
	_ = width
	return mask, value, b.Name != ""
}

// expandOptionals returns every reading of a template with optional groups
// present or absent. `{ ` (brace, space) opens a register list, not a group.
func expandOptionals(s string) []string {
	depth, start := 0, -1
	for i, r := range s {
		switch r {
		case '{':
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

func splitMnemonic(reading string) (string, string) {
	mnemonic, operands := reading, ""
	if i := strings.IndexByte(reading, ' '); i >= 0 {
		mnemonic, operands = reading[:i], strings.TrimSpace(reading[i+1:])
	}
	mnemonic = strings.ToLower(mnemonic)
	if strings.HasPrefix(mnemonic, "b.<cond>") {
		return "b.", "<cond>, " + operands
	}
	if strings.HasPrefix(mnemonic, "bc.<cond>") {
		return "bc.", "<cond>, " + operands
	}
	return mnemonic, operands
}

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

// explain finds the explanation of a symbol for an encoding.
func explain(enc, sym string, explanations []explanation) *body {
	var fallback *body
	for i := range explanations {
		ex := &explanations[i]
		if strings.TrimSpace(html.UnescapeString(ex.Symbol)) != sym {
			continue
		}
		b := ex.Account
		if b == nil {
			b = ex.Definition
		}
		if b == nil {
			continue
		}
		for _, e := range strings.Split(ex.EncList, ",") {
			if strings.TrimSpace(e) == enc {
				return b
			}
		}
		if fallback == nil {
			fallback = b
		}
	}
	return fallback
}

func tableOf(b *body) []tableRow {
	if b == nil {
		return nil
	}
	var rows []tableRow
	for _, row := range b.Rows {
		var r tableRow
		for _, e := range row.Entries {
			text := strings.TrimSpace(html.UnescapeString(e.Text))
			switch e.Class {
			case "bitfield":
				r.Bits = append(r.Bits, text)
			case "symbol":
				r.Text = strings.ToUpper(text)
			}
		}
		if r.Text != "" && r.Text != "RESERVED" && !strings.HasPrefix(r.Text, "UINT") && !strings.Contains(r.Text, "UINT(") {
			rows = append(rows, r)
		}
	}
	return rows
}

// fieldsOf splits an `encodedin` list ("sf:imm6", "(imms :: immr)",
// "op2[2:1]") at the top-level colons; slices in brackets stay whole.
func fieldsOf(b *body) []string {
	if b == nil || b.EncodedIn == "" {
		return nil
	}
	s := strings.NewReplacer("(", "", ")", "", " ", "").Replace(b.EncodedIn)
	s = strings.ReplaceAll(s, "::", ":")
	var out []string
	depth, last := 0, 0
	for i, r := range s {
		switch r {
		case '[', '<':
			depth++
		case ']', '>':
			depth--
		case ':':
			if depth == 0 {
				out = append(out, s[last:i])
				last = i + 1
			}
		}
	}
	return append(out, s[last:])
}

func introText(b *body) string {
	if b == nil {
		return ""
	}
	return clean(b.Intro.Inner)
}

// buildForm translates one operand reading into operands mapped to fields.
func buildForm(enc, text string, explanations []explanation) (formDef, string) {
	var form formDef
	tokens := splitOperands(text)
	// A post-indexed immediate or register belongs to the memory operand.
	if n := len(tokens); n >= 2 && strings.HasPrefix(tokens[n-2], "[") && strings.HasSuffix(tokens[n-2], "]") {
		last := tokens[n-1]
		if strings.HasPrefix(last, "#") || last == "<imm>" {
			tokens[n-2] = tokens[n-2] + ", " + last + "@post"
			tokens = tokens[:n-1]
		} else if gpRegRe.MatchString(last) {
			return form, "post-index by register"
		}
	}
	for i := 0; i < len(tokens); i++ {
		tok := tokens[i]
		// Trailing shift/extend modifiers attach to the previous operand.
		if strings.HasPrefix(tok, "<shift>") || strings.HasPrefix(tok, "<extend>") || strings.HasPrefix(tok, "LSL") || strings.HasPrefix(tok, "MSL") || strings.HasPrefix(tok, "MUL #") {
			mod, why := modifierOperands(enc, tok, explanations)
			if why != "" {
				return form, why
			}
			form.Operands = append(form.Operands, mod...)
			continue
		}
		op, why := classify(enc, tok, explanations)
		if why != "" {
			return form, why
		}
		form.Operands = append(form.Operands, op)
	}
	return form, ""
}

// modifierOperands: `<shift> #<amount>`, `<extend>`, `<extend> #<amount>`,
// `LSL #<amount>`, `LSL #<shift>`, `LSL #0`, `MSL #<amount>`, `<shift>`.
func modifierOperands(enc, tok string, explanations []explanation) ([]operand, string) {
	var out []operand
	parts := strings.Fields(tok)
	for _, p := range parts {
		switch {
		case p == "<shift>" || p == "<extend>":
			b := explain(enc, p, explanations)
			if b == nil {
				return nil, "modifier without explanation: " + p
			}
			out = append(out, operand{Sym: p, Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)})
		case p == "LSL" || p == "MSL" || p == "MUL":
			out = append(out, operand{Sym: p, Kind: "text", Text: p})
		case strings.HasPrefix(p, "#"):
			op, why := classify(enc, p, explanations)
			if why != "" {
				return nil, why
			}
			out = append(out, op)
		default:
			return nil, "modifier shape: " + tok
		}
	}
	return out, ""
}

// indexRows keeps the per-size index formulas of an `<index>` explanation
// ("size <index> 01 UInt(H:L:M) 10 UInt(H:L)") as rows whose text names
// the fields holding the index, most significant first.
func indexRows(b *body) []tableRow {
	var rows []tableRow
	for _, row := range b.Rows {
		var r tableRow
		for _, e := range row.Entries {
			text := strings.TrimSpace(html.UnescapeString(e.Text))
			switch e.Class {
			case "bitfield":
				r.Bits = append(r.Bits, text)
			case "symbol":
				if strings.HasPrefix(text, "UInt(") {
					inner := strings.TrimSuffix(strings.TrimPrefix(text, "UInt("), ")")
					r.Text = strings.ReplaceAll(strings.ReplaceAll(inner, " ", ""), "::", ":")
				}
			}
		}
		if r.Text != "" {
			rows = append(rows, r)
		}
	}
	return rows
}

func immediate(enc, sym string, explanations []explanation) (operand, string) {
	op := operand{Sym: sym, Kind: "imm", Scale: 1}
	if strings.Contains(sym, ".") || strings.HasPrefix(sym, "#-") && strings.Contains(sym, ".") {
		op.Kind = "fimm"
	}
	inner := strings.TrimPrefix(sym, "#")
	if _, err := strconv.ParseInt(inner, 10, 64); err == nil {
		op.Kind = "text"
		op.Text = sym
		return op, ""
	}
	if _, err := strconv.ParseFloat(inner, 64); err == nil {
		op.Kind = "text"
		op.Text = sym
		return op, ""
	}
	b := explain(enc, inner, explanations)
	if b == nil {
		return op, "immediate without explanation: " + sym
	}
	op.Fields = fieldsOf(b)
	text := introText(b)
	if m := encodedInRe.FindStringSubmatch(text); m != nil {
		op.Fields = []string{m[1]} // the prose names the one field the value goes in
	}
	rows := tableOf(b)
	if len(rows) == 0 && (strings.Contains(inner, "index") || strings.Contains(text, "UInt(")) {
		rows = indexRows(b) // per-size index formulas: which fields hold the index
		if len(rows) > 0 {
			op.Special = "index"
			op.Table = rows
			return op, ""
		}
	}
	if len(rows) == 0 {
		// Arrangement and size fields are chosen by the vector operands.
		var kept []string
		for _, f := range op.Fields {
			switch f {
			case "Q", "size", "sz":
				continue
			}
			kept = append(kept, f)
		}
		op.Fields = kept
	}
	if isAlias && (!strings.Contains(text, "encoded") || strings.Contains(text, "-<")) {
		op.Special = "computed" // the field value comes from the alias's equivalence expression
	}
	if sub64Re.MatchString(text) {
		op.Special = "sub64"
	}
	if m := rangeRe.FindStringSubmatch(text); m != nil {
		op.Min, _ = strconv.ParseInt(m[1], 10, 64)
		op.Max, _ = strconv.ParseInt(m[2], 10, 64)
		op.HasRange = true
	}
	if m := multipleRe.FindStringSubmatch(text); m != nil {
		op.Scale, _ = strconv.ParseInt(m[1], 10, 64)
	}
	if m := divRe.FindStringSubmatch(text); m != nil {
		op.Scale, _ = strconv.ParseInt(m[1], 10, 64)
	}
	if m := encodedTimesRe.FindStringSubmatch(text); m != nil {
		op.Scale, _ = strconv.ParseInt(m[1], 10, 64) // `encoded as "off3" times 2`
	}
	if m := plusRe.FindStringSubmatch(text); m != nil {
		op.Offset, _ = strconv.ParseInt(m[1], 10, 64)
	}
	if m := minusRe.FindStringSubmatch(text); m != nil {
		v, _ := strconv.ParseInt(m[1], 10, 64)
		op.Offset = -v
	}
	if op.Offset == 0 && op.Scale == 1 && len(op.Fields) == 1 && op.Special == "" && !isAlias && len(rows) == 0 {
		// The prose says only "encoded in the imm4 field" while the Decode
		// computes `UInt(imm4) + 1`: the offset the prose leaves implicit.
		if m := decodePlusRe(op.Fields[0]).FindStringSubmatch(currentDecode); m != nil {
			op.Offset, _ = strconv.ParseInt(m[1], 10, 64)
		}
	}
	if m := subRe.FindStringSubmatch(text); m != nil && op.Special == "" {
		// `encoded as 16 minus "imm4"`: the field holds N - value.
		op.Special = "sub"
		op.Offset, _ = strconv.ParseInt(m[1], 10, 64)
	}
	if len(rows) > 0 {
		op.Kind = "table"
		op.Table = rows
	}
	joined := strings.Join(op.Fields, ":")
	switch {
	case op.Special == "sub64":
	case joined == "tszh:tszl:imm3" && strings.Contains(text, "shift amount"):
		// The SVE shift by immediate: tsize = esize + shift (left) or
		// 2*esize - shift (right), the element size in the top bits.
		if strings.Contains(text, "in the range 0 to") {
			op.Special = "sve-shift-left"
		} else {
			op.Special = "sve-shift-right"
		}
		op.HasRange = false
	case joined == "imm2:tsz" && strings.Contains(text, "index"):
		op.Special = "sve-index" // the index above the element-size marker bit
	case strings.Contains(text, "bitmask immediate"):
		op.Special = "bitmask"
	case strings.Contains(text, "floating-point constant"), strings.Contains(text, "floating-point immediate value expressible"):
		op.Kind = "fimm"
		op.Special = "fp8"
	case strings.Contains(strings.Join(op.Fields, ":"), "a:b:c:d:e:f:g:h"):
		op.Special = "movi"
	case strings.Contains(text, `can be encoded in "imm16:hw"`), strings.Contains(text, "wide immediate"):
		op.Special = "wide"
	case strings.Contains(text, "fractional bits"):
		op.Special = "fbits"
	case strings.Contains(strings.Join(op.Fields, ":"), "immh") && !strings.Contains(text, "fractional"):
		op.Special = "shift-immh"
	}
	return op, ""
}

func classify(enc, tok string, explanations []explanation) (operand, string) {
	if op, why, matched := scalable(enc, tok, explanations); matched {
		return op, why
	}
	switch {
	case strings.HasPrefix(tok, "["):
		return memory(enc, tok, explanations)
	case tok == "<label>":
		b := explain(enc, tok, explanations)
		if b == nil {
			return operand{}, "label without explanation"
		}
		op := operand{Sym: tok, Kind: "label", Fields: fieldsOf(b), Scale: 1}
		text := introText(b)
		if m := timesRe.FindStringSubmatch(text); m != nil {
			op.Scale, _ = strconv.ParseInt(m[1], 10, 64)
		}
		if m := pmRangeRe.FindStringSubmatch(text); m != nil {
			n, _ := strconv.ParseInt(m[1], 10, 64)
			switch m[2] {
			case "KB":
				n <<= 10
			case "MB":
				n <<= 20
			case "GB":
				n <<= 30
			}
			op.Min, op.Max, op.HasRange = -n, n-1, true
		}
		return op, ""
	case tok == "<cond>" || tok == "<invcond>":
		b := explain(enc, tok, explanations)
		op := operand{Sym: tok, Kind: "cond", Fields: []string{"cond"}}
		if b != nil {
			op.Fields = fieldsOf(b)
			op.Table = tableOf(b)
		}
		return op, ""
	case tok == "<systemreg>" || sysRegRe.MatchString(tok) || tok == "<pstatefield>":
		b := explain(enc, "<systemreg>", explanations)
		op := operand{Sym: tok, Kind: "sysreg", Fields: []string{"o0", "op1", "CRn", "CRm", "op2"}}
		if tok == "<pstatefield>" {
			b = explain(enc, tok, explanations)
			op.Kind = "table"
			op.Fields = fieldsOf(b)
			op.Table = tableOf(b)
		} else if b != nil && len(fieldsOf(b)) > 0 {
			op.Fields = fieldsOf(b)
		}
		return op, ""
	case strings.HasPrefix(tok, "#"):
		return immediate(enc, tok, explanations)
	case strings.HasPrefix(tok, "{"):
		if strings.Contains(tok, "}[") {
			return operand{}, "structure lane list"
		}
		return list(enc, tok, explanations)
	case strings.Contains(tok, "|") && !strings.HasPrefix(tok, "[") && !gpRegRe.MatchString(tok) && !rRegRe.MatchString(tok):
		// Alternatives such as (<prfop>|#<imm5>) or (<systemreg>|S<op0>_...):
		// the first spelling that explains itself stands for the operand
		// (the encoder accepts both spellings through the same fields).
		alts := strings.Split(strings.TrimSuffix(strings.TrimPrefix(tok, "("), ")"), "|")
		op, why := classify(enc, strings.TrimSpace(alts[0]), explanations)
		if why != "" {
			return classify(enc, strings.TrimSpace(alts[1]), explanations)
		}
		if len(alts) > 1 {
			if second, why2 := classify(enc, strings.TrimSpace(alts[1]), explanations); why2 == "" && second.Kind == "imm" && op.Kind == "table" {
				op.Special = "table-or-imm"
			}
		}
		return op, ""
	}
	if m := gpRegRe.FindStringSubmatch(tok); m != nil {
		width := 64
		if m[1] == "W" {
			width = 32
		}
		b := explain(enc, tok, explanations)
		op := operand{Sym: tok, Kind: "gp", Width: width, SP: m[4] != "", ZR: m[4] == ""}
		if b != nil && !strings.Contains(tok, "+1") {
			op.Fields = fieldsOf(b)
		}
		if len(op.Fields) == 0 {
			// <X(s+1)>, <X(t+1)>: the register after another operand's.
			f := regFieldFor(m[2])
			if !strings.HasPrefix(f, "+") {
				f = "+" + f
			}
			op.Fields = []string{f}
		}
		return op, ""
	}
	if rRegRe.MatchString(tok) {
		b := explain(enc, "<R>", explanations)
		op := operand{Sym: tok, Kind: "gp", Width: 0, ZR: !strings.Contains(tok, "|SP"), SP: strings.Contains(tok, "|SP")}
		tok = strings.Replace(tok, "|SP", "", 1)
		if b != nil {
			op.Table = tableOf(b) // W/X by the option field
			op.Sizes = op.Table
		}
		fieldName := "R" + strings.Trim(tok[strings.LastIndex(tok, "<"):], "<>")
		if mb := explain(enc, "<"+strings.Trim(tok[strings.LastIndex(tok, "<"):], "<>")+">", explanations); mb != nil && len(fieldsOf(mb)) > 0 {
			fieldName = fieldsOf(mb)[0]
		}
		op.Fields = []string{fieldName}
		if b != nil {
			op.Fields = append(op.Fields, fieldsOf(b)...) // the width table's fields
		}
		return op, ""
	}
	if m := fpRegRe.FindStringSubmatch(tok); m != nil {
		letter := m[1] + m[3]
		op := operand{Sym: tok, Kind: "fp", Width: map[string]int{"B": 8, "H": 16, "S": 32, "D": 64, "Q": 128}[letter]}
		if b := explain(enc, tok, explanations); b != nil {
			op.Fields = fieldsOf(b)
		}
		if len(op.Fields) == 0 {
			op.Fields = []string{regFieldFor(strings.Trim(tok, "<>BHSDQ"))}
		}
		return op, ""
	}
	if vRegRe.MatchString(tok) {
		// <V><d>: the size comes from a table on the encoding's size field.
		sizeSym := tok[:strings.Index(tok, ">")+1]
		regSym := tok[strings.Index(tok, ">")+1:]
		op := operand{Sym: tok, Kind: "fp", Width: 0}
		if b := explain(enc, sizeSym, explanations); b != nil {
			op.Sizes = tableOf(b)
			if len(op.Sizes) == 0 {
				if m := sizeProseRe.FindStringSubmatch(introText(b)); m != nil {
					op.Width = map[string]int{"B": 8, "H": 16, "S": 32, "D": 64, "Q": 128}[m[1]]
				}
			} else {
				op.Fields = fieldsOf(b)
			}
		}
		if b := explain(enc, regSym, explanations); b != nil && len(fieldsOf(b)) > 0 {
			op.Fields = append([]string{fieldsOf(b)[0]}, op.Fields...)
		} else {
			op.Fields = append([]string{regFieldFor(strings.Trim(regSym, "<>"))}, op.Fields...)
		}
		return op, ""
	}
	if m := vecLaneRe.FindStringSubmatch(tok); m != nil {
		op := operand{Sym: tok, Kind: "veclane"}
		regSym := m[1]
		if strings.HasPrefix(regSym, "V<") {
			regSym = "<" + strings.Trim(regSym, "V<>") + ">"
			if b := explain(enc, regSym, explanations); b != nil {
				op.Fields = fieldsOf(b)
			}
		} else if b := explain(enc, regSym, explanations); b != nil {
			op.Fields = fieldsOf(b)
		}
		if len(op.Fields) == 0 {
			op.Fields = []string{"R" + strings.Trim(regSym, "<>V")}
		}
		if strings.HasPrefix(m[2], "<") {
			if b := explain(enc, m[2], explanations); b != nil {
				op.Sizes = tableOf(b)
				op.Sub = append(op.Sub, operand{Sym: m[2], Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)})
			}
		} else {
			op.Text = m[2]
		}
		if strings.HasPrefix(m[3], "<") {
			if b := explain(enc, m[3], explanations); b != nil {
				op.Sub = append(op.Sub, operand{Sym: m[3], Kind: "imm", Fields: fieldsOf(b), Special: "index", Table: indexRows(b)})
			} else {
				return operand{}, "lane index without explanation"
			}
		} else {
			op.Sub = append(op.Sub, operand{Sym: m[3], Kind: "text", Text: m[3]})
		}
		return op, ""
	}
	if m := vecArrRe.FindStringSubmatch(tok); m != nil {
		op := operand{Sym: tok, Kind: "vecarr"}
		regSym := "<V" + m[1] + ">"
		if b := explain(enc, regSym, explanations); b != nil {
			op.Fields = fieldsOf(b)
		}
		if len(op.Fields) == 0 {
			op.Fields = []string{"R" + m[1]}
		}
		if strings.HasPrefix(m[2], "<") {
			b := explain(enc, m[2], explanations)
			if b == nil {
				return operand{}, "arrangement without explanation"
			}
			op.Sizes = tableOf(b)
			op.Sub = []operand{{Sym: m[2], Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)}}
		} else {
			op.Text = strings.ToUpper(m[2])
		}
		return op, ""
	}
	// Option words and other table-valued symbols.
	if strings.HasPrefix(tok, "<") && strings.HasSuffix(tok, ">") {
		if b := explain(enc, tok, explanations); b != nil {
			op := operand{Sym: tok, Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)}
			if len(op.Table) == 0 {
				if m := optionSYRe.FindStringSubmatch(introText(b)); m != nil {
					op.Table = []tableRow{{Bits: []string{m[1]}, Text: "SY"}}
					return op, ""
				}
				if m := rangeRe.FindStringSubmatch(introText(b)); m != nil {
					op.Kind = "imm"
					op.Min, _ = strconv.ParseInt(m[1], 10, 64)
					op.Max, _ = strconv.ParseInt(m[2], 10, 64)
					op.HasRange = true
					op.Scale = 1
					return op, ""
				}
				return operand{}, "symbol without table: " + tok
			}
			return op, ""
		}
		return operand{}, "symbol without explanation: " + tok
	}
	// Fixed words (CSYNC, SY, nXS, WZR/XZR in alias targets).
	return operand{Sym: tok, Kind: "text", Text: tok}, ""
}

func regFieldFor(suffix string) string {
	switch suffix {
	case "t1":
		return "Rt"
	case "t2":
		return "Rt2"
	case "(s+1)":
		return "+Rs"
	case "(t+1)", "t+1":
		return "+Rt"
	}
	return "R" + suffix
}

func list(enc, tok string, explanations []explanation) (operand, string) {
	inner := strings.TrimSpace(strings.TrimSuffix(strings.TrimPrefix(tok, "{"), "}"))
	parts := splitOperands(inner)
	op := operand{Sym: tok, Kind: "list"}
	// Scalable lists: `{ <Zt>.<T> }`, `{ <Zn1>.<T>-<Zn4>.<T> }` (consecutive
	// registers, the first encoded), `{ <ZAt><HV>.S[<Ws>, <offs>] }` (one
	// tile slice), `{ <mask> }` / `{ }` (zero's tile mask), `{ ZT0 }`.
	if inner == "" || inner == "<mask>" || inner == "{<mask>}" {
		b := explain(enc, "<mask>", explanations)
		if b == nil {
			return op, "tile mask without explanation"
		}
		return operand{Sym: tok, Kind: "tilemask", Fields: fieldsOf(b)}, ""
	}
	if len(parts) == 1 {
		p := parts[0]
		if m := zRangeRe.FindStringSubmatch(p); m != nil {
			first, why := classify(enc, m[1], explanations)
			if why != "" {
				return op, why
			}
			count, _ := strconv.Atoi(m[3])
			if first.Kind != "zreg" || count < 2 {
				return op, "multi-vector list shape: " + p
			}
			return operand{Sym: tok, Kind: "zlist", Count: count, Sub: []operand{first}}, ""
		}
		if zRegRe.MatchString(p) || sliceRe.MatchString(p) {
			sub, why := classify(enc, p, explanations)
			if why != "" {
				return op, why
			}
			return operand{Sym: tok, Kind: "zlist", Count: 1, Sub: []operand{sub}}, ""
		}
	}
	if len(parts) > 1 && zRegRe.MatchString(parts[0]) {
		// `{ <Zt1>.B, <Zt2>.B }`: consecutive registers when the head is
		// encoded plainly (the SVE structure accesses), strided when it is
		// constructed from T:'0':Zt (the SME2 strided multi-vector forms).
		first, why := classify(enc, parts[0], explanations)
		if why != "" {
			if strings.Contains(why, "constructed") {
				return op, "strided multi-vector list"
			}
			return op, why
		}
		for _, p := range parts[1:] {
			if !zRegRe.MatchString(p) {
				return op, "multi-vector list shape: " + inner
			}
		}
		return operand{Sym: tok, Kind: "zlist", Count: len(parts), Sub: []operand{first}}, ""
	}
	for _, p := range parts {
		sub, why := classify(enc, strings.TrimSpace(p), explanations)
		if why != "" {
			return op, why
		}
		op.Sub = append(op.Sub, sub)
	}
	return op, ""
}

// memory parses `[<Xn|SP>, #<simm>]!`-style operands (with `@post` marking a
// post-indexed offset appended by buildForm).
func memory(enc, tok string, explanations []explanation) (operand, string) {
	op := operand{Sym: tok, Kind: "mem", Mode: "off"}
	text := tok
	if strings.Contains(text, "@post") {
		op.Mode = "post"
		text = strings.ReplaceAll(text, "@post", "")
		// `[base], #imm` → base and offset.
		close := strings.IndexByte(text, ']')
		text = text[:close] + ", " + strings.TrimSpace(strings.TrimPrefix(text[close+1:], ",")) + "]"
	} else if strings.HasSuffix(text, "]!") {
		op.Mode = "pre"
		text = strings.TrimSuffix(text, "!")
	}
	inner := strings.TrimSuffix(strings.TrimPrefix(text, "["), "]")
	parts := splitOperands(inner)
	if len(parts) == 0 {
		return op, "empty memory operand"
	}
	base, why := classify(enc, parts[0], explanations)
	if why != "" {
		return op, why
	}
	op.Sub = append(op.Sub, base)
	for _, p := range parts[1:] {
		p = strings.TrimSpace(p)
		switch {
		case p == "MUL VL":
			// A vector-length-scaled immediate offset (SVE/SME).
			op.Sub = append(op.Sub, operand{Sym: p, Kind: "text", Text: p})
		case strings.HasPrefix(p, "#") || p == "<imm>":
			imm, why := immediate(enc, "#"+strings.TrimPrefix(p, "#"), explanations)
			if why != "" {
				return op, why
			}
			imm.Sym = "off"
			op.Sub = append(op.Sub, imm)
		case strings.HasPrefix(p, "(<Wm>|<Xm>)") || strings.HasPrefix(p, "<Xm>") || strings.HasPrefix(p, "<Wm>"):
			// Index register, then an optional extend and amount.
			fields := strings.Fields(p)
			idx := operand{Sym: "idx", Kind: "gp", Fields: []string{"Rm"}, ZR: true}
			switch {
			case strings.HasPrefix(fields[0], "(<Wm>|<Xm>)"):
				idx.Width = 0 // chosen by the extend option
			case strings.HasPrefix(fields[0], "<Xm>"):
				idx.Width = 64
			default:
				idx.Width = 32
			}
			op.Sub = append(op.Sub, idx)
			for _, f := range fields[1:] {
				switch {
				case f == "<extend>":
					b := explain(enc, f, explanations)
					if b == nil {
						return op, "extend without explanation"
					}
					op.Sub = append(op.Sub, operand{Sym: f, Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)})
				case f == "LSL":
					op.Sub = append(op.Sub, operand{Sym: f, Kind: "text", Text: "LSL"})
				case f == "<amount>" || f == "#<amount>":
					b := explain(enc, "<amount>", explanations)
					if b == nil {
						return op, "amount without explanation"
					}
					am := operand{Sym: "<amount>", Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)}
					if len(am.Table) == 0 {
						am.Kind = "imm"
						am.Scale = 1
						if m := rangeRe.FindStringSubmatch(introText(b)); m != nil {
							am.Min, _ = strconv.ParseInt(m[1], 10, 64)
							am.Max, _ = strconv.ParseInt(m[2], 10, 64)
							am.HasRange = true
						}
					}
					op.Sub = append(op.Sub, am)
				case strings.HasPrefix(f, "#") && strings.Trim(f[1:], "0123456789") == "":
					// A fixed amount (`LSL #2` of the SVE word accesses).
					op.Sub = append(op.Sub, operand{Sym: "<amount>", Kind: "text", Text: f})
				default:
					return op, "memory index shape: " + p
				}
			}
		case p == "<extend>" || strings.HasPrefix(p, "<extend> ") || strings.HasPrefix(p, "LSL"):
			for _, f := range strings.Fields(p) {
				switch {
				case f == "<extend>":
					b := explain(enc, f, explanations)
					if b == nil {
						return op, "extend without explanation"
					}
					op.Sub = append(op.Sub, operand{Sym: f, Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)})
				case f == "LSL":
					op.Sub = append(op.Sub, operand{Sym: f, Kind: "text", Text: "LSL"})
				case f == "<amount>" || f == "#<amount>":
					b := explain(enc, "<amount>", explanations)
					if b == nil {
						return op, "amount without explanation"
					}
					am := operand{Sym: "<amount>", Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)}
					if len(am.Table) == 0 {
						am.Kind = "imm"
						am.Scale = 1
						if m := rangeRe.FindStringSubmatch(introText(b)); m != nil {
							am.Min, _ = strconv.ParseInt(m[1], 10, 64)
							am.Max, _ = strconv.ParseInt(m[2], 10, 64)
							am.HasRange = true
						}
					}
					op.Sub = append(op.Sub, am)
				case strings.HasPrefix(f, "#") && strings.Trim(f[1:], "0123456789") == "":
					op.Sub = append(op.Sub, operand{Sym: "<amount>", Kind: "text", Text: f})
				default:
					return op, "memory modifier shape: " + p
				}
			}
		default:
			return op, "memory shape: " + p
		}
	}
	return op, ""
}

// ---- rendering --------------------------------------------------------------

// scalable classifies the SVE/SME template symbols. matched is false for a
// token of the base or SIMD&FP vocabulary.
func scalable(enc, tok string, explanations []explanation) (op operand, why string, matched bool) {
	// The element size of a `.<T>` / `.S` suffix: a fixed letter or a table.
	elem := func(op *operand, size string) string {
		if size == "" {
			return ""
		}
		if strings.HasPrefix(size, "<") {
			b := explain(enc, size, explanations)
			if b == nil || len(tableOf(b)) == 0 {
				return "element size without table: " + size
			}
			op.Sub = append(op.Sub, operand{Sym: size, Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)})
			return ""
		}
		op.Text = size
		return ""
	}
	// The register field, with the "times N" / "plus N" encodings of list
	// heads and counter predicates.
	regFields := func(op *operand, sym string) string {
		b := explain(enc, sym, explanations)
		if b == nil {
			return "register without explanation: " + sym
		}
		op.Fields = fieldsOf(b)
		text := introText(b)
		if strings.Contains(text, "'") && !strings.Contains(text, "encoded in") {
			return "register with a constructed encoding: " + sym
		}
		op.Scale = 1
		if m := encodedTimesRe.FindStringSubmatch(text); m != nil {
			op.Scale, _ = strconv.ParseInt(m[1], 10, 64)
		}
		if m := plusRe.FindStringSubmatch(text); m != nil {
			op.Offset, _ = strconv.ParseInt(m[1], 10, 64)
		}
		return ""
	}
	switch {
	case zLaneRe.MatchString(tok):
		m := zLaneRe.FindStringSubmatch(tok)
		op = operand{Sym: tok, Kind: "zlane"}
		if why := regFields(&op, "<Z"+m[1]+">"); why != "" {
			return op, why, true
		}
		if why := elem(&op, m[2]); why != "" {
			return op, why, true
		}
		if strings.HasPrefix(m[3], "<") {
			idx, why := immediate(enc, "#"+m[3], explanations)
			if why != "" {
				return op, why, true
			}
			idx.Sym = "idx"
			op.Sub = append(op.Sub, idx)
		} else {
			// A literal index (`<Zn>.<T>[0]` of the mov alias): encoded like
			// the instruction's own index operand when it has one.
			idx := operand{Sym: "idx", Kind: "text", Text: m[3]}
			for _, sym := range []string{"#<imm>", "#<index>"} {
				if op, why := immediate(enc, sym, explanations); why == "" && len(op.Fields) > 0 {
					idx = op
					idx.Sym, idx.Text = "idx", m[3]
					break
				}
			}
			op.Sub = append(op.Sub, idx)
		}
		return op, "", true
	case zRegRe.MatchString(tok):
		m := zRegRe.FindStringSubmatch(tok)
		op = operand{Sym: tok, Kind: "zreg"}
		if why := regFields(&op, "<Z"+m[1]+">"); why != "" {
			return op, why, true
		}
		return op, elem(&op, m[2]), true
	case pRegRe.MatchString(tok):
		m := pRegRe.FindStringSubmatch(tok)
		op = operand{Sym: tok, Kind: "preg"}
		if why := regFields(&op, "<P"+m[1]+">"); why != "" {
			return op, why, true
		}
		if why := elem(&op, m[2]); why != "" {
			return op, why, true
		}
		switch m[3] {
		case "M", "Z":
			op.Qual = m[3]
		case "<ZM>":
			b := explain(enc, "<ZM>", explanations)
			if b == nil {
				return op, "predicate qualifier without table", true
			}
			op.Sub = append(op.Sub, operand{Sym: "<ZM>", Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)})
		}
		return op, "", true
	case pnRegRe.MatchString(tok):
		m := pnRegRe.FindStringSubmatch(tok)
		op = operand{Sym: tok, Kind: "pnreg"}
		if why := regFields(&op, "<PN"+m[1]+">"); why != "" {
			return op, why, true
		}
		if why := elem(&op, m[2]); why != "" {
			return op, why, true
		}
		if m[3] != "" {
			op.Qual = "Z"
		}
		if m[4] != "" {
			idx, why := immediate(enc, "#"+m[4], explanations)
			if why != "" {
				return op, why, true
			}
			idx.Sym = "idx"
			op.Sub = append(op.Sub, idx)
		}
		return op, "", true
	case tileRe.MatchString(tok):
		m := tileRe.FindStringSubmatch(tok)
		op = operand{Sym: tok, Kind: "tile"}
		if strings.HasPrefix(m[1], "<") {
			if why := regFields(&op, m[1]); why != "" {
				return op, why, true
			}
		} else {
			n, _ := strconv.Atoi(strings.TrimPrefix(m[1], "ZA"))
			op.Offset = int64(n) // a fixed tile number, no field
			op.Special = "fixed"
		}
		return op, elem(&op, m[2]), true
	case sliceRe.MatchString(tok):
		m := sliceRe.FindStringSubmatch(tok)
		op = operand{Sym: tok, Kind: "slice", Count: 1}
		tile := operand{Sym: "tile", Kind: "tile"}
		switch {
		case strings.HasPrefix(m[1], "<"):
			if why := regFields(&tile, m[1]); why != "" {
				return op, why, true
			}
		case m[1] == "ZA":
			tile.Special = "array" // the whole array, addressed by vector
		default:
			n, _ := strconv.Atoi(strings.TrimPrefix(m[1], "ZA"))
			tile.Offset = int64(n)
			tile.Special = "fixed"
		}
		op.Sub = append(op.Sub, tile)
		if m[2] != "" {
			b := explain(enc, "<HV>", explanations)
			if b == nil {
				return op, "slice direction without table", true
			}
			op.Sub = append(op.Sub, operand{Sym: "hv", Kind: "table", Fields: fieldsOf(b), Table: tableOf(b)})
		}
		if m[3] != "" {
			e := operand{Sym: "elem"}
			if why := elem(&e, m[3]); why != "" {
				return op, why, true
			}
			if e.Text != "" {
				op.Text = e.Text
			} else {
				e.Sub[0].Sym = "elem"
				op.Sub = append(op.Sub, e.Sub[0])
			}
		}
		idx := operand{Sym: "idx", Kind: "gp", Width: 32}
		if why := regFields(&idx, m[4]); why != "" {
			return op, why, true
		}
		op.Sub = append(op.Sub, idx)
		offs, why := immediate(enc, "#"+m[5], explanations)
		if why != "" {
			return op, why, true
		}
		offs.Sym = "offs"
		op.Sub = append(op.Sub, offs)
		if m[6] != "" {
			count, _ := strconv.Atoi(strings.Trim(m[6], "<offs>"))
			if count < 2 {
				return op, "slice range shape: " + tok, true
			}
			op.Count = count
		}
		if m[7] != "" {
			op.Sub = append(op.Sub, operand{Sym: "group", Kind: "text", Text: m[7]})
		}
		return op, "", true
	case tok == "ZT0":
		return operand{Sym: tok, Kind: "text", Text: tok}, "", true
	case strings.HasPrefix(tok, "ZT0["):
		return op, "ZT0 element index", true
	case pSliceRe.MatchString(tok):
		return op, "predicate element index (psel)", true
	case tok == "<mask>":
		b := explain(enc, tok, explanations)
		if b == nil {
			return op, "tile mask without explanation", true
		}
		return operand{Sym: tok, Kind: "tilemask", Fields: fieldsOf(b)}, "", true
	}
	return op, "", false
}

func render(release string, defs []encodingDef) string {
	var b strings.Builder
	fmt.Fprintf(&b, "// Code generated by asm/internal/isagen from Arm's A64 ISA XML (%s); DO NOT EDIT.\n\n", release)
	b.WriteString("package asm\n\n")
	fmt.Fprintf(&b, "const isaRelease = %q\n\n", release)
	b.WriteString("var isaEncodings = []isaEncoding{\n")
	for _, d := range defs {
		fmt.Fprintf(&b, "\t{Name: %q, Mnemonic: %q, Mask: 0x%08x, Value: 0x%08x, Fields: []isaField{", d.Name, d.Mnemonic, d.Mask, d.Value)
		for i, f := range d.Fields {
			if i > 0 {
				b.WriteString(", ")
			}
			fmt.Fprintf(&b, "{%q, %d, %d}", f.Name, f.Hi, f.Width)
		}
		b.WriteString("}, Forms: []isaForm{")
		for i, f := range d.Forms {
			if i > 0 {
				b.WriteString(", ")
			}
			b.WriteString("{Operands: ")
			renderOperands(&b, f.Operands)
			if len(f.Defaults) > 0 {
				b.WriteString(", Defaults: []isaDefault{")
				for j, df := range f.Defaults {
					if j > 0 {
						b.WriteString(", ")
					}
					fmt.Fprintf(&b, "{%q, %d}", df.Field, df.Value)
				}
				b.WriteString("}")
			}
			b.WriteString("}")
		}
		b.WriteString("}")
		if d.Alias != "" {
			fmt.Fprintf(&b, ", Alias: %q, AliasCond: %q", d.Alias, d.AliasCond)
		}
		if d.Mode != "" {
			fmt.Fprintf(&b, ", Mode: %q", d.Mode)
		}
		if d.Flags {
			b.WriteString(", Flags: true")
		}
		b.WriteString("},\n")
	}
	b.WriteString("}\n")
	return b.String()
}

func renderOperands(b *strings.Builder, ops []operand) {
	b.WriteString("[]isaOperand{")
	for i, op := range ops {
		if i > 0 {
			b.WriteString(", ")
		}
		renderOperand(b, op)
	}
	b.WriteString("}")
}

func renderOperand(b *strings.Builder, op operand) {
	fmt.Fprintf(b, "{Sym: %q, Kind: %q", op.Sym, op.Kind)
	if len(op.Fields) > 0 {
		fmt.Fprintf(b, ", Fields: %#v", op.Fields)
	}
	if op.Width != 0 {
		fmt.Fprintf(b, ", Width: %d", op.Width)
	}
	if op.SP {
		b.WriteString(", SP: true")
	}
	if op.ZR {
		b.WriteString(", ZR: true")
	}
	if op.HasRange {
		fmt.Fprintf(b, ", Min: %d, Max: %d, HasRange: true", op.Min, op.Max)
	}
	if op.Scale > 1 {
		fmt.Fprintf(b, ", Scale: %d", op.Scale)
	}
	if op.Offset != 0 {
		fmt.Fprintf(b, ", Offset: %d", op.Offset)
	}
	if op.Mode != "" && op.Kind == "mem" {
		fmt.Fprintf(b, ", Mode: %q", op.Mode)
	}
	if op.Text != "" {
		fmt.Fprintf(b, ", Text: %q", op.Text)
	}
	if op.Special != "" {
		fmt.Fprintf(b, ", Special: %q", op.Special)
	}
	if op.Count > 0 {
		fmt.Fprintf(b, ", Count: %d", op.Count)
	}
	if op.Qual != "" {
		fmt.Fprintf(b, ", Qual: %q", op.Qual)
	}
	if len(op.Table) > 0 {
		b.WriteString(", Table: []isaTableRow{")
		for i, r := range op.Table {
			if i > 0 {
				b.WriteString(", ")
			}
			fmt.Fprintf(b, "{%#v, %q}", r.Bits, r.Text)
		}
		b.WriteString("}")
	}
	if len(op.Sizes) > 0 && op.Kind == "fp" {
		b.WriteString(", Sizes: []isaTableRow{")
		for i, r := range op.Sizes {
			if i > 0 {
				b.WriteString(", ")
			}
			fmt.Fprintf(b, "{%#v, %q}", r.Bits, r.Text)
		}
		b.WriteString("}")
	}
	if len(op.Sub) > 0 {
		b.WriteString(", Sub: ")
		renderOperands(b, op.Sub)
	}
	b.WriteString("}")
}
