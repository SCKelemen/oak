// Command sysreggen derives the AArch64 system register table of the Oak
// assembler from Arm's machine-readable SysReg XML (docs/spec/94-assembler.md
// §9).
//
//	go run ./asm/internal/sysreggen -xml ../external/sysreg/SysReg_xml_A_profile-2026-06 -o asm/sysregs_gen.go
//
// For every AArch64 register reached by MRS or MSR it writes the name (register
// arrays expanded, `DBGBVR<m>_EL1` → dbgbvr0_el1 … dbgbvr15_el1), the
// op0:op1:CRn:CRm:op2 encoding, and whether the register is readable and
// writable. Only these facts are written; none of Arm's prose is reproduced.
package main

import (
	"encoding/xml"
	"flag"
	"fmt"
	"go/format"
	"html"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
)

type registerPage struct {
	Registers []struct {
		ExecutionState string `xml:"execution_state,attr"`
		ShortName      string `xml:"reg_short_name"`
		Array          *struct {
			Start int `xml:"reg_array_start"`
			End   int `xml:"reg_array_end"`
		} `xml:"reg_array"`
		Mechanisms []struct {
			Accessor  string `xml:"accessor,attr"`
			Encodings []struct {
				Instruction string `xml:"access_instruction"`
				Enc         []struct {
					N string `xml:"n,attr"`
					V string `xml:"v,attr"`
				} `xml:"enc"`
			} `xml:"encoding"`
		} `xml:"access_mechanisms>access_mechanism"`
	} `xml:"registers>register"`
}

type sysReg struct {
	name                    string
	op0, op1, crn, crm, op2 uint32
	read, write             bool
}

var fieldWidths = map[string]int{"op0": 2, "op1": 3, "CRn": 4, "CRm": 4, "op2": 3}

func main() {
	xmlDir := flag.String("xml", "", "directory of the SysReg XML release")
	out := flag.String("o", "asm/sysregs_gen.go", "output Go file")
	flag.Parse()
	if *xmlDir == "" {
		fmt.Fprintln(os.Stderr, "sysreggen: -xml is required")
		os.Exit(2)
	}
	files, err := filepath.Glob(filepath.Join(*xmlDir, "AArch64-*.xml"))
	if err != nil || len(files) == 0 {
		fmt.Fprintln(os.Stderr, "sysreggen: no AArch64 register files")
		os.Exit(1)
	}
	regs := map[string]*sysReg{}
	skipped := map[string]int{}
	for _, file := range files {
		data, err := os.ReadFile(file)
		if err != nil {
			fail(err)
		}
		var page registerPage
		if err := xml.Unmarshal(data, &page); err != nil {
			fail(fmt.Errorf("%s: %w", file, err))
		}
		for _, reg := range page.Registers {
			if reg.ExecutionState != "AArch64" {
				continue
			}
			for _, mech := range reg.Mechanisms {
				op := strings.Fields(mech.Accessor)
				if len(op) == 0 || op[0] != "MRS" && op[0] != "MSR" && op[0] != "MSRregister" {
					continue
				}
				for _, enc := range mech.Encodings {
					instr := clean(enc.Instruction)
					op[0] = strings.Fields(instr)[0] // MRS or MSR, from the instruction itself
					// `MSR <pstatefield>, #imm`-style accesses and 128-bit
					// moves are not register moves the encoder names.
					if strings.Contains(instr, "#") || strings.HasPrefix(instr, "MRRS") || strings.HasPrefix(instr, "MSRR") {
						skipped["immediate or 128-bit access"]++
						continue
					}
					name := registerName(instr)
					if name == "" {
						skipped["unrecognized access instruction"]++
						continue
					}
					indices := []int{-1}
					if strings.Contains(name, "<") {
						if reg.Array == nil {
							skipped["array register without a range"]++
							continue
						}
						indices = nil
						for i := reg.Array.Start; i <= reg.Array.End; i++ {
							indices = append(indices, i)
						}
					}
					for _, index := range indices {
						values := map[string]uint32{}
						ok := true
						highest := -1 // the highest index bit the encoding consults
						for _, e := range enc.Enc {
							v, hi, fits := evalEncoding(e.V, index, fieldWidths[e.N])
							if !fits {
								ok = false
								break
							}
							if hi > highest {
								highest = hi
							}
							values[e.N] = v
						}
						if ok && index >= 0 && index>>uint(highest+1) != 0 {
							continue // an index beyond the bits the encoding carries is another register's
						}
						if !ok || len(values) != 5 {
							if index < 0 || index == reg.Array.Start {
								var parts []string
								for _, e := range enc.Enc {
									parts = append(parts, e.N+"="+e.V)
								}
								skipped["encoding expression "+strings.Join(parts, " ")]++
							}
							continue
						}
						spelled := strings.ToLower(name)
						if index >= 0 {
							spelled = strings.ToLower(regexp.MustCompile(`<[a-z]>`).ReplaceAllString(name, strconv.Itoa(index)))
						}
						r := regs[spelled]
						if r == nil {
							r = &sysReg{name: spelled, op0: values["op0"], op1: values["op1"], crn: values["CRn"], crm: values["CRm"], op2: values["op2"]}
							regs[spelled] = r
						} else if r.op0 != values["op0"] || r.op1 != values["op1"] || r.crn != values["CRn"] || r.crm != values["CRm"] || r.op2 != values["op2"] {
							skipped["conflicting encodings for one name"]++
							continue
						}
						if op[0] == "MRS" {
							r.read = true
						} else {
							r.write = true
						}
					}
				}
			}
		}
	}
	var names []string
	for name := range regs {
		names = append(names, name)
	}
	sort.Strings(names)
	var b strings.Builder
	fmt.Fprintf(&b, "// Code generated by asm/internal/sysreggen from Arm's SysReg XML (%s); DO NOT EDIT.\n\n", filepath.Base(*xmlDir))
	b.WriteString("package asm\n\n")
	fmt.Fprintf(&b, "const sysRegRelease = %q\n\n", filepath.Base(*xmlDir))
	b.WriteString("// systemRegisterEncodings: op0, op1, CRn, CRm, op2 and the access\n// directions of every AArch64 register MRS or MSR can name.\n")
	b.WriteString("var systemRegisterEncodings = map[string]sysRegEncoding{\n")
	for _, name := range names {
		r := regs[name]
		fmt.Fprintf(&b, "\t%q: {%d, %d, %d, %d, %d, %t, %t},\n", name, r.op0, r.op1, r.crn, r.crm, r.op2, r.read, r.write)
	}
	b.WriteString("}\n")
	formatted, err := format.Source([]byte(b.String()))
	if err != nil {
		fail(err)
	}
	if err := os.WriteFile(*out, formatted, 0o644); err != nil {
		fail(err)
	}
	var reasons []string
	for why, n := range skipped {
		reasons = append(reasons, fmt.Sprintf("%d %s", n, why))
	}
	sort.Strings(reasons)
	fmt.Fprintf(os.Stderr, "sysreggen: %d registers written to %s; skipped: %s\n", len(names), *out, strings.Join(reasons, "; "))
}

func fail(err error) {
	fmt.Fprintln(os.Stderr, "sysreggen:", err)
	os.Exit(1)
}

var tags = regexp.MustCompile(`<[^>]*>`)

func clean(s string) string {
	return strings.Join(strings.Fields(html.UnescapeString(s)), " ")
}

// registerName extracts the register from `MRS <Xt>, NAME` or `MSR NAME, <Xt>`.
func registerName(instr string) string {
	fields := strings.Fields(strings.ReplaceAll(instr, ",", " "))
	if len(fields) < 3 {
		return ""
	}
	switch fields[0] {
	case "MRS":
		return fields[2]
	case "MSR":
		return fields[1]
	}
	return ""
}

// evalEncoding evaluates an `enc` value: `0b011`, `m[3:0]`, `0b1:m[2:0]`,
// concatenated most significant first; index substitutes the array
// variable. highest is the highest index bit consulted (-1 for none); fits
// reports whether the result has exactly width bits.
func evalEncoding(v string, index int, width int) (value uint32, highest int, fits bool) {
	highest = -1
	bitsDone := 0
	for _, part := range splitTopLevel(v) {
		part = strings.TrimSpace(part)
		switch {
		case strings.HasPrefix(part, "0b"):
			n, err := strconv.ParseUint(part[2:], 2, 32)
			if err != nil {
				return 0, -1, false
			}
			value = value<<uint(len(part)-2) | uint32(n)
			bitsDone += len(part) - 2
		case len(part) > 1 && part[1] == '[':
			if index < 0 {
				return 0, -1, false
			}
			spec := strings.TrimSuffix(part[2:], "]")
			hi, lo := 0, 0
			if i := strings.IndexByte(spec, ':'); i >= 0 {
				hi, _ = strconv.Atoi(spec[:i])
				lo, _ = strconv.Atoi(spec[i+1:])
			} else {
				hi, _ = strconv.Atoi(spec)
				lo = hi
			}
			if hi < lo {
				return 0, -1, false
			}
			n := hi - lo + 1
			value = value<<uint(n) | (uint32(index)>>uint(lo))&(1<<uint(n)-1)
			bitsDone += n
			if hi > highest {
				highest = hi
			}
		default:
			return 0, -1, false
		}
	}
	return value, highest, bitsDone == width
}

// splitTopLevel splits at colons outside brackets (`0b1:m[2:0]`).
func splitTopLevel(s string) []string {
	var out []string
	depth, last := 0, 0
	for i, r := range s {
		switch r {
		case '[':
			depth++
		case ']':
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
