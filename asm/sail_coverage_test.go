package asm

import (
	"bufio"
	"bytes"
	"fmt"
	"math/rand"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"sort"
	"strconv"
	"strings"
	"testing"
)

// Completeness audit of the instruction table against Arm's machine-readable
// decoder (docs/spec/94-assembler.md §8, grounding stage 1).
//
// The Sail model of Armv8.5-A that Arm and the REMS group generated from
// Arm's ASL/XML release carries the A64 decode tree as one clause per
// encoding class: a 32-bit pattern of fixed bits and fields, and the decode
// function the class dispatches to. This test walks every clause, draws
// encodings from its pattern, and asks the host LLVM disassembler which
// mnemonic each defined encoding spells. Every mnemonic Arm's decoder
// reaches must be in our table, or on the by-design exclusion list below —
// so a class we silently do not cover fails the test by name. The
// disassembler is the encoding-to-text oracle only; the classes come from
// Arm's tree, which is what makes this an audit of the specification's
// surface rather than of a sample we chose ourselves.
//
// The test skips when the external model or the disassembler is absent.

const sailArmModel = "/Users/sam/oak/external/sail-arm/arm-v8.5-a/model/aarch_decode.sail"

var llvmMCCandidates = []string{"/opt/homebrew/opt/llvm/bin/llvm-mc", "/usr/local/opt/llvm/bin/llvm-mc"}

// sailDecodeClass is one `function clause decode64` clause.
type sailDecodeClass struct {
	line  int
	mask  uint32 // fixed bits
	value uint32 // their values
	fn    string // decode function dispatched to
}

var (
	sailClauseHead = regexp.MustCompile(`^function clause decode64 \(\((.*) as op_code\) if SEE < (\d+)\) = \{`)
	sailFixedBits  = regexp.MustCompile(`^0b([01]+)$`)
	sailFieldBits  = regexp.MustCompile(`^[A-Za-z_][A-Za-z0-9_']* : bits\((\d+)\)$`)
	sailCall       = regexp.MustCompile(`^\s*([a-z0-9_]+)\(`)
)

// parseSailDecodeClasses reads the decode64 clauses of aarch_decode.sail.
func parseSailDecodeClasses(path string) ([]sailDecodeClass, error) {
	data, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	var classes []sailDecodeClass
	lines := strings.Split(string(data), "\n")
	for i := 0; i < len(lines); i++ {
		m := sailClauseHead.FindStringSubmatch(lines[i])
		if m == nil {
			continue
		}
		class := sailDecodeClass{line: i + 1}
		width := 0
		for _, item := range strings.Split(m[1], " @ ") {
			item = strings.TrimSpace(item)
			if fixed := sailFixedBits.FindStringSubmatch(item); fixed != nil {
				for _, bit := range fixed[1] {
					class.mask = class.mask<<1 | 1
					class.value <<= 1
					if bit == '1' {
						class.value |= 1
					}
					width++
				}
				continue
			}
			if field := sailFieldBits.FindStringSubmatch(item); field != nil {
				n, _ := strconv.Atoi(field[1])
				class.mask <<= uint(n)
				class.value <<= uint(n)
				width += n
				continue
			}
			return nil, fmt.Errorf("%s:%d: unrecognized pattern item %q", path, i+1, item)
		}
		if width != 32 {
			return nil, fmt.Errorf("%s:%d: pattern is %d bits wide", path, i+1, width)
		}
		// The dispatched decode function is the last call before the closing brace.
		for j := i + 1; j < len(lines) && lines[j] != "}"; j++ {
			if call := sailCall.FindStringSubmatch(lines[j]); call != nil && strings.HasSuffix(call[1], "_decode") {
				class.fn = strings.TrimSuffix(call[1], "_decode")
				// The generator doubled some class names (`X_X_`); keep one.
				if half := strings.TrimSuffix(class.fn, "_"); len(half)%2 == 1 && half[:len(half)/2] == half[len(half)/2+1:] {
					class.fn = half[:len(half)/2]
				}
			}
		}
		if class.fn == "" {
			return nil, fmt.Errorf("%s:%d: clause without a decode function", path, i+1)
		}
		classes = append(classes, class)
	}
	return classes, nil
}

// sampleEncodings draws words matching the class: the free bits all clear,
// all set, and pseudo-random fills from a fixed seed.
func sampleEncodings(class sailDecodeClass, rng *rand.Rand, n int) []uint32 {
	free := ^class.mask
	words := []uint32{class.value, class.value | free}
	for i := 0; i < n; i++ {
		words = append(words, class.value|(rng.Uint32()&free))
	}
	return words
}

// The marker word separating samples in the disassembler's input:
// `movz x3, #0xbeef`, which no sampled class is likely to spell.
const sailMarkerWord uint32 = 0xd297dde3

// disassembleAll returns, for each word, the mnemonic the disassembler
// prints, or "" when the encoding is undefined. Samples are interleaved
// with marker words so undefined encodings (which print nothing) keep the
// alignment.
func disassembleAll(t *testing.T, llvmMC string, words []uint32) []string {
	var input bytes.Buffer
	for _, w := range words {
		fmt.Fprintf(&input, "0x%02x 0x%02x 0x%02x 0x%02x\n", byte(w), byte(w>>8), byte(w>>16), byte(w>>24))
		w = sailMarkerWord
		fmt.Fprintf(&input, "0x%02x 0x%02x 0x%02x 0x%02x\n", byte(w), byte(w>>8), byte(w>>16), byte(w>>24))
	}
	cmd := exec.Command(llvmMC, "--disassemble", "--triple=arm64", "-mcpu=apple-m4")
	cmd.Stdin = &input
	var stdout, stderr bytes.Buffer
	cmd.Stdout, cmd.Stderr = &stdout, &stderr
	if err := cmd.Run(); err != nil {
		t.Fatalf("llvm-mc: %v\n%s", err, stderr.String())
	}
	out := make([]string, len(words))
	index := 0
	pending := ""
	scanner := bufio.NewScanner(&stdout)
	scanner.Buffer(make([]byte, 1<<20), 1<<26)
	for scanner.Scan() {
		line := strings.TrimSpace(scanner.Text())
		if line == "" {
			continue
		}
		if strings.HasPrefix(line, "mov") && strings.Contains(line, "x3, #48879") {
			if index >= len(words) {
				t.Fatalf("llvm-mc: more markers than samples")
			}
			out[index] = pending
			pending = ""
			index++
			continue
		}
		fields := strings.Fields(line)
		pending = fields[0]
	}
	if index != len(words) {
		t.Fatalf("llvm-mc: %d markers for %d samples", index, len(words))
	}
	return out
}

// sailExcluded lists mnemonics Arm's decoder reaches that the table leaves
// out by design, each with the reason. A new entry needs a spec paragraph.
var sailExcluded = map[string]string{
	"dcps1": "debug-state entry: a debugger's instruction, never a unit's",
	"dcps2": "debug-state entry",
	"dcps3": "debug-state entry",
	"drps":  "debug-state return",
	"hlt":   "halting breakpoint: enters debug state; `brk` is the trap",
	"sys":   "raw system operation: the table spells its aliases (dc, ic, tlbi, at)",
	"sysl":  "raw system operation with a result: no aliases the unit needs",
}

func TestSailDecodeCoverage(t *testing.T) {
	if _, err := os.Stat(sailArmModel); err != nil {
		t.Skipf("sail-arm model not present: %v", err)
	}
	llvmMC := ""
	for _, candidate := range llvmMCCandidates {
		if _, err := os.Stat(candidate); err == nil {
			llvmMC = candidate
			break
		}
	}
	if llvmMC == "" {
		t.Skip("llvm-mc not present")
	}
	classes, err := parseSailDecodeClasses(sailArmModel)
	if err != nil {
		t.Fatal(err)
	}
	if len(classes) < 900 {
		t.Fatalf("parsed %d decode64 clauses; expected the full A64 tree", len(classes))
	}

	rng := rand.New(rand.NewSource(94))
	var words []uint32
	var owner []int
	for i, class := range classes {
		for _, w := range sampleEncodings(class, rng, 62) {
			words = append(words, w)
			owner = append(owner, i)
		}
	}
	mnemonics := disassembleAll(t, llvmMC, words)

	byMnemonic := map[string]map[string]bool{}
	covered := make([]bool, len(classes))
	for i, mnemonic := range mnemonics {
		if mnemonic == "" {
			continue
		}
		covered[owner[i]] = true
		if byMnemonic[mnemonic] == nil {
			byMnemonic[mnemonic] = map[string]bool{}
		}
		byMnemonic[mnemonic][classes[owner[i]].fn] = true
	}

	inTable := func(mnemonic string) bool {
		if _, ok := instructionTable[mnemonic]; ok {
			return true
		}
		if strings.HasPrefix(mnemonic, "b.") {
			_, ok := instructionTable["b."]
			return ok
		}
		return false
	}

	var missing, present []string
	for mnemonic := range byMnemonic {
		if inTable(mnemonic) {
			present = append(present, mnemonic)
			continue
		}
		if _, excluded := sailExcluded[mnemonic]; excluded {
			continue
		}
		missing = append(missing, mnemonic)
	}
	sort.Strings(missing)
	sort.Strings(present)

	uncovered := 0
	for i := range classes {
		if !covered[i] {
			uncovered++
		}
	}
	t.Logf("decode classes: %d (%d yielded no defined encoding in %d samples); mnemonics reached: %d; in table: %d; excluded by design: %d",
		len(classes), uncovered, 64, len(byMnemonic), len(present), len(byMnemonic)-len(present)-len(missing))

	if len(missing) > 0 {
		var report strings.Builder
		for _, mnemonic := range missing {
			var fns []string
			for fn := range byMnemonic[mnemonic] {
				fns = append(fns, fn)
			}
			sort.Strings(fns)
			fmt.Fprintf(&report, "  %-12s %s\n", mnemonic, strings.Join(fns, ", "))
		}
		t.Errorf("%d mnemonics reached by Arm's decoder are missing from the table:\n%s", len(missing), report.String())
	}

	// Write the audit report beside the test data for the record.
	if dir := os.Getenv("OAK_SAIL_REPORT_DIR"); dir != "" {
		var report strings.Builder
		for _, mnemonic := range present {
			fmt.Fprintf(&report, "%s\n", mnemonic)
		}
		if err := os.WriteFile(filepath.Join(dir, "sail_decode_coverage.txt"), []byte(report.String()), 0o644); err != nil {
			t.Fatal(err)
		}
	}
}
