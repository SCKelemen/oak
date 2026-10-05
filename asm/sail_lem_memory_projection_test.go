package asm

import (
	"fmt"
	"os"
	"os/exec"
	"path/filepath"
	"strconv"
	"strings"
	"testing"
)

// This is a deliberately small, test-only interchange format, not a general
// raw Lem importer. Never insert unchecked text into a generated Lean command.
func lemBitsLiteral(text string, width int) (string, error) {
	if len(text) != width {
		return "", fmt.Errorf("bit-vector width: got %d, want %d", len(text), width)
	}
	bits := make([]string, width)
	for i, bit := range text {
		if bit < '0' || bit > '2' {
			return "", fmt.Errorf("unknown bit encoding")
		}
		bits[i] = strconv.Itoa(int(bit - '0'))
	}
	return "[" + strings.Join(bits, ", ") + "]", nil
}

func lemNatural(text string, bits int) (uint64, error) {
	n, err := strconv.ParseUint(text, 10, bits)
	if err != nil || strconv.FormatUint(n, 10) != text {
		return 0, fmt.Errorf("invalid canonical unsigned integer")
	}
	return n, nil
}

func lemEventView(line string) (string, error) {
	fields := strings.Fields(line)
	if len(fields) == 3 && fields[0] == "READ" && fields[1] == "__defaultRAM" {
		selector, err := lemBitsLiteral(fields[2], 56)
		if err != nil {
			return "", err
		}
		return `.readReg "__defaultRAM" ` + selector, nil
	}
	if (len(fields) != 4 || fields[0] != "EA") && (len(fields) != 6 || fields[0] != "WRITE") {
		return "", fmt.Errorf("unknown event or field count")
	}
	if fields[1] != "plain" {
		return "", fmt.Errorf("only plain requests are supported")
	}
	address, err := lemNatural(fields[2], 56)
	if err != nil {
		return "", err
	}
	size, err := lemNatural(fields[3], 8)
	if err != nil || size == 0 || size > 8 {
		return "", fmt.Errorf("unsupported request size")
	}
	if fields[0] == "EA" {
		return fmt.Sprintf(".writeEA %d %d", address, size), nil
	}
	bytes := strings.Split(fields[4], ",")
	if len(bytes) != int(size) {
		return "", fmt.Errorf("payload byte count differs from request size")
	}
	for i, bits := range bytes {
		bytes[i], err = lemBitsLiteral(bits, 8)
		if err != nil {
			return "", err
		}
	}
	ack := fields[5]
	if ack != "true" && ack != "false" {
		return "", fmt.Errorf("invalid acknowledgement")
	}
	return fmt.Sprintf(".writeMem %d %d [%s] %s", address, size, strings.Join(bytes, ", "), ack), nil
}

func parseLemMemoryExport(data []byte) ([][]string, error) {
	if len(data) > 16*1024 || !strings.HasSuffix(string(data), "\n") {
		return nil, fmt.Errorf("oversized or unterminated export")
	}
	lines := strings.Split(strings.TrimSuffix(string(data), "\n"), "\n")
	if len(lines) == 0 || lines[0] != "OAK_LEM_MEMORY_TRACE_V1" {
		return nil, fmt.Errorf("unknown export schema")
	}
	index := 1
	var cases [][]string
	for _, name := range []string{"mixed", "identical"} {
		if index >= len(lines) || lines[index] != "CASE "+name {
			return nil, fmt.Errorf("missing or reordered case %s", name)
		}
		index++
		var views []string
		for index < len(lines) && lines[index] != "DONE" {
			if len(views) == 16 {
				return nil, fmt.Errorf("too many requests")
			}
			view, err := lemEventView(lines[index])
			if err != nil {
				return nil, fmt.Errorf("line %d: %w", index+1, err)
			}
			views = append(views, view)
			index++
		}
		if len(views) == 0 || index >= len(lines) {
			return nil, fmt.Errorf("empty or incomplete case")
		}
		index++ // DONE is evidence from the executable adapter, not a proof.
		cases = append(cases, views)
	}
	if index != len(lines)-1 || lines[index] != "END" {
		return nil, fmt.Errorf("missing end marker or trailing data")
	}
	return cases, nil
}

// The expected calls and responses are independently fixed test inputs, not
// recovered from the observed events. Undefined bits remain 2, never zero.
func lemProjectionCheck(views [][]string) string {
	literal := func(text string, width int) string {
		value, err := lemBitsLiteral(text, width)
		if err != nil {
			panic(err) // Only fixed internal test constants enter this helper.
		}
		return value
	}
	zeroSelector := literal(strings.Repeat("0", 56), 56)
	nextSelector := literal(fmt.Sprintf("%056b", 0x1234), 56)
	undefined := literal(strings.Repeat("2", 56), 56)
	var dataBytes, zeroBytes []string
	for _, b := range []byte{0xef, 0xcd, 0xab, 0x89, 0x67, 0x45, 0x23, 0x01} {
		dataBytes = append(dataBytes, literal(fmt.Sprintf("%08b", b), 8))
		zeroBytes = append(zeroBytes, literal("00000000", 8))
	}
	data := "[" + strings.Join(dataBytes, ", ") + "]"
	zero := "[" + strings.Join(zeroBytes, ", ") + "]"
	blocks := []string{
		fmt.Sprintf("[⟨%s, 4096, 8, %s, true⟩, ⟨%s, 4096, 8, %s, false⟩]", zeroSelector, zero, nextSelector, data),
		fmt.Sprintf("[⟨%s, 4096, 8, %s, true⟩, ⟨%s, 4096, 8, %s, true⟩]", undefined, data, undefined, data),
	}
	calls := []string{
		fmt.Sprintf("[⟨4096, 8, %s⟩, ⟨4096, 8, %s⟩]", zero, data),
		fmt.Sprintf("[⟨4096, 8, %s⟩, ⟨4096, 8, %s⟩]", data, data),
	}
	var source strings.Builder
	source.WriteString("import MemoryEventProjection\nopen Oak.MemoryEventProjection\n")
	for i := range views {
		fmt.Fprintf(&source, "def observed%d : List (View (List Nat) (List (List Nat))) := [%s]\n", i, strings.Join(views[i], ",\n"))
		fmt.Fprintf(&source, "def expected%d : List (Block (List Nat) (List (List Nat))) := %s\n", i, blocks[i])
		fmt.Fprintf(&source, "def calls%d : List (Call (List (List Nat))) := %s\n", i, calls[i])
		fmt.Fprintf(&source, "theorem observed%d_exact : projectCalls calls%d 0 observed%d = some (positioned 0 expected%d) := by decide\n", i, i, i, i)
		fmt.Fprintf(&source, "/-- info: 'observed%d_exact' depends on axioms: [propext] -/\n#guard_msgs in\n#print axioms observed%d_exact\n", i, i)
	}
	return source.String()
}

func TestSailLemMemoryExportParser(t *testing.T) {
	read := "READ __defaultRAM " + strings.Repeat("0", 56) + "\n"
	ea := "EA plain 4096 8\n"
	write := "WRITE plain 4096 8 " + strings.TrimSuffix(strings.Repeat("00000000,", 8), ",") + " true\n"
	good := "OAK_LEM_MEMORY_TRACE_V1\nCASE mixed\n" + read + ea + write + "DONE\nCASE identical\n" + read + ea + write + "DONE\nEND\n"
	views, err := parseLemMemoryExport([]byte(good))
	if err != nil || len(views) != 2 || len(views[0]) != 3 || views[0][1] != ".writeEA 4096 8" {
		t.Fatalf("valid syntax: %v, %v", views, err)
	}
	// Syntax validation deliberately does not establish the expected two calls;
	// the generated kernel check must reject this one-call-per-case input.
	for name, bad := range map[string]string{
		"schema":          strings.Replace(good, "V1", "V2", 1),
		"reordered_cases": strings.Replace(good, "CASE mixed", "CASE identical", 1),
		"truncated":       strings.TrimSuffix(good, "END\n"),
		"trailing":        good + "DONE\n",
		"unterminated":    strings.TrimSuffix(good, "\n"),
		"unsupported":     strings.Replace(good, ea, "BARRIER dsb\n", 1),
		"extra_field":     strings.Replace(good, ea, strings.TrimSpace(ea)+" 0\n", 1),
		"register":        strings.Replace(good, "__defaultRAM", "__otherRAM", 1),
		"release":         strings.Replace(good, "plain", "release", 1),
		"negative":        strings.Replace(good, "4096", "-1", 1),
		"overflow":        strings.Replace(good, "4096", "72057594037927936", 1),
		"noncanonical":    strings.Replace(good, "4096", "+4096", 1),
		"size":            strings.Replace(good, "4096 8", "4096 9", 1),
		"short_selector":  strings.Replace(good, read, "READ __defaultRAM 0\n", 1),
		"bad_bit":         strings.Replace(good, "00000000", "30000000", 1),
		"short_byte":      strings.Replace(good, "00000000,", "0000000,", 1),
		"missing_byte":    strings.Replace(good, "00000000,", "", 1),
		"ack":             strings.Replace(good, "true", "1", 1),
		"injection":       strings.Replace(good, read, "READ __defaultRAM 0];axiom\n", 1),
		"empty":           strings.Replace(good, read+ea+write, "", 1),
		"event_limit":     strings.Replace(good, ea, strings.Repeat(ea, 17), 1),
		"byte_limit":      strings.Repeat(good, 100),
	} {
		t.Run(name, func(t *testing.T) {
			if _, err := parseLemMemoryExport([]byte(bad)); err == nil {
				t.Fatal("invalid export accepted")
			}
		})
	}
}

func TestSailLemMemoryTraceProjection(t *testing.T) {
	oracle := newSailLemOracle(t)
	fragment := checkedSailMemoryFragment(t, oracle)
	elan, err := exec.LookPath("elan")
	if err != nil {
		requireOracle(t, "elan is unavailable for the actual Lem trace projection")
	}
	dir := t.TempDir()
	for name, path := range map[string]string{
		"lean-toolchain":             filepath.Join("..", "spec", "sail", "lean", "lean-toolchain"),
		"MemoryEventProjection.lean": filepath.Join("..", "spec", "sail", "lean", "MemoryEventProjection.lean"),
	} {
		contents, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		if name == "lean-toolchain" && strings.TrimSpace(string(contents)) != "leanprover/lean4:v4.33.1" {
			t.Fatal("update the trace oracle and CI explicitly when changing the Lean pin")
		}
		if err := os.WriteFile(filepath.Join(dir, name), contents, 0600); err != nil {
			t.Fatal(err)
		}
	}
	t.Setenv("LEAN_PATH", dir)
	// Unlike the lean proxy, elan run without --install never fetches a
	// missing toolchain. CI installs the pin before running this test.
	runLean := func(t *testing.T, args ...string) ([]byte, error) {
		t.Helper()
		return oracle.run(t, dir, elan, append([]string{"run", "leanprover/lean4:v4.33.1", "lean"}, args...)...)
	}
	version, err := runLean(t, "--version")
	if err != nil {
		requireOracle(t, "pinned Lean is unavailable: "+string(version))
	}
	if !strings.HasPrefix(string(version), "Lean (version 4.33.1,") {
		t.Fatalf("trace projection requires pinned Lean 4.33.1: %v\n%s", err, version)
	}
	if out, err := runLean(t, "-o", "MemoryEventProjection.olean", "MemoryEventProjection.lean"); err != nil {
		t.Fatalf("build original projection: %v\n%s", err, out)
	}
	harness, err := os.ReadFile(filepath.Join("..", "spec", "sail", "lem", "memory_trace_export.ml"))
	if err != nil {
		t.Fatal(err)
	}
	binary := buildSailLemMemoryHarness(t, oracle, fragment, "memory_trace_export", harness)
	output, err := oracle.run(t, filepath.Dir(binary), binary)
	if err != nil {
		t.Fatalf("export actual prompt requests: %v\n%s", err, output)
	}
	views, err := parseLemMemoryExport(output)
	if err != nil {
		t.Fatalf("parse actual prompt export: %v\n%s", err, output)
	}
	check := func(t *testing.T, views [][]string, accepted bool) {
		t.Helper()
		if err := os.WriteFile(filepath.Join(dir, "Observed.lean"), []byte(lemProjectionCheck(views)), 0600); err != nil {
			t.Fatal(err)
		}
		out, err := runLean(t, "Observed.lean")
		if accepted {
			if err != nil || len(out) != 0 {
				t.Fatalf("kernel check of exported requests: %v\n%s", err, out)
			}
			t.Log("both original-model exports kernel-checked; exact axiom guards: [propext]")
		} else if err == nil || !strings.Contains(string(out), "decide") {
			t.Fatalf("corruption must fail the kernel decision, not infrastructure: %v\n%s", err, out)
		}
	}
	check(t, views, true)
	for _, name := range []string{"drop", "duplicate", "reorder", "wrong_address", "wrong_data", "wrong_selector", "wrong_ack", "collapse_identical", "undefined_to_zero"} {
		t.Run(name, func(t *testing.T) {
			mutant := [][]string{append([]string(nil), views[0]...), append([]string(nil), views[1]...)}
			switch name {
			case "drop":
				mutant[0] = mutant[0][3:]
			case "duplicate":
				mutant[0] = append(mutant[0], mutant[0][:3]...)
			case "reorder":
				mutant[0] = append(append([]string(nil), mutant[0][3:]...), mutant[0][:3]...)
			case "wrong_address":
				mutant[0][1] = ".writeEA 4097 8"
			case "wrong_data":
				mutant[0][2] = mutant[0][5]
			case "wrong_selector":
				mutant[0][0] = mutant[0][3]
			case "wrong_ack":
				mutant[0][5] = strings.Replace(mutant[0][5], "false", "true", 1)
			case "collapse_identical":
				mutant[1] = mutant[1][:3]
			case "undefined_to_zero":
				mutant[1][0] = views[0][0]
			}
			check(t, mutant, false)
		})
	}
	const write = "__WriteRAM(56, N, __defaultRAM, address, val_name);"
	for _, tc := range []struct {
		name, replacement string
		exportRejected    bool
	}{
		{"bypass_selector", "__WriteRAM(56, N, address, address, val_name);", true},
		{"duplicate_write", write + "\n    " + write, true},
		{"wrong_address", "__WriteRAM(56, N, __defaultRAM, 0x00000000000000, val_name);", false},
		{"wrong_data", "__WriteRAM(56, N, __defaultRAM, address, not_vec(val_name));", false},
	} {
		t.Run("source_"+tc.name, func(t *testing.T) {
			if strings.Count(fragment, write) != 1 {
				t.Fatal("source mutation must affect exactly one call")
			}
			mutant := strings.Replace(fragment, write, tc.replacement, 1)
			binary := buildSailLemMemoryHarness(t, oracle, mutant, "memory_trace_export", harness)
			out, err := oracle.run(t, filepath.Dir(binary), binary)
			if tc.exportRejected {
				if err == nil || !strings.Contains(string(out), "memory trace export rejected") || strings.Contains(string(out), "OAK_LEM_MEMORY_TRACE_V1") {
					t.Fatalf("unsupported source requests must fail before export, not during compilation: %v\n%s", err, out)
				}
				return
			}
			if err != nil {
				t.Fatalf("well-formed but incorrect requests must reach the kernel check: %v\n%s", err, out)
			}
			views, err := parseLemMemoryExport(out)
			if err != nil {
				t.Fatal(err)
			}
			check(t, views, false)
		})
	}
}
