package asm

import (
	"fmt"
	"path/filepath"
	"regexp"
	"strings"
	"testing"
)

const sailXBank = "register _R : vector(31, dec, bits(64))"
const sailXGetterSignature = "val aget_X : forall 'width 'n,\n" +
	"  ('n >= 0 & 'n <= 31 & 'width in {8, 16, 32, 64}).\n" +
	"  (implicit('width), int('n)) -> bits('width) effect {rreg}"
const sailXGetter = "function aget_X (width, n) = if n != 31 then slice(_R[n], 0, width) else Zeros(width)"

func auditSailXBank(source string) error {
	declaration, err := exactSailRegister(source, "_R")
	if err != nil {
		return err
	}
	if declaration != compactSail(sailXBank) {
		return fmt.Errorf("general-register bank changed: %s", declaration)
	}
	return nil
}

// Check the complete signature and expression through its next declaration,
// not just the first function line: continuations cannot hide extra effects.
func auditSailXGetter(source string) error {
	signature, err := exactSailValParagraph(source, "aget_X")
	if err != nil {
		return err
	}
	if signature != compactSail(sailXGetterSignature) {
		return fmt.Errorf("general-register getter signature changed: %s", signature)
	}
	active, err := stripSailComments(source)
	if err != nil {
		return err
	}
	start, err := exactSailFunctionStart(active, "aget_X")
	if err != nil {
		return err
	}
	tail := active[start+len("function"):]
	next := regexp.MustCompile(`(?m)^(?:val|function|register|type|enum|struct|overload|let)[ \t]`).FindStringIndex(tail)
	if next == nil {
		return fmt.Errorf("general-register getter lacks its immediate X overload")
	}
	end := start + len("function") + next[0]
	if got := compactSail(active[start:end]); got != compactSail(sailXGetter) {
		return fmt.Errorf("general-register getter body changed: %s", got)
	}
	overload, _, _ := strings.Cut(active[end:], "\n")
	if compactSail(overload) != "overloadX={aget_X}" {
		return fmt.Errorf("general-register getter overload changed: %s", overload)
	}
	return nil
}

func TestSailGeneralRegisterBankExactAndMutated(t *testing.T) {
	checkSailMemorySourceGate(t, filepath.Join(filepath.Dir(sailArmModel), "aarch_mem.sail"),
		auditSailXBank, []sailMemoryMutation{
			{"direction", sailXBank, strings.Replace(sailXBank, "dec", "inc", 1)},
			{"count", sailXBank, strings.Replace(sailXBank, "31", "32", 1)},
			{"width", sailXBank, strings.Replace(sailXBank, "64", "32", 1)},
			{"duplicate", sailXBank, sailXBank + "\n" + sailXBank},
			{"commented", sailXBank, "/* " + sailXBank + " */"},
		})
}

func TestSailGeneralRegisterReadExactAndMutated(t *testing.T) {
	checkSailMemorySourceGate(t, filepath.Join(filepath.Dir(sailArmModel), "aarch64.sail"),
		auditSailXGetter, []sailMemoryMutation{
			{"index_domain", sailXGetterSignature, strings.Replace(sailXGetterSignature, "'n <= 31", "'n <= 32", 1)},
			{"width_domain", sailXGetterSignature, strings.Replace(sailXGetterSignature, "8, 16, 32, 64", "8, 16, 32, 64, 128", 1)},
			{"wrong_slot", sailXGetter, strings.Replace(sailXGetter, "_R[n]", "_R[0]", 1)},
			{"reversed_slot", sailXGetter, strings.Replace(sailXGetter, "_R[n]", "_R[30 - n]", 1)},
			{"wrong_slice", sailXGetter, strings.Replace(sailXGetter, ", 0, width", ", 1, width", 1)},
			{"wrong_zero_register", sailXGetter, strings.Replace(sailXGetter, "n != 31", "n != 30", 1)},
			{"zero_reads_bank", sailXGetter, strings.Replace(sailXGetter, "else Zeros(width)", "else slice(_R[0], 0, width)", 1)},
			{"continued_effect", sailXGetter, sailXGetter + ";\n  throw()"},
			{"duplicate", sailXGetter, sailXGetter + "\n" + sailXGetter},
			{"commented", sailXGetter, "/* " + sailXGetter + " */"},
			{"wrong_overload", "overload X = {aget_X}", "overload X = {Zeros}"},
		})
}
