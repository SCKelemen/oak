package asm

// Shifted and extended register operands, and shifted immediates
// (docs/spec/94-assembler.md §3): the A64 data-processing forms
// `add x0, x1, x2, lsl #3`, `add x0, x1, w2, uxtw`, `movz w0, #1, lsl #16`.
// The unit parser folds the trailing shift or extend field into the operand
// before it; the checker reads the register inside; the executor applies the
// shift or extension to the register's term.

import (
	"fmt"
	"strings"
)

// Shifted is a register operand shifted by a constant: `x2, lsl #3`.
type Shifted struct {
	Reg    Register
	Kind   string // lsl lsr asr ror
	Amount int64
}

// Extended is a register operand extended (and optionally shifted):
// `w2, uxtw #2`, `w2, sxtw`.
type Extended struct {
	Reg    Register
	Kind   string // uxtb uxth uxtw uxtx sxtb sxth sxtw sxtx
	Amount int64
}

func (Shifted) operandKind() string  { return "shifted register" }
func (Extended) operandKind() string { return "extended register" }

var shiftKinds = map[string]bool{"lsl": true, "lsr": true, "asr": true, "ror": true, "msl": true}
var extendKinds = map[string]bool{"uxtb": true, "uxth": true, "uxtw": true, "uxtx": true, "sxtb": true, "sxth": true, "sxtw": true, "sxtx": true}

// foldModifier folds a trailing `lsl #n` / `uxtw #n` field into the operand
// before it. It reports whether the field was consumed.
func foldModifier(text string, operands []Operand) ([]Operand, bool, error) {
	fields := strings.Fields(strings.ToLower(text))
	if len(fields) == 0 || len(fields) > 2 || len(operands) == 0 {
		return operands, false, nil
	}
	kind := fields[0]
	if !shiftKinds[kind] && !extendKinds[kind] {
		return operands, false, nil
	}
	var amount int64
	if len(fields) == 2 {
		if !strings.HasPrefix(fields[1], "#") {
			return operands, false, fmt.Errorf("shift amount must be an immediate, got %q", fields[1])
		}
		value, err := parseImmediate(fields[1][1:])
		if err != nil {
			return operands, false, err
		}
		amount = value
	} else if shiftKinds[kind] {
		return operands, false, fmt.Errorf("shift %s needs an amount", kind)
	}
	last := len(operands) - 1
	switch previous := operands[last].(type) {
	case Register:
		if previous.Class != ClassX && previous.Class != ClassW {
			return operands, false, fmt.Errorf("only general registers take a shift or extend, got %s", previous.Text)
		}
		if kind == "msl" {
			return operands, false, fmt.Errorf("msl shifts an immediate, not a register")
		}
		if amount < 0 || amount >= int64(widthOf(previous.Class)) {
			return operands, false, fmt.Errorf("shift amount %d is not below the width of %s", amount, previous.Text)
		}
		if shiftKinds[kind] {
			operands[last] = Shifted{Reg: previous, Kind: kind, Amount: amount}
		} else {
			if amount > 4 {
				return operands, false, fmt.Errorf("extend shift %d exceeds 4", amount)
			}
			operands[last] = Extended{Reg: previous, Kind: kind, Amount: amount}
		}
		return operands, true, nil
	case Immediate:
		// `lsl #n` (wide moves by 16, add/sub by 12, vector immediates by
		// 8) or `msl #n` (vector shifting ones); the checker and the encoder
		// hold each instruction to its own amounts.
		if kind != "lsl" && kind != "msl" || amount < 0 || amount > 63 {
			return operands, false, fmt.Errorf("an immediate takes lsl #n or msl #n, got %s #%d", kind, amount)
		}
		previous.Shift = amount
		previous.MSL = kind == "msl"
		operands[last] = previous
		return operands, true, nil
	}
	return operands, false, fmt.Errorf("a shift or extend must follow a register or immediate")
}

// renderModified spells a shifted or extended operand back.
func renderModified(operand Operand) (string, bool) {
	switch o := operand.(type) {
	case Shifted:
		return fmt.Sprintf("%s, %s #%d", o.Reg.Text, o.Kind, o.Amount), true
	case Extended:
		if o.Amount == 0 {
			return fmt.Sprintf("%s, %s", o.Reg.Text, o.Kind), true
		}
		return fmt.Sprintf("%s, %s #%d", o.Reg.Text, o.Kind, o.Amount), true
	}
	return "", false
}

// operandRegister is the register inside a plain, shifted, or extended
// register operand.
func operandRegister(operand Operand) (Register, bool) {
	switch o := operand.(type) {
	case Register:
		return o, true
	case Shifted:
		return o.Reg, true
	case Extended:
		return o.Reg, true
	}
	return Register{}, false
}

// modifierAllowed reports the mnemonics whose last register operand may be
// shifted (the logical and arithmetic group) or extended (add/sub/cmp/cmn).
func modifierAllowed(mnemonic string, operand Operand) bool {
	switch operand.(type) {
	case Shifted:
		switch mnemonic {
		case "add", "adds", "sub", "subs", "cmp", "cmn", "neg", "negs", "and", "ands", "orr", "eor", "bic", "bics", "orn", "eon", "tst", "mvn":
			return true
		}
	case Extended:
		switch mnemonic {
		case "add", "adds", "sub", "subs", "cmp", "cmn":
			return true
		}
	}
	return false
}
