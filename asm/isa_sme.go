package asm

// SVE and SME for the seam checker (docs/spec/94-assembler.md §3, §9).
//
// The Apple M4 implements the Scalable Matrix Extension (SME, SME2,
// SME_F64F64, SME_I16I64) and reaches SVE only through SME's streaming
// mode. Their instructions are not hand-listed here: every mnemonic of the
// generated encoding table that needs streaming mode or the ZA array, or
// that names a scalable operand, gets a table-form entry, and its legal
// operand forms are exactly the readings of Arm's templates — the encoder's
// structural match decides. The checker adds the disciplines the templates
// cannot state:
//
//   - mode: an instruction Arm's pseudocode guards with
//     CheckStreamingSVEEnabled / CheckSVEEnabled needs PSTATE.SM, one it
//     guards with the ZA checks needs PSTATE.ZA, and Advanced SIMD guarded
//     by CheckFPAdvSIMDEnabled is illegal in streaming mode; `smstart` and
//     `smstop` switch the modes, tracked along the block;
//   - zeroing: entering or leaving streaming mode zeroes z0-z31 (hence
//     v0-v31) and p0-p15, so a value bound or written before `smstart` is
//     gone after it — reading it is refused;
//   - authority: z registers are the vector registers (clobber vN or zN),
//     predicates need `clobber pN`, the ZA array needs only its mode;
//   - a function returns in the mode it was entered: `ret` with streaming
//     mode or ZA still enabled is refused, as is `bl` inside either;
//   - the SVE loads and stores read their base and index registers and are
//     otherwise trusted (their extent is the predicate's and the vector
//     length's, neither known here) — the trust of §5 stated explicitly.
//
// The bitvector verifier trusts all of it, as it trusts NEON.

import "strings"

func init() {
	scalable := map[string]bool{"smstart": true, "smstop": true, "rdsvl": true, "addsvl": true, "addspl": true}
	for i := range isaEncodings {
		enc := &isaEncodings[i]
		if enc.Mode == "sm" || enc.Mode == "za" || enc.Mode == "smza" || hasScalableOperand(enc) {
			scalable[enc.Mnemonic] = true
		}
	}
	for name := range scalable {
		spec, known := instructionTable[name]
		if !known {
			spec.sysregOperand = -1
		}
		spec.tableForms = true
		instructionTable[name] = spec
	}
}

func hasScalableOperand(enc *isaEncoding) bool {
	for _, form := range enc.Forms {
		for _, op := range form.Operands {
			switch op.Kind {
			case "zreg", "zlane", "preg", "pnreg", "tile", "slice", "zlist", "tilemask":
				return true
			}
		}
	}
	return false
}

// usesScalable reports an instruction spelled with the scalable file: its
// form is decided by the encoding table even under a mnemonic the base
// tables also know (add, mov, ldr, fadd).
func usesScalable(operands []Operand) bool {
	for _, op := range operands {
		switch o := op.(type) {
		case Register:
			if o.Class.Scalable() {
				return true
			}
		case RegisterList:
			for _, reg := range o.Regs {
				if reg.Class.Scalable() {
					return true
				}
			}
		case TileSlice:
			return true
		case Memory:
			if o.MulVL {
				return true
			}
		case Option:
			if o.Mul != 0 {
				return true
			}
		}
	}
	return false
}

// scalable checks one SVE/SME instruction: its form against Arm's
// templates, its mode, and the reads and writes of its operands.
func (c *checker) scalable(instr Instruction) bool {
	_, _, e, err := encodeInstruction(instr, 0, map[string]int64{})
	if err != nil {
		c.errorf(instr.Line, "%s: operands %s match no reading of Arm's template (%v)", instr.Mnemonic, describeOperands(instr.Operands), err)
		return false
	}
	if e == nil {
		return false
	}
	c.requireMode(instr, e.enc.Mode)
	if instr.Mnemonic == "smstart" || instr.Mnemonic == "smstop" {
		c.streamingSwitch(instr)
		return false
	}
	if instr.Mnemonic == "zero" {
		return false // ZA tiles or ZT0: state the mode rule already covers
	}
	m := instr.Mnemonic
	readAll := strings.HasPrefix(m, "st") || strings.HasPrefix(m, "prf") || m == "ptest" || m == "wrffr" || len(instr.Operands) == 0
	if readAll {
		for _, op := range instr.Operands {
			c.readOperand(instr, op)
		}
	} else {
		dest, sources := instr.Operands[0], instr.Operands[1:]
		for _, op := range sources {
			c.readOperand(instr, op)
		}
		if c.destRead(e, instr) {
			c.readOperand(instr, dest)
		}
		c.writeOperand(instr, dest)
	}
	if e.enc.Flags {
		c.flagsValid = true
	}
	return false
}

// requireMode holds an instruction to the PSTATE its pseudocode checks.
func (c *checker) requireMode(instr Instruction, mode string) {
	switch mode {
	case "sm":
		if !c.sm {
			c.errorf(instr.Line, "%s is a streaming SVE instruction: enter streaming mode with smstart first", instr.Mnemonic)
		}
	case "za":
		if !c.za {
			c.errorf(instr.Line, "%s uses the ZA array: enable it with smstart (or smstart za) first", instr.Mnemonic)
		}
	case "smza":
		if !c.sm || !c.za {
			c.errorf(instr.Line, "%s needs streaming mode and the ZA array: smstart first", instr.Mnemonic)
		}
	case "nosm":
		if c.sm {
			c.errorf(instr.Line, "%s is an Advanced SIMD instruction that is illegal in streaming mode (smstop first, or use its SVE form)", instr.Mnemonic)
		}
	}
}

// streamingSwitch applies smstart/smstop: `smstart` enables both modes,
// `smstart sm` / `smstart za` one; smstop likewise. A change of PSTATE.SM
// zeroes the vector and predicate registers.
func (c *checker) streamingSwitch(instr Instruction) {
	on := instr.Mnemonic == "smstart"
	mode := "both"
	if len(instr.Operands) == 1 {
		if opt, ok := instr.Operands[0].(Option); ok {
			mode = opt.Name
		}
	}
	if mode == "both" || mode == "sm" {
		if c.sm != on {
			// Zeroing v8–v15 writes the caller's callee-saved d8–d15: they
			// must have been saved to the frame first, and restored before ret.
			for num := 8; num <= 15; num++ {
				if state := c.calleeSavedV[num]; state != nil {
					if !state.saved {
						c.errorf(instr.Line, "%s zeroes callee-saved d%d (the caller's under AAPCS64): save d8–d15 to the frame first and restore them before ret", instr.Mnemonic, num)
					} else {
						state.written = true
						state.restored = false
					}
				}
			}
			c.writtenV = map[int]bool{}
			c.writtenP = map[int]bool{}
			c.vZeroed = true
		}
		c.sm = on
	}
	if mode == "both" || mode == "za" {
		c.za = on
	}
}

// destRead: the destination is also a source when the template names an
// accumulating register (<Zdn>, <Zda>, <ZAda>, <Pdn>), when a merging
// predicate (/m) keeps its inactive elements, or when a ZA vector is
// accumulated into (fmla za.s[...]) rather than loaded or moved.
func (c *checker) destRead(e *encoder, instr Instruction) bool {
	if e.form != nil && len(e.form.Operands) > 0 {
		sym := e.form.Operands[0].Sym
		if strings.Contains(sym, "dn>") || strings.Contains(sym, "da>") || strings.Contains(sym, "dm>") {
			return true
		}
	}
	for _, op := range instr.Operands {
		if reg, ok := op.(Register); ok && reg.Qual == "m" {
			return true
		}
	}
	if _, isSlice := instr.Operands[0].(TileSlice); isSlice {
		switch {
		case strings.HasPrefix(instr.Mnemonic, "ld"), instr.Mnemonic == "mova", instr.Mnemonic == "mov", instr.Mnemonic == "movaz":
			return false
		}
		return true
	}
	return false
}

// readOperand reads every register an operand names.
func (c *checker) readOperand(instr Instruction, op Operand) {
	switch o := op.(type) {
	case Register:
		c.read(instr, o)
	case Shifted:
		c.read(instr, o.Reg)
	case Extended:
		c.read(instr, o.Reg)
	case RegisterList:
		for _, reg := range o.Regs {
			c.read(instr, reg)
		}
	case TileSlice:
		c.read(instr, o.Index)
	case Memory:
		c.read(instr, o.Base)
		if o.Index != nil {
			c.read(instr, *o.Index)
		}
	}
}

// writeOperand writes every register an operand names (a ZA slice reads
// its index register).
func (c *checker) writeOperand(instr Instruction, op Operand) {
	switch o := op.(type) {
	case Register:
		c.write(instr, o)
	case RegisterList:
		for _, reg := range o.Regs {
			c.write(instr, reg)
		}
	case TileSlice:
		c.read(instr, o.Index)
	}
}
