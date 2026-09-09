package asm

// The operand-stack shorthand (docs/spec/94-assembler.md §2): a body may be
// written as
//
//	push left
//	push right
//	add
//
// and is DESUGARED here into ordinary bound-register instructions before the
// seam checker runs — the shorthand is sugar over the same bound values,
// never a runtime stack. `push <param>` names a parameter (its contract
// binding is written for it), `push #imm` an immediate; a data-processing
// mnemonic with no operands pops two values and pushes the result in a
// compiler-chosen scratch register (x9–x15, declared as clobbers for the
// author); the single value left on the stack at the end is moved into the
// result register and the function returns. Anything else — underflow, a
// leftover value, mixing explicit operands into a shorthand body, or a
// shorthand body that also spells its own bindings — is refused. The
// checker then validates the desugared body exactly like handwritten one.

import (
	"fmt"
)

var stackBinaryOps = map[string]bool{"add": true, "sub": true, "and": true, "orr": true, "eor": true, "lsl": true, "lsr": true}

// usesOperandStack reports whether the body is written in the shorthand.
func usesOperandStack(fn *Function) bool {
	for _, item := range fn.Items {
		instr, ok := item.(Instruction)
		if !ok {
			continue
		}
		if instr.Mnemonic == "push" || (stackBinaryOps[instr.Mnemonic] && len(instr.Operands) == 0) {
			return true
		}
	}
	return false
}

// desugarOperandStack rewrites a shorthand body into explicit instructions.
func desugarOperandStack(fn *Function) error {
	if len(fn.Bindings) != 0 {
		return fmt.Errorf("%s: the operand-stack shorthand writes its own bindings; remove the explicit bind lines or the shorthand", fn.Name)
	}
	classes := map[string]RegClass{}
	registers := map[string]int{}
	next := 0
	for _, param := range fn.Signature.Parameters {
		class, ok := contractClass(param.Type)
		if !ok {
			return fmt.Errorf("%s: parameter %s cannot cross the asm boundary", fn.Name, param.Name.Value)
		}
		if class == ClassV {
			return fmt.Errorf("%s: the shorthand covers integer parameters only", fn.Name)
		}
		classes[param.Name.Value] = class
		registers[param.Name.Value] = next
		next++
	}
	resultClass, hasResult := contractClass(fn.Signature.ReturnType)
	if !hasResult {
		return fmt.Errorf("%s: the shorthand needs an integer result type", fn.Name)
	}

	scratch := []int{9, 10, 11, 12, 13, 14, 15}
	used := map[int]bool{}
	alloc := func() (int, error) {
		for _, num := range scratch {
			if !used[num] {
				used[num] = true
				return num, nil
			}
		}
		return 0, fmt.Errorf("%s: more than %d live shorthand values", fn.Name, len(scratch))
	}
	reg := func(class RegClass, num int) Register {
		prefix := "x"
		if class == ClassW {
			prefix = "w"
		}
		return Register{Text: fmt.Sprintf("%s%d", prefix, num), Class: class, Num: num}
	}

	var stack []Operand
	var out []Item
	bound := map[string]bool{}
	temps := map[int]bool{}
	for _, item := range fn.Items {
		instr, ok := item.(Instruction)
		if !ok {
			out = append(out, item)
			continue
		}
		switch {
		case instr.Mnemonic == "push":
			if len(instr.Operands) != 1 {
				return fmt.Errorf("%s:%d: push takes one parameter name or immediate", fn.Name, instr.Line)
			}
			switch operand := instr.Operands[0].(type) {
			case Immediate:
				stack = append(stack, operand)
			case Symbol:
				class, isParam := classes[operand.Name]
				if !isParam {
					return fmt.Errorf("%s:%d: push %s: not a parameter", fn.Name, instr.Line, operand.Name)
				}
				r := reg(class, registers[operand.Name])
				if !bound[operand.Name] {
					bound[operand.Name] = true
					fn.Bindings = append(fn.Bindings, Binding{Register: r, Param: operand.Name, Line: instr.Line})
				}
				stack = append(stack, r)
			default:
				return fmt.Errorf("%s:%d: push takes a parameter name or #immediate", fn.Name, instr.Line)
			}
		case stackBinaryOps[instr.Mnemonic] && len(instr.Operands) == 0:
			if len(stack) < 2 {
				return fmt.Errorf("%s:%d: %s pops two values but the operand stack holds %d", fn.Name, instr.Line, instr.Mnemonic, len(stack))
			}
			right := stack[len(stack)-1]
			left := stack[len(stack)-2]
			stack = stack[:len(stack)-2]
			leftReg, leftIsReg := left.(Register)
			if !leftIsReg {
				// Materialize an immediate left operand.
				num, err := alloc()
				if err != nil {
					return err
				}
				temps[num] = true
				leftReg = reg(resultClass, num)
				out = append(out, Instruction{Mnemonic: "mov", Operands: []Operand{leftReg, left}, Line: instr.Line})
			}
			num, err := alloc()
			if err != nil {
				return err
			}
			temps[num] = true
			dest := reg(leftReg.Class, num)
			out = append(out, Instruction{Mnemonic: instr.Mnemonic, Operands: []Operand{dest, leftReg, right}, Line: instr.Line})
			// Scratch operands are free once consumed.
			for _, consumed := range []Operand{left, right} {
				if r, isReg := consumed.(Register); isReg && temps[r.Num] && r.Num != dest.Num {
					used[r.Num] = false
				}
			}
			stack = append(stack, dest)
		default:
			return fmt.Errorf("%s:%d: %s: a shorthand body holds only push and operand-less data-processing mnemonics", fn.Name, instr.Line, instr.Mnemonic)
		}
	}
	if len(stack) != 1 {
		return fmt.Errorf("%s: the operand stack must hold exactly the result at the end, holds %d", fn.Name, len(stack))
	}
	result := reg(resultClass, 0)
	if top, isReg := stack[0].(Register); !isReg || top.Num != 0 || top.Class != resultClass {
		out = append(out, Instruction{Mnemonic: "mov", Operands: []Operand{result, stack[0]}, Line: fn.Line})
	}
	out = append(out, Instruction{Mnemonic: "ret", Line: fn.Line})
	for num := range temps {
		fn.Clobbers = append(fn.Clobbers, Register{Text: fmt.Sprintf("x%d", num), Class: ClassX, Num: num})
	}
	fn.Items = out
	return nil
}
