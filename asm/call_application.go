package asm

import (
	"fmt"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/semir"
	"github.com/SCKelemen/oak/typechecker"
)

// callApplicationInputBits is a profitability boundary, not a semantic one.
// A fixed aggregate is a finite value and may therefore be an application
// argument, but flattening an enormous value would merely move the verifier's
// work from the callee body into the Ackermann input vector.
const (
	callApplicationInputBits = 4096
	callApplicationMinBits   = 512
)

// callApplicationArguments returns the complete finite semantic input of a
// callee after its ABI arguments have been bound in lo.locals. It deliberately
// refuses every source of externally changing state: borrowed memory, mutable
// globals, effectful or foreign calls, atomics, methods, and unknown
// invocations. The ordinary expanded call summary remains the fallback.
func (lo *oakLowering) callApplicationArguments(callee *ast.FunctionStatement) ([]*term, bool) {
	// Witness runs must execute the callee: an application's evidence
	// interpretation is not the source function's result.
	if lo.concrete != nil || lo.expandCallApplications || !lo.finiteCallApplication(callee, map[string]bool{}) {
		return nil, false
	}
	// A partially inlined wrapper and its surviving inner call are not the
	// same uninterpreted application. Expand source-only wrappers, retaining
	// the inner machine boundaries; never change the proof obligations.
	if !lo.retainCallApplication(callee.Name.Value) {
		return nil, false
	}
	var args []*term
	bits := 0
	for _, param := range callee.Parameters {
		if param == nil || param.Name == nil {
			return nil, false
		}
		typ, ok := lo.oakTypeOf(param.Type)
		if !ok {
			return nil, false
		}
		local := lo.locals[param.Name.Value]
		if local == nil {
			return nil, false
		}
		if typ.kind == oakScalar {
			if local.value == nil {
				return nil, false
			}
			args = append(args, truncate(local.value, typ.width))
			bits += typ.width
		} else {
			if local.agg == nil || local.agg.hasSpan() || !appendApplicationLeaves(local.agg, typ, &args, &bits) {
				return nil, false
			}
		}
		if bits > callApplicationInputBits {
			return nil, false
		}
	}
	result, ok := lo.oakTypeOf(callee.ReturnType)
	resultBits, ok := applicationTypeBits(result)
	if !ok || resultBits > callApplicationInputBits {
		return nil, false
	}
	// An application is a candidate, not an obligation. Small straight-line
	// bodies are cheaper and more precise when expanded; loops and wide value
	// boundaries are where suppressing the body pays for the Ackermann input.
	if !bodyHasLoop(callee.Body, lo.functions) && bits+resultBits < callApplicationMinBits {
		return nil, false
	}
	return args, true
}

// appendApplicationLeaves follows the declared type, never map iteration, so
// the machine and Oak lowerings use the same stable argument order.
func appendApplicationLeaves(value *oakValue, typ *oakType, into *[]*term, bits *int) bool {
	if value == nil || typ == nil {
		return false
	}
	switch typ.kind {
	case oakScalar:
		if value.scalar == nil {
			return false
		}
		*into = append(*into, truncate(value.scalar, typ.width))
		*bits += typ.width
		return *bits <= callApplicationInputBits
	case oakRecord:
		for _, field := range typ.fields {
			if !appendApplicationLeaves(value.fields[field.name], field.typ, into, bits) {
				return false
			}
		}
		return true
	case oakADT:
		if !appendApplicationLeaves(value.fields["tag"], &oakType{kind: oakScalar, width: 32}, into, bits) {
			return false
		}
		for _, variant := range typ.variants {
			if variant.payload != nil && !appendApplicationLeaves(value.fields[variant.name], variant.payload, into, bits) {
				return false
			}
		}
		return true
	case oakArray:
		if int64(len(value.elems)) != typ.length {
			return false
		}
		for _, elem := range value.elems {
			if !appendApplicationLeaves(elem, typ.elem, into, bits) {
				return false
			}
		}
		return true
	}
	return false
}

func (lo *oakLowering) finiteCallApplication(callee *ast.FunctionStatement, visiting map[string]bool) bool {
	if callee == nil || callee.Name == nil || callee.Name.Value == "" || callee.Body == nil ||
		callee.ExternSymbol != "" || callee.Receiver != nil || len(callee.TypeParams) != 0 ||
		len(callee.Effects) != 0 || unitFunction(callee) {
		return false
	}
	name := callee.Name.Value
	if visiting[name] {
		return false
	}
	visiting[name] = true
	defer delete(visiting, name)

	for _, param := range callee.Parameters {
		if param == nil || param.Name == nil || param.Variadic || isBorrowType(param.Type) {
			return false
		}
		typ, ok := lo.oakTypeOf(param.Type)
		if !ok || !finiteApplicationType(typ) {
			return false
		}
	}
	result, ok := lo.oakTypeOf(callee.ReturnType)
	if !ok || !finiteApplicationType(result) {
		return false
	}

	safe := true
	walkASTNodes(callee.Body, func(node ast.Node) {
		if !safe {
			return
		}
		switch node := node.(type) {
		case *ast.Identifier:
			if _, mutable := lo.globals[node.Value]; mutable && !lo.declaredTables[node.Value] {
				safe = false
			}
		case *ast.InvocationExpression:
			if node.ResolvedMethod != "" {
				safe = false
				return
			}
			if _, simd := simdMember(node.Function); simd {
				return
			}
			if _, _, instruction := instructionFunction(node); instruction {
				return
			}
			ident, direct := node.Function.(*ast.Identifier)
			if !direct {
				safe = false
				return
			}
			if _, atomic := semir.LookupAtomicBuiltin(ident.Value); atomic {
				safe = false
				return
			}
			if nested := lo.functions[ident.Value]; nested != nil {
				safe = lo.finiteCallApplication(nested, visiting)
				return
			}
			if external := lo.externs[ident.Value]; external != nil || !finiteApplicationBuiltin(ident.Value, node) {
				safe = false
			}
		}
	})
	return safe
}

func finiteApplicationType(typ *oakType) bool {
	if typ == nil || strings.HasPrefix(typ.name, "simd.") {
		return false
	}
	switch typ.kind {
	case oakScalar:
		return !typ.float
	case oakRecord:
		for _, field := range typ.fields {
			if !finiteApplicationType(field.typ) {
				return false
			}
		}
		return true
	case oakADT:
		for _, variant := range typ.variants {
			if variant.payload != nil && !finiteApplicationType(variant.payload) {
				return false
			}
		}
		return true
	case oakArray:
		return typ.length > 0 && finiteApplicationType(typ.elem)
	}
	return false
}

func applicationTypeBits(typ *oakType) (int, bool) {
	if typ == nil {
		return 0, false
	}
	switch typ.kind {
	case oakScalar:
		return typ.width, typ.width > 0 && typ.width <= 64
	case oakRecord:
		total := 0
		for _, field := range typ.fields {
			bits, ok := applicationTypeBits(field.typ)
			if !ok || total > callApplicationInputBits-bits {
				return 0, false
			}
			total += bits
		}
		return total, true
	case oakADT:
		total := 32
		for _, variant := range typ.variants {
			if variant.payload == nil {
				continue
			}
			bits, ok := applicationTypeBits(variant.payload)
			if !ok || total > callApplicationInputBits-bits {
				return 0, false
			}
			total += bits
		}
		return total, true
	case oakArray:
		bits, ok := applicationTypeBits(typ.elem)
		if !ok || typ.length <= 0 || typ.length > int64(callApplicationInputBits) || bits > callApplicationInputBits/int(typ.length) {
			return 0, false
		}
		return int(typ.length) * bits, true
	}
	return 0, false
}

func finiteApplicationBuiltin(name string, call *ast.InvocationExpression) bool {
	switch name {
	case "assert", "len", "span", "view", "subslice":
		return true
	case "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "f32", "f64":
		return len(call.Arguments) == 1
	}
	if _, _, _, conversion := typechecker.ConversionParts(name); conversion {
		return len(call.Arguments) == 1
	}
	return typechecker.FloatIntrinsicName(name)
}

func callApplicationName(callee string, leaf string) string {
	if leaf == "" {
		return "call:" + callee + ":result"
	}
	return fmt.Sprintf("call:%s:result%s", callee, leaf)
}

func callApplicationValue(callee string, typ *oakType, args []*term) (*oakValue, bool) {
	return aggregateFrom(typ, "", func(path string, leaf *oakType) *term {
		return applyTerm(callApplicationName(callee, path), leaf.width, args...)
	})
}

// retainCallApplication applies only the source representation policy. The
// ordinary purity, argument, profitability and proof checks still apply.
func (lo *oakLowering) retainCallApplication(callee string) bool {
	if lo.machineApplications == nil {
		return true
	}
	prefix := callApplicationName(callee, "")
	if lo.machineApplications[prefix] {
		return true
	}
	for name := range lo.machineApplications {
		if strings.HasPrefix(name, prefix+"[") || strings.HasPrefix(name, prefix+".") {
			return true
		}
	}
	return false
}

// machineCallApplications records the actual application boundaries before
// lowering the source. A loop's final result can be only a fresh symbol: its
// next values, conditions, traps and memories still contain the applications
// that the source must retain. Each term in the shared DAG is visited once.
func machineCallApplications(result *term, execution *pathExecutor) map[string]bool {
	applications := map[string]bool{}
	seen := map[*term]bool{}
	var visit func(*term)
	visit = func(t *term) {
		if t == nil || seen[t] {
			return
		}
		seen[t] = true
		if t.kind == termApply {
			applications[t.name] = true
		}
		visit(t.cond)
		visit(t.left)
		visit(t.right)
		for _, arg := range t.args {
			visit(arg)
		}
	}
	visitMap := func(values map[string]*term) {
		for _, value := range values {
			visit(value)
		}
	}
	visitWrites := func(logs map[string][]*spanWrite) {
		for _, writes := range logs {
			for _, write := range writes {
				visit(write.index)
				visit(write.value)
				visit(write.guard)
			}
		}
	}
	visit(result)
	if execution == nil {
		return applications
	}
	for _, result := range execution.moreResults {
		visit(result)
	}
	visit(execution.trap)
	visitMap(execution.cells)
	visitWrites(execution.writes)
	for _, event := range execution.loops {
		visit(event.cond)
		visit(event.headerTrap)
		visit(event.bodyTrap)
		visit(event.reached)
		visit(event.oakPath)
		visitMap(event.header)
		visitMap(event.fresh)
		visitMap(event.next)
		visitWrites(event.entry)
		visitWrites(event.writes)
	}
	return applications
}
