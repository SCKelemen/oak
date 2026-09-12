package compiler

// Kernels (docs/spec/56-kernels.md): a function declared with the `kernel`
// marker is held to the kernel subset whether or not Metal output is
// requested, so a kernel that compiles is one the Metal emitter, the C
// backend, the interpreter, and the Lean extraction all agree on. The
// emitter defines the subset (OAK-K0101); this file adds the rules the
// emitter cannot judge alone: every loop the kernel reaches is canonical
// (OAK-K0102) and the kernel reaches no effect and nothing with unknown
// effects (OAK-K0103).

import (
	"errors"
	"fmt"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/codegen/metal"
	"github.com/SCKelemen/oak/diagnostic"
	"github.com/SCKelemen/oak/discipline"
	"github.com/SCKelemen/oak/typechecker"
)

const (
	// CodeKernelSubset reports a kernel, or a function it reaches, outside
	// the kernel subset, naming the construct.
	CodeKernelSubset = "OAK-K0101"
	// CodeKernelLoop reports a loop without a statically evident bound
	// reachable from a kernel; kernels are strict about termination in every
	// profile.
	CodeKernelLoop = "OAK-K0102"
	// CodeKernelEffect reports a kernel that reaches an effect, or code whose
	// effects the compiler cannot know.
	CodeKernelEffect = "OAK-K0103"
	// CodeKernelIndependence reports a span access the checker cannot prove
	// disjoint across grid positions (docs/spec/56-kernels.md section 6).
	CodeKernelIndependence = "OAK-K0104"
)

// analyzeKernels checks every kernel in the specialized program.
func analyzeKernels(program *ast.Program, tc *typechecker.TypeChecker) []*diagnostic.Diagnostic {
	var kernels []*ast.FunctionStatement
	functions := map[string]*ast.FunctionStatement{}
	var order []string
	for _, stmt := range program.Statements {
		fn, ok := stmt.(*ast.FunctionStatement)
		if !ok || fn.Name == nil {
			continue
		}
		if fn.Receiver == nil {
			if _, seen := functions[fn.Name.Value]; !seen {
				functions[fn.Name.Value] = fn
				order = append(order, fn.Name.Value)
			}
		}
		if fn.Kernel {
			kernels = append(kernels, fn)
		}
	}
	if len(kernels) == 0 {
		return nil
	}
	var diags []*diagnostic.Diagnostic
	report := func(code string, node ast.Node, format string, args ...interface{}) {
		diags = append(diags, diagnostic.NewDiagnosticFromNodeWithCode(node, "compiler", code, fmt.Sprintf(format, args...)))
	}
	// Reach and effects come from the effect analysis' call facts, so the
	// loop and effect rules are reported even when the emitter rejects.
	facts := map[string]*effectFacts{}
	for _, name := range order {
		facts[name] = collectEffectFacts(functions[name], functions)
	}
	reach := map[string]string{} // function -> kernel that reaches it
	for _, fn := range kernels {
		queue := []string{fn.Name.Value}
		for len(queue) > 0 {
			name := queue[0]
			queue = queue[1:]
			if _, seen := reach[name]; seen {
				continue
			}
			reach[name] = fn.Name.Value
			if f := facts[name]; f != nil {
				queue = append(queue, f.callees...)
			}
		}
	}
	for _, loop := range discipline.UnboundedLoops(program) {
		if kernel, reached := reach[loop.Function]; reached {
			report(CodeKernelLoop, loop.Loop, "kernel %s reaches a loop in %s with no statically evident bound; kernels use the canonical bounded shape (while i < bound with one i = i + k step) in every profile", kernel, loop.Function)
		}
	}
	for _, fn := range kernels {
		effects, unknown, path := closureEffects(fn.Name.Value, facts)
		if unknown != "" {
			report(CodeKernelEffect, fn.Name, "kernel %s reaches %s (%s), whose effects the compiler cannot know", fn.Name.Value, unknown, strings.Join(path, " -> "))
			continue
		}
		keys := make([]string, 0, len(effects))
		for k := range effects {
			keys = append(keys, k)
		}
		sort.Strings(keys)
		for _, key := range keys {
			report(CodeKernelEffect, fn.Name, "kernel %s performs %s: %s; a kernel body has no effects", fn.Name.Value, key, strings.Join(effects[key], " -> "))
		}
	}
	if _, err := metal.Emit(program, tc); err != nil {
		// The message names the kernel or helper and the construct.
		node := ast.Node(program)
		for _, fn := range kernels {
			if strings.Contains(err.Error(), "kernel "+fn.Name.Value+":") {
				node = fn.Name
			}
		}
		var independence *metal.IndependenceError
		if errors.As(err, &independence) {
			report(CodeKernelIndependence, node, "kernel: %v; a launch runs positions in any order, so every span access must be at the grid position or at gid * T + k under `while k < T` (docs/spec/56-kernels.md section 6)", err)
		} else {
			report(CodeKernelSubset, node, "%v", err)
		}
	}
	return diags
}
