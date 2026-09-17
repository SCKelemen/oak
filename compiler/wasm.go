package compiler

import (
	"fmt"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/wasm"
)

// EmitWasm emits the experimental core/wasm32 scalar profile. It deliberately
// refuses verified-only builds: source checks and Wasm validation do not yet
// establish formal source-to-output correspondence. No C fallback is possible.
func (comp Compilation) EmitWasm() Stage[wasm.Module] {
	if comp.options.VerifiedProfile {
		return Failure[wasm.Module](fmt.Errorf("wasm: source-to-bytes formal verification is not implemented; -verified is unavailable"))
	}
	if comp.options.NativeBodies || comp.options.NativeAsm || len(comp.options.AsmUnits) != 0 || comp.options.CPU != "" {
		return Failure[wasm.Module](fmt.Errorf("wasm: native/assembly/CPU options are not supported"))
	}
	comp = comp.WithTarget(target.Target{OS: target.OSCore, Arch: target.ArchWasm32})
	return comp.Check().Then(func(model *SemanticModel) (wasm.Module, error) {
		if len(model.AsmFunctions) != 0 {
			return wasm.Module{}, fmt.Errorf("wasm: assembler units are unsupported")
		}
		planner := newOptIRCallEffectPlanner(model.Tree.Root, model.TypeChecker, nil)
		var cfgs []optir.CFG
		for _, stmt := range model.Tree.Root.Statements {
			fn, ok := stmt.(*ast.FunctionStatement)
			if !ok {
				return wasm.Module{}, fmt.Errorf("wasm: scalar v0 supports function declarations only (got %T)", stmt)
			}
			if fn.Name == nil || fn.Body == nil || fn.ExternSymbol != "" || fn.AsmBacked || len(fn.TypeParams) != 0 || fn.Receiver != nil || len(fn.Dispatch) != 0 {
				return wasm.Module{}, fmt.Errorf("wasm: requires concrete, non-extern, non-dispatched functions")
			}
			checked, err := planner.lowerRoot(fn)
			if err != nil {
				return wasm.Module{}, fmt.Errorf("wasm: %s: %w", fn.Name.Value, err)
			}
			cfgs = append(cfgs, checked.cfg)
		}
		return wasm.Emit(cfgs)
	})
}
