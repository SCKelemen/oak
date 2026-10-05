package compiler

import (
	"context"
	"fmt"
	"sort"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/opt"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/target"
	"github.com/SCKelemen/oak/wasm"
	"github.com/SCKelemen/oak/wasm/check"
)

// WasmEmission contains only an admitted module and diagnostic DAG provenance.
// Pipeline is not a proof of source-to-Wasm correspondence.
type WasmEmission struct {
	Module   wasm.Module    `json:"module"`
	Pipeline EmissionReport `json:"pipeline"`
}

// EmitWasm emits the experimental core/wasm32 scalar profile. It deliberately
// refuses verified-only builds: source checks and Wasm validation do not yet
// establish formal source-to-output correspondence. No C fallback is possible.
func (comp Compilation) EmitWasm() Stage[wasm.Module] {
	return comp.EmitWasmWithReport().Then(func(result WasmEmission) (wasm.Module, error) {
		return result.Module, nil
	})
}

// EmitWasmWithReport uses the same frontend as EmitWasm and records the typed
// materialization/admission graph. Straight-line frontend checks stay outside
// the DAG. Successful byte admission still does not license -verified.
func (comp Compilation) EmitWasmWithReport() Stage[WasmEmission] {
	if comp.options.VerifiedProfile {
		return Failure[WasmEmission](fmt.Errorf("wasm: source-to-bytes formal verification is not implemented; -verified is unavailable"))
	}
	if comp.options.NativeBodies || comp.options.NativeAsm || len(comp.options.AsmUnits) != 0 || comp.options.CPU != "" {
		return Failure[WasmEmission](fmt.Errorf("wasm: native/assembly/CPU options are not supported"))
	}
	comp = comp.WithTarget(target.Target{OS: target.OSCore, Arch: target.ArchWasm32})
	description, err := comp.requireBackend(target.BackendWasm, "EmitWasm")
	if err != nil {
		return Failure[WasmEmission](err)
	}
	return comp.Check().Then(func(model *SemanticModel) (WasmEmission, error) {
		if len(model.AsmFunctions) != 0 {
			return WasmEmission{}, fmt.Errorf("wasm: assembler units are unsupported")
		}
		planner := newOptIRCallEffectPlanner(model.Tree.Root, model.TypeChecker, nil)
		var inputs []wasm.FunctionInput
		for _, stmt := range model.Tree.Root.Statements {
			fn, ok := stmt.(*ast.FunctionStatement)
			if !ok {
				return WasmEmission{}, fmt.Errorf("wasm: scalar profile supports function declarations only (got %T)", stmt)
			}
			if fn.Name == nil || fn.Body == nil || fn.ExternSymbol != "" || fn.AsmBacked || len(fn.TypeParams) != 0 || fn.Receiver != nil || len(fn.Dispatch) != 0 {
				return WasmEmission{}, fmt.Errorf("wasm: requires concrete, non-extern, non-dispatched functions")
			}
			checked, err := planner.lowerRoot(fn)
			if err != nil {
				return WasmEmission{}, fmt.Errorf("wasm: %s: %w", fn.Name.Value, err)
			}
			inputs = append(inputs, wasm.FunctionInput{Structured: checked.structured, CFG: checked.cfg})
		}
		return emitStructuredWasmGraph(context.Background(), description, inputs)
	})
}

// emitStructuredWasmGraph owns and keys both views of every checked function.
// Materialization independently binds them by exact reprojection. Keeping this
// separate from the raw-CFG test boundary makes structured provenance explicit
// in the artifact recipe without granting it verification authority.
func emitStructuredWasmGraph(ctx context.Context, description target.Description, functions []wasm.FunctionInput) (WasmEmission, error) {
	if description.Backend != target.BackendWasm {
		return WasmEmission{}, fmt.Errorf("wasm: incompatible emission target")
	}
	if len(functions) == 0 || len(functions) > 128 {
		return WasmEmission{}, fmt.Errorf("wasm: need 1..128 functions")
	}
	owned := make([]wasm.FunctionInput, len(functions))
	inputs := make([]opt.ArtifactKey, len(functions))
	for i, function := range functions {
		structured, structuredFingerprint, err := optir.SnapshotFunction(function.Structured)
		if err != nil {
			return WasmEmission{}, err
		}
		cfg, cfgFingerprint, err := optir.SnapshotCFG(function.CFG)
		if err != nil {
			return WasmEmission{}, err
		}
		owned[i] = wasm.FunctionInput{Structured: structured, CFG: cfg}
		structuredKey := opt.ArtifactKey{Kind: opt.ArtifactIR, Name: structured.Name + ".structured", Version: structuredFingerprint}
		cfgKey := opt.ArtifactKey{Kind: opt.ArtifactIR, Name: cfg.Name + ".cfg", Version: cfgFingerprint}
		inputs[i] = opt.ArtifactKey{Kind: opt.ArtifactChecked, Name: cfg.Name,
			Version: opt.DeriveArtifactVersion("oak.wasm.checked-function.v1", structuredKey, cfgKey)}
	}
	sort.Slice(owned, func(i, j int) bool { return owned[i].CFG.Name < owned[j].CFG.Name })
	sort.Slice(inputs, func(i, j int) bool { return inputs[i].Name < inputs[j].Name })
	key := opt.ArtifactKey{Kind: opt.ArtifactChecked, Name: "wasm.checked-structured-cfg",
		Version: opt.DeriveArtifactVersion("oak.wasm.checked-structured-cfg.v1", inputs...)}
	module, report, err := runEmissionGraph(ctx, description, key, owned, emissionBackend[[]wasm.FunctionInput, wasm.Module]{
		name: "wasm", materializeRevision: "oak.wasm.encode.v9/" + wasm.Profile,
		admissionRevision: "oak.wasm.manifest-admission.v1/" + check.Validator + "/" + check.CoreSpecRevision,
		materialize: func(_ context.Context, _ target.Description, input []wasm.FunctionInput) (wasm.Module, error) {
			return wasm.EncodeStructuredCandidate(input)
		},
		admit: admitWasmCandidate,
	})
	if err != nil {
		return WasmEmission{}, err
	}
	return WasmEmission{Module: module, Pipeline: report}, nil
}

// Raw-CFG compatibility and backend tests call this boundary. Production Wasm
// emission uses emitStructuredWasmGraph so lowering-plan identity is retained.
// A valid CFG alone is not permission to substitute an optimized candidate.
func emitWasmGraph(ctx context.Context, description target.Description, cfgs []optir.CFG) (WasmEmission, error) {
	if description.Backend != target.BackendWasm {
		return WasmEmission{}, fmt.Errorf("wasm: incompatible emission target")
	}
	if len(cfgs) == 0 || len(cfgs) > 128 {
		return WasmEmission{}, fmt.Errorf("wasm: need 1..128 functions")
	}
	owned := make([]optir.CFG, len(cfgs))
	inputs := make([]opt.ArtifactKey, len(cfgs))
	for i, cfg := range cfgs {
		snapshot, fingerprint, err := optir.SnapshotCFG(cfg)
		if err != nil {
			return WasmEmission{}, err
		}
		owned[i] = snapshot
		inputs[i] = opt.ArtifactKey{Kind: opt.ArtifactIR, Name: cfg.Name, Version: fingerprint}
	}
	// Declaration order does not affect Wasm output, so normalize input identity.
	sort.Slice(owned, func(i, j int) bool { return owned[i].Name < owned[j].Name })
	sort.Slice(inputs, func(i, j int) bool { return inputs[i].Name < inputs[j].Name })
	key := opt.ArtifactKey{Kind: opt.ArtifactChecked, Name: "wasm.checked-raw-cfg",
		Version: opt.DeriveArtifactVersion("oak.wasm.checked-raw-cfg.v1", inputs...)}
	module, report, err := runEmissionGraph(ctx, description, key, owned, emissionBackend[[]optir.CFG, wasm.Module]{
		name: "wasm", materializeRevision: "oak.wasm.encode.v7/" + wasm.Profile,
		admissionRevision: "oak.wasm.manifest-admission.v1/" + check.Validator + "/" + check.CoreSpecRevision,
		materialize: func(_ context.Context, _ target.Description, input []optir.CFG) (wasm.Module, error) {
			return wasm.EncodeCandidate(input)
		},
		admit: admitWasmCandidate,
	})
	if err != nil {
		return WasmEmission{}, err
	}
	return WasmEmission{Module: module, Pipeline: report}, nil
}

func admitWasmCandidate(_ context.Context, description target.Description, candidate wasm.Module) (wasm.Module, error) {
	if err := description.Validate(); err != nil {
		return wasm.Module{}, err
	}
	if description.Backend != target.BackendWasm {
		return wasm.Module{}, fmt.Errorf("wasm: byte admission requires the Core Wasm target")
	}
	checked, err := candidate.ValidateBytes()
	if err != nil {
		return wasm.Module{}, err
	}
	candidate.ByteValidation = &checked
	return candidate, nil
}
