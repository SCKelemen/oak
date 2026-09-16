package compiler

import (
	"errors"
	"fmt"
	"sort"
	"strconv"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

// OptIRFunction is one checked structured projection, its independently
// verified CFG/SSA view, and optimization results. The native candidate search
// may select the pure LoopInvariant result or the final region-memory
// MemoryCleanup.CFG result through its fail-closed AArch64 and RV64 selectors.
type OptIRFunction struct {
	Name                  string
	Structured            optir.Function
	CheckedFacts          optir.CheckedFactAuthority
	CheckedFactsHash      string
	CheckedMemory         optir.CheckedMemoryAuthority
	CheckedMemoryHash     string
	CFG                   optir.CFG
	Constants             optir.SCCPResult
	SCCPSimplified        optir.CFG
	SCCPRewrite           optir.SCCPRewriteReport
	Loops                 optir.LoopAnalysis
	Simplified            optir.CFG
	Simplification        optir.GVNDCEReport
	LoopInvariant         optir.CFG
	LoopMotion            optir.LICMReport
	MemoryProjection      optir.CheckedMemoryProjection
	MemorySSA             optir.RegionMemorySSA
	MemoryLiveness        optir.MemoryDefinitionLiveness
	DeadStores            optir.CFG
	DeadStoreMetadata     optir.RegionMemoryMetadata
	DeadStoreElimination  optir.DeadStoreEliminationReport
	ForwardedLoads        optir.CFG
	ForwardedLoadMetadata optir.RegionMemoryMetadata
	RegionLoadForwarding  optir.RegionLoadForwardingReport
	MemoryCleanup         OptIRMemoryCleanup
	FinalMemoryProjection optir.CheckedMemoryProjection
	FinalMemorySSA        optir.RegionMemorySSA
}

// OptIRRefusal is an ordinary unsupported-subset result. The function remains
// on the existing backend path; no partial OptIR is returned for it.
type OptIRRefusal struct {
	Function string
	Reason   string
	Source   optir.Source
}

type OptIRModule struct {
	Functions []OptIRFunction
	Refusals  []OptIRRefusal
}

// OptIR checks the program as written and projects every supported concrete
// scalar function. It is also the public inspection API for the same middle
// end whose optimized result can enter native candidate search.
func (comp Compilation) OptIR() Stage[OptIRModule] {
	return comp.Check().Then(func(model *SemanticModel) (OptIRModule, error) {
		return lowerOptIRModule(model)
	})
}

type optIRUnsupported struct {
	reason string
	source optir.Source
}

func (unsupported *optIRUnsupported) Error() string { return unsupported.reason }

// optIRCallEffectPlanner derives exact scalar Mod/Ref summaries from checked
// projections, never from a source-level effect annotation. Direct whole-cell
// stores become conservative may-write effects at call boundaries.
type optIRCallEffectPlanner struct {
	tc        *typechecker.TypeChecker
	globals   map[string]optir.Type
	functions map[string]*ast.FunctionStatement
	visiting  map[string]bool
	cache     map[string]optIRCheckedProjection
}

type optIRCheckedProjection struct {
	structured optir.Function
	facts      optir.CheckedFactAuthority
	memory     optir.CheckedMemoryAuthority
	cfg        optir.CFG
	summary    optir.CheckedMemoryCallSummary
}

func newOptIRCallEffectPlanner(root *ast.Program, tc *typechecker.TypeChecker, globals map[string]optir.Type) *optIRCallEffectPlanner {
	functions := map[string]*ast.FunctionStatement{}
	if root != nil {
		for _, statement := range root.Statements {
			function, ok := statement.(*ast.FunctionStatement)
			if ok && function.Name != nil {
				functions[function.Name.Value] = function
			}
		}
	}
	return &optIRCallEffectPlanner{
		tc: tc, globals: globals, functions: functions,
		visiting: map[string]bool{}, cache: map[string]optIRCheckedProjection{},
	}
}

func (planner *optIRCallEffectPlanner) lower(function *ast.FunctionStatement) (optIRCheckedProjection, error) {
	if function == nil || function.Name == nil || function.Name.Value == "" {
		return optIRCheckedProjection{}, refuseOptIR(token.Token{}, "unnamed call target cannot receive a checked call-effect summary")
	}
	name := function.Name.Value
	if cached, exists := planner.cache[name]; exists {
		return cached, nil
	}
	if function.Body == nil || function.ExternSymbol != "" || function.AsmBacked {
		return optIRCheckedProjection{}, refuseOptIR(function.Token, "callee %s has no concrete internal Oak body", name)
	}
	if function.Receiver != nil || len(function.TypeParams) != 0 {
		return optIRCheckedProjection{}, refuseOptIR(function.Token, "callee %s is not a concrete nonmethod function", name)
	}
	if len(function.Dispatch) != 0 {
		return optIRCheckedProjection{}, refuseOptIR(function.Token, "callee %s has target-dispatched realizations", name)
	}
	if planner.visiting[name] {
		return optIRCheckedProjection{}, refuseOptIR(function.Token, "recursive call cycle through %s has no finite call-effect summary", name)
	}
	planner.visiting[name] = true
	defer delete(planner.visiting, name)

	structured, facts, memory, err := lowerCheckedOptIRFunctionWithCalls(function, planner.tc, planner.globals, planner.authorizeCall)
	if err != nil {
		return optIRCheckedProjection{}, err
	}
	cfg, err := projectCheckedOptIRFunction(structured, memory)
	if err != nil {
		return optIRCheckedProjection{}, fmt.Errorf("compiler: OptIR projection of %s failed verification: %w", name, err)
	}
	if err := optir.VerifyCFGCheckedFacts(cfg, facts); err != nil {
		return optIRCheckedProjection{}, fmt.Errorf("compiler: OptIR checked facts for %s failed after projection: %w", name, err)
	}
	summary, err := optir.DeriveCheckedMemoryCallSummary(cfg, memory)
	if err != nil {
		return optIRCheckedProjection{}, fmt.Errorf("compiler: OptIR call-effect summary for %s: %w", name, err)
	}
	projection := optIRCheckedProjection{
		structured: structured, facts: facts, memory: memory, cfg: cfg, summary: summary,
	}
	planner.cache[name] = projection
	return projection, nil
}

// lowerRoot preserves the pre-summary call-only OptIR subset. It first asks
// for the strict recursively checked projection. If that ordinary subset
// refusal was solely needed to summarize a call, a second unsummarized
// lowering may still succeed when the caller has no direct checked memory.
// The old mixed-memory guard remains in that lowering, so this fallback cannot
// authorize a memory transform.
func (planner *optIRCallEffectPlanner) lowerRoot(function *ast.FunctionStatement) (optIRCheckedProjection, error) {
	checked, strictErr := planner.lower(function)
	if strictErr == nil {
		return checked, nil
	}
	var unsupported *optIRUnsupported
	if !errors.As(strictErr, &unsupported) {
		return optIRCheckedProjection{}, strictErr
	}
	structured, facts, memory, err := lowerCheckedOptIRFunction(function, planner.tc, planner.globals)
	if err != nil {
		return optIRCheckedProjection{}, strictErr
	}
	cfg, err := projectCheckedOptIRFunction(structured, memory)
	if err != nil {
		return optIRCheckedProjection{}, fmt.Errorf("compiler: fallback OptIR projection of %s failed verification: %w", function.Name.Value, err)
	}
	if err := optir.VerifyCFGCheckedFacts(cfg, facts); err != nil {
		return optIRCheckedProjection{}, fmt.Errorf("compiler: fallback OptIR checked facts for %s failed after projection: %w", function.Name.Value, err)
	}
	return optIRCheckedProjection{structured: structured, facts: facts, memory: memory, cfg: cfg}, nil
}

func (planner *optIRCallEffectPlanner) authorizeCall(name string) (optir.CheckedMemoryCallSummary, error) {
	function, exists := planner.functions[name]
	if !exists {
		return optir.CheckedMemoryCallSummary{}, refuseOptIR(token.Token{}, "callee %s is unknown or not an internal function", name)
	}
	projection, err := planner.lower(function)
	if err != nil {
		return optir.CheckedMemoryCallSummary{}, err
	}
	return projection.summary, nil
}

// memoryCallCertificate closes one optimized root over exactly the concrete
// checked callees still reachable from that CFG. The planner cache can contain
// projections built for unrelated module functions, so it is deliberately not
// used as the certificate node set.
func (planner *optIRCallEffectPlanner) memoryCallCertificate(root string, cfg optir.CFG, authority optir.CheckedMemoryAuthority) (optir.CheckedMemoryCallCertificate, error) {
	if planner == nil || root == "" {
		return optir.CheckedMemoryCallCertificate{}, fmt.Errorf("compiler: checked memory-call certificate has no root")
	}
	cached, exists := planner.cache[root]
	if !exists || cached.memory.Fingerprint() != authority.Fingerprint() {
		return optir.CheckedMemoryCallCertificate{}, fmt.Errorf("compiler: checked memory-call certificate root %q is not the cached authority", root)
	}

	nodes := make([]optir.CheckedMemoryCallCertificateNode, 0, len(planner.cache))
	seen := map[string]bool{}
	var collect func(string, optir.CFG, optir.CheckedMemoryAuthority) error
	collect = func(name string, current optir.CFG, memory optir.CheckedMemoryAuthority) error {
		if seen[name] {
			return nil
		}
		seen[name] = true
		nodes = append(nodes, optir.CheckedMemoryCallCertificateNode{Name: name, CFG: current, Authority: memory})
		calls, err := activeOptIRMemoryCalls(current, memory)
		if err != nil {
			return fmt.Errorf("compiler: checked memory-call certificate node %q: %w", name, err)
		}
		for _, call := range calls {
			child, exists := planner.cache[call.Callee]
			if !exists {
				return fmt.Errorf("compiler: checked memory-call certificate node %q is missing cached callee %q", name, call.Callee)
			}
			if err := collect(call.Callee, child.cfg, child.memory); err != nil {
				return err
			}
		}
		return nil
	}
	if err := collect(root, cfg, authority); err != nil {
		return optir.CheckedMemoryCallCertificate{}, err
	}
	return optir.NewCheckedMemoryCallCertificate(root, nodes)
}

func activeOptIRMemoryCalls(cfg optir.CFG, authority optir.CheckedMemoryAuthority) ([]optir.CheckedMemoryCallRecord, error) {
	byID := make(map[string]optir.CheckedMemoryCallRecord, len(authority.CallRecords()))
	for _, record := range authority.CallRecords() {
		byID[record.ID] = record
	}
	active := map[string]optir.CheckedMemoryCallRecord{}
	for _, block := range cfg.Blocks {
		for _, operation := range block.Operations {
			if operation.MemoryCallID == "" {
				continue
			}
			record, exists := byID[operation.MemoryCallID]
			if !exists {
				return nil, fmt.Errorf("operation refers to unknown checked call ID %s", operation.MemoryCallID)
			}
			active[record.ID] = record
		}
	}
	ids := make([]string, 0, len(active))
	for id := range active {
		ids = append(ids, id)
	}
	sort.Strings(ids)
	calls := make([]optir.CheckedMemoryCallRecord, 0, len(ids))
	for _, id := range ids {
		calls = append(calls, active[id])
	}
	return calls, nil
}

func lowerOptIRModule(model *SemanticModel) (OptIRModule, error) {
	if model == nil || model.Tree == nil || model.Tree.Root == nil || model.TypeChecker == nil {
		return OptIRModule{}, fmt.Errorf("compiler: OptIR requires a checked semantic model")
	}
	var module OptIRModule
	globals := checkedOptIRGlobals(model.Tree.Root, model.TypeChecker)
	planner := newOptIRCallEffectPlanner(model.Tree.Root, model.TypeChecker, globals)
	for _, statement := range model.Tree.Root.Statements {
		function, isFunction := statement.(*ast.FunctionStatement)
		if !isFunction || function.Name == nil || function.Body == nil || function.ExternSymbol != "" || function.AsmBacked || len(function.TypeParams) != 0 {
			continue
		}
		checked, err := planner.lowerRoot(function)
		if err != nil {
			var unsupported *optIRUnsupported
			if errors.As(err, &unsupported) {
				module.Refusals = append(module.Refusals, OptIRRefusal{Function: function.Name.Value, Reason: unsupported.reason, Source: unsupported.source})
				continue
			}
			return OptIRModule{}, err
		}
		structured, authority, memoryAuthority, cfg := checked.structured, checked.facts, checked.memory, checked.cfg
		analyses, err := runOptIRAnalysisGraphWithMemory(cfg, memoryAuthority)
		if err != nil {
			return OptIRModule{}, fmt.Errorf("compiler: OptIR analysis graph for %s failed: %w", function.Name.Value, err)
		}
		if err := verifyOptIRAnalysisFacts(authority, analyses); err != nil {
			return OptIRModule{}, fmt.Errorf("compiler: OptIR checked facts for %s failed after optimization: %w", function.Name.Value, err)
		}
		module.Functions = append(module.Functions, OptIRFunction{
			Name:                  function.Name.Value,
			Structured:            structured,
			CheckedFacts:          authority,
			CheckedFactsHash:      authority.Fingerprint(),
			CheckedMemory:         memoryAuthority,
			CheckedMemoryHash:     memoryAuthority.Fingerprint(),
			CFG:                   cfg,
			Constants:             analyses.constants,
			SCCPSimplified:        analyses.sccpSimplified,
			SCCPRewrite:           analyses.sccpSimplification,
			Loops:                 analyses.loops,
			Simplified:            analyses.simplified,
			Simplification:        analyses.simplification,
			LoopInvariant:         analyses.loopInvariant,
			LoopMotion:            analyses.loopMotion,
			MemoryProjection:      analyses.memoryProjection,
			MemorySSA:             analyses.memorySSA,
			MemoryLiveness:        analyses.memoryLiveness,
			DeadStores:            analyses.deadStores,
			DeadStoreMetadata:     analyses.deadStoreMetadata,
			DeadStoreElimination:  analyses.deadStoreElimination,
			ForwardedLoads:        analyses.regionLoads,
			ForwardedLoadMetadata: analyses.regionLoadMetadata,
			RegionLoadForwarding:  analyses.regionLoadForwarding,
			MemoryCleanup:         analyses.memoryCleanup,
			FinalMemoryProjection: analyses.memoryCleanup.Projection,
			FinalMemorySSA:        analyses.memoryCleanup.MemorySSA,
		})
	}
	return module, nil
}

type optIRIDs struct{ next optir.ValueID }

func (ids *optIRIDs) value(typ optir.Type, name string, source optir.Source) optir.Value {
	value := optir.Value{ID: ids.next, Type: typ, Name: name, Source: source}
	ids.next++
	return value
}

type optIRLowerer struct {
	tc     *typechecker.TypeChecker
	ids    *optIRIDs
	env    map[string]optir.Value
	facts  *optIRFactBuilder
	memory *optIRMemoryBuilder
}

type optIRFactBuilder struct {
	records map[string]optir.CheckedFactRecord
	values  map[string]optir.ValueID
	err     error
}

type optIRMemoryBuilder struct {
	globals          map[string]optir.Type
	records          map[string]optir.CheckedMemoryAccessRecord
	callRecords      map[string]optir.CheckedMemoryCallRecord
	authorizeCall    func(string) (optir.CheckedMemoryCallSummary, error)
	unsummarizedCall bool
	err              error
}

func lowerCheckedOptIRFunction(function *ast.FunctionStatement, tc *typechecker.TypeChecker, globals map[string]optir.Type) (optir.Function, optir.CheckedFactAuthority, optir.CheckedMemoryAuthority, error) {
	return lowerCheckedOptIRFunctionWithCalls(function, tc, globals, nil)
}

func lowerCheckedOptIRFunctionWithCalls(function *ast.FunctionStatement, tc *typechecker.TypeChecker, globals map[string]optir.Type, authorizeCall func(string) (optir.CheckedMemoryCallSummary, error)) (optir.Function, optir.CheckedFactAuthority, optir.CheckedMemoryAuthority, error) {
	if function.Receiver != nil {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, refuseOptIR(function.Token, "methods are not in the first OptIR projection subset")
	}
	if function.Kernel {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, refuseOptIR(function.Token, "kernels retain their dedicated checked representation")
	}
	if function.Lowering != nil {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, refuseOptIR(function.Token, "compiler-projected protocol functions retain their table lowering")
	}
	signatureType, exists := tc.Env().GetType(function.Name.Value)
	signature, isFunction := signatureType.(*typechecker.FunctionType)
	if !exists || !isFunction || len(signature.Parameters) != len(function.Parameters) {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, fmt.Errorf("compiler: checked signature for OptIR function %s is unavailable", function.Name.Value)
	}
	resultType, supported := checkedOptIRType(tc, signature.ReturnType)
	if !supported {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, refuseOptIR(function.Token, "return type %s is outside the scalar OptIR subset", signature.ReturnType)
	}
	lowerer := &optIRLowerer{
		tc: tc, ids: &optIRIDs{next: 1}, env: map[string]optir.Value{},
		facts: &optIRFactBuilder{records: map[string]optir.CheckedFactRecord{}, values: map[string]optir.ValueID{}},
		memory: &optIRMemoryBuilder{
			globals: globals, records: map[string]optir.CheckedMemoryAccessRecord{},
			callRecords: map[string]optir.CheckedMemoryCallRecord{}, authorizeCall: authorizeCall,
		},
	}
	structured := optir.Function{Name: function.Name.Value, Results: []optir.Type{resultType}}
	for index, parameter := range function.Parameters {
		if parameter == nil || parameter.Name == nil || parameter.Variadic {
			return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, refuseOptIR(function.Token, "variadic or unnamed parameters are outside the scalar OptIR subset")
		}
		typ, ok := checkedOptIRType(tc, signature.Parameters[index])
		if !ok {
			return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, refuseOptIR(parameter.Token, "parameter %s has unsupported type %s", parameter.Name.Value, signature.Parameters[index])
		}
		value := lowerer.ids.value(typ, parameter.Name.Value, optIRSource(parameter.Token))
		structured.Parameters = append(structured.Parameters, value)
		lowerer.env[parameter.Name.Value] = value
	}

	var returned optir.Value
	var err error
	switch body := function.Body.(type) {
	case *ast.BlockExpression:
		returned, err = lowerer.lowerBlock(body.Block, &structured.Body, true, false)
	default:
		returned, err = lowerer.lowerExpression(body, &structured.Body)
	}
	if err != nil {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, err
	}
	if returned.Type != resultType {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, fmt.Errorf("compiler: OptIR function %s produced %s, checked return is %s", function.Name.Value, returned.Type, resultType)
	}
	structured.Body.Yield = []optir.ValueID{returned.ID}
	if lowerer.facts.err != nil {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, lowerer.facts.err
	}
	if lowerer.memory.err != nil {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, lowerer.memory.err
	}
	if lowerer.memory.unsummarizedCall && len(lowerer.memory.records) != 0 {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, refuseOptIR(function.Token, "calls mixed with checked global memory require interprocedural effect summaries")
	}
	records := make([]optir.CheckedFactRecord, 0, len(lowerer.facts.records))
	for _, record := range lowerer.facts.records {
		records = append(records, record)
	}
	authority, err := optir.NewCheckedFactAuthority(records)
	if err != nil {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, fmt.Errorf("compiler: OptIR checked fact authority for %s: %w", function.Name.Value, err)
	}
	if err := optir.VerifyFunctionCheckedFacts(structured, authority); err != nil {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, fmt.Errorf("compiler: OptIR checked facts for %s: %w", function.Name.Value, err)
	}
	memoryRecords := make([]optir.CheckedMemoryAccessRecord, 0, len(lowerer.memory.records))
	for _, record := range lowerer.memory.records {
		memoryRecords = append(memoryRecords, record)
	}
	callRecords := make([]optir.CheckedMemoryCallRecord, 0, len(lowerer.memory.callRecords))
	for _, record := range lowerer.memory.callRecords {
		callRecords = append(callRecords, record)
	}
	memoryAuthority, err := optir.NewCheckedMemoryAuthorityWithCalls(memoryRecords, callRecords)
	if err != nil {
		return optir.Function{}, optir.CheckedFactAuthority{}, optir.CheckedMemoryAuthority{}, fmt.Errorf("compiler: OptIR checked memory authority for %s: %w", function.Name.Value, err)
	}
	return structured, authority, memoryAuthority, nil
}

func checkedOptIRType(tc *typechecker.TypeChecker, typ typechecker.Type) (optir.Type, bool) {
	switch concrete := typ.(type) {
	case *typechecker.BoolType:
		return optir.TypeBool, true
	case *typechecker.UnitType:
		return optir.Type("()"), true
	case *typechecker.PrimitiveType:
		if concrete.Refinement != "" {
			return "", false
		}
		if name := tc.FixedWidthName(concrete.Name); name != "" {
			return optir.Type(name), true
		}
	}
	return "", false
}

func checkedOptIRGlobals(root *ast.Program, tc *typechecker.TypeChecker) map[string]optir.Type {
	globals := map[string]optir.Type{}
	if root == nil || tc == nil || tc.Env() == nil {
		return globals
	}
	for _, statement := range root.Statements {
		declaration, ok := statement.(*ast.VariableDeclaration)
		if !ok || declaration.Name == nil {
			continue
		}
		checked, exists := tc.Env().GetType(declaration.Name.Value)
		if !exists {
			continue
		}
		typ, supported := checkedOptIRType(tc, checked)
		if supported && typ != optir.Type("()") {
			globals[declaration.Name.Value] = typ
		}
	}
	return globals
}

func projectCheckedOptIRFunction(function optir.Function, memoryAuthority optir.CheckedMemoryAuthority) (optir.CFG, error) {
	if len(memoryAuthority.Records()) == 0 && len(memoryAuthority.CallRecords()) == 0 {
		return optir.Project(function)
	}
	cfg, projection, err := optir.ProjectWithCheckedMemory(function, memoryAuthority)
	if err != nil {
		return optir.CFG{}, err
	}
	if err := optir.VerifyCheckedMemoryProjection(cfg, memoryAuthority, projection); err != nil {
		return optir.CFG{}, err
	}
	return cfg, nil
}

func (lowerer *optIRLowerer) clone() *optIRLowerer {
	environment := make(map[string]optir.Value, len(lowerer.env))
	for name, value := range lowerer.env {
		environment[name] = value
	}
	return &optIRLowerer{tc: lowerer.tc, ids: lowerer.ids, env: environment, facts: lowerer.facts, memory: lowerer.memory}
}

func (lowerer *optIRLowerer) lowerBlock(block *ast.BlockStatement, region *optir.Region, wantResult, scoped bool) (optir.Value, error) {
	if block == nil {
		return optir.Value{}, refuseOptIR(token.Token{}, "nil block is outside OptIR")
	}
	outer := map[string]bool{}
	if scoped {
		for name := range lowerer.env {
			outer[name] = true
		}
		defer func() {
			for name := range lowerer.env {
				if !outer[name] {
					delete(lowerer.env, name)
				}
			}
		}()
	}
	var last optir.Value
	for index, statement := range block.Statements {
		value, produced, err := lowerer.lowerStatement(statement, region)
		if err != nil {
			return optir.Value{}, err
		}
		if produced {
			last = value
		}
		if wantResult && index == len(block.Statements)-1 {
			if _, isExpression := statement.(*ast.ExpressionStatement); !isExpression {
				last = lowerer.emitUnit(region, statementToken(statement))
			}
		}
	}
	if wantResult && last.ID == 0 {
		last = lowerer.emitUnit(region, block.Token)
	}
	return last, nil
}

func (lowerer *optIRLowerer) lowerStatement(statement ast.Statement, region *optir.Region) (optir.Value, bool, error) {
	switch current := statement.(type) {
	case *ast.ExpressionStatement:
		value, err := lowerer.lowerExpression(current.Expression, region)
		return value, true, err
	case *ast.VariableDeclaration:
		if current.Name == nil || current.Value == nil {
			return optir.Value{}, false, refuseOptIR(current.Token, "uninitialized or unnamed locals are outside the first OptIR subset")
		}
		value, err := lowerer.lowerExpression(current.Value, region)
		if err != nil {
			return optir.Value{}, false, err
		}
		lowerer.env[current.Name.Value] = value
		return optir.Value{}, false, nil
	case *ast.AssignmentStatement:
		if current.Name == nil {
			return optir.Value{}, false, refuseOptIR(current.Token, "assignment has no local name")
		}
		prior, exists := lowerer.env[current.Name.Value]
		if !exists {
			globalType, isGlobal := lowerer.memory.globals[current.Name.Value]
			if !isGlobal {
				return optir.Value{}, false, refuseOptIR(current.Token, "assignment to nonlocal %s is outside the first OptIR subset", current.Name.Value)
			}
			proof, checked := lowerer.tc.ScalarGlobalWriteProof(current.Token)
			if !checked || proof.Global != current.Name.Value || proof.Type != string(globalType) {
				return optir.Value{}, false, refuseOptIR(current.Token, "assignment to global %s has no exact checked scalar-memory authority", current.Name.Value)
			}
			value, err := lowerer.lowerExpression(current.Value, region)
			if err != nil {
				return optir.Value{}, false, err
			}
			if value.Type != globalType {
				return optir.Value{}, false, fmt.Errorf("compiler: OptIR global assignment %s changed checked type %s to %s", current.Name.Value, globalType, value.Type)
			}
			lowerer.emitGlobalStore(region, current.Name.Value, optir.RegionID(proof.RegionID), value, current.Token)
			return optir.Value{}, false, nil
		}
		value, err := lowerer.lowerExpression(current.Value, region)
		if err != nil {
			return optir.Value{}, false, err
		}
		if value.Type != prior.Type {
			return optir.Value{}, false, fmt.Errorf("compiler: OptIR assignment %s changed checked type %s to %s", current.Name.Value, prior.Type, value.Type)
		}
		lowerer.env[current.Name.Value] = value
		return optir.Value{}, false, nil
	case *ast.IfStatement:
		return optir.Value{}, false, lowerer.lowerIfStatement(current, region)
	case *ast.WhileStatement:
		return optir.Value{}, false, lowerer.lowerWhile(current, region)
	case *ast.BreakStatement:
		return optir.Value{}, false, refuseOptIR(current.Token, "break is not represented by the first structured loop subset")
	default:
		return optir.Value{}, false, refuseOptIR(statementToken(statement), "statement %T is outside the first OptIR subset", statement)
	}
}

func (lowerer *optIRLowerer) lowerExpression(expression ast.Expression, region *optir.Region) (optir.Value, error) {
	if expression == nil {
		return optir.Value{}, refuseOptIR(token.Token{}, "nil expression is outside OptIR")
	}
	sourceToken, positioned := ast.ExpressionToken(expression)
	if !positioned {
		return optir.Value{}, refuseOptIR(token.Token{}, "expression %T has no stable source identity", expression)
	}
	resultType, err := lowerer.expressionType(expression)
	if err != nil {
		return optir.Value{}, err
	}
	switch current := expression.(type) {
	case *ast.Identifier:
		value, exists := lowerer.env[current.Value]
		if !exists {
			globalType, isGlobal := lowerer.memory.globals[current.Value]
			if !isGlobal {
				return optir.Value{}, refuseOptIR(current.Token, "identifier %s is not a scalar local or checked global", current.Value)
			}
			if globalType != resultType {
				return optir.Value{}, fmt.Errorf("compiler: OptIR global %s has declared type %s, checked expression type %s", current.Value, globalType, resultType)
			}
			global, checked := lowerer.tc.ScalarGlobalRegion(current.Value)
			if !checked || global.Name != current.Value || global.Type != string(resultType) {
				return optir.Value{}, refuseOptIR(current.Token, "global %s has no exact checked scalar-memory authority", current.Value)
			}
			return lowerer.emitGlobalLoad(region, current.Value, optir.RegionID(global.ID), resultType, current.Token), nil
		}
		if value.Type != resultType {
			return optir.Value{}, fmt.Errorf("compiler: OptIR identifier %s has environment type %s, checked type %s", current.Value, value.Type, resultType)
		}
		return value, nil
	case *ast.IntegerLiteral:
		spelling := strconv.FormatInt(current.Value, 10)
		if current.Wide {
			spelling = strconv.FormatUint(current.Magnitude(), 10)
		}
		return lowerer.emit(region, optir.OpConstInt, resultType, "integer", sourceToken, nil, nil, []optir.Attribute{{Name: optir.AttributeValue, Value: spelling}}), nil
	case *ast.Boolean:
		return lowerer.emit(region, optir.OpConstBool, resultType, "boolean", sourceToken, nil, nil, []optir.Attribute{{Name: optir.AttributeValue, Value: strconv.FormatBool(current.Value)}}), nil
	case *ast.PrefixExpression:
		operand, err := lowerer.lowerExpression(current.Right, region)
		if err != nil {
			return optir.Value{}, err
		}
		code := ""
		switch current.Operator {
		case "!":
			code = optir.OpBoolNot
		case "-":
			code = optir.OpIntNeg
		default:
			return optir.Value{}, refuseOptIR(current.Token, "prefix operator %s is outside the first OptIR subset", current.Operator)
		}
		if operand.Type != resultType {
			return optir.Value{}, refuseOptIR(current.Token, "prefix operator %s changes scalar type %s to %s", current.Operator, operand.Type, resultType)
		}
		return lowerer.emit(region, code, resultType, "prefix", current.Token, []optir.ValueID{operand.ID}, nil, nil), nil
	case *ast.InfixExpression:
		return lowerer.lowerInfix(current, resultType, region)
	case *ast.InvocationExpression:
		return lowerer.lowerCall(current, resultType, region)
	case *ast.BlockExpression:
		return lowerer.lowerBlock(current.Block, region, true, true)
	case *ast.MatchExpression:
		return lowerer.lowerBooleanMatch(current, resultType, region)
	default:
		return optir.Value{}, refuseOptIR(sourceToken, "expression %T is outside the first OptIR subset", expression)
	}
}

func (lowerer *optIRLowerer) expressionType(expression ast.Expression) (optir.Type, error) {
	tok, positioned := ast.ExpressionToken(expression)
	if !positioned {
		return "", refuseOptIR(token.Token{}, "expression %T has no checked position", expression)
	}
	typ, checked := lowerer.tc.ExpressionTypeAt(tok)
	if !checked {
		return "", refuseOptIR(tok, "expression %T has no checked type", expression)
	}
	result, supported := checkedOptIRType(lowerer.tc, typ)
	if !supported {
		return "", refuseOptIR(tok, "expression type %s is outside the scalar OptIR subset", typ)
	}
	return result, nil
}

func (lowerer *optIRLowerer) lowerInfix(expression *ast.InfixExpression, resultType optir.Type, region *optir.Region) (optir.Value, error) {
	if expression.Operator == "&&" || expression.Operator == "||" {
		return lowerer.lowerShortCircuit(expression, region)
	}
	left, err := lowerer.lowerExpression(expression.Left, region)
	if err != nil {
		return optir.Value{}, err
	}
	right, err := lowerer.lowerExpression(expression.Right, region)
	if err != nil {
		return optir.Value{}, err
	}
	code := map[string]string{
		"+": optir.OpIntAdd, "-": optir.OpIntSub, "*": optir.OpIntMul, "/": optir.OpIntDiv, "%": optir.OpIntRem,
		"&": optir.OpIntAnd, "|": optir.OpIntOr, "^": optir.OpIntXor, "<<": optir.OpIntShl, ">>": optir.OpIntShr,
		"==": optir.OpEqual, "!=": optir.OpNotEqual, "<": optir.OpLess, "<=": optir.OpLessEqual, ">": optir.OpGreater, ">=": optir.OpGreaterEqual,
	}[expression.Operator]
	if code == "" {
		return optir.Value{}, refuseOptIR(expression.Token, "infix operator %s is outside the first OptIR subset", expression.Operator)
	}
	comparison := code == optir.OpEqual || code == optir.OpNotEqual || code == optir.OpLess || code == optir.OpLessEqual || code == optir.OpGreater || code == optir.OpGreaterEqual
	if left.Type != right.Type || (!comparison && left.Type != resultType) || (comparison && resultType != optir.TypeBool) {
		return optir.Value{}, refuseOptIR(expression.Token, "operator %s has unsupported mixed scalar types %s, %s -> %s", expression.Operator, left.Type, right.Type, resultType)
	}
	var effects []optir.Effect
	if code == optir.OpIntDiv || code == optir.OpIntRem || code == optir.OpIntShl || code == optir.OpIntShr {
		effects = []optir.Effect{optir.EffectTrap}
	}
	return lowerer.emit(region, code, resultType, "infix", expression.Token, []optir.ValueID{left.ID, right.ID}, effects, nil), nil
}

func (lowerer *optIRLowerer) lowerShortCircuit(expression *ast.InfixExpression, region *optir.Region) (optir.Value, error) {
	condition, err := lowerer.lowerExpression(expression.Left, region)
	if err != nil {
		return optir.Value{}, err
	}
	if condition.Type != optir.TypeBool {
		return optir.Value{}, refuseOptIR(expression.Token, "short-circuit condition is not Bool")
	}
	thenLowerer, elseLowerer := lowerer.clone(), lowerer.clone()
	thenRegion, elseRegion := optir.Region{}, optir.Region{}
	var thenValue, elseValue optir.Value
	if expression.Operator == "&&" {
		thenValue, err = thenLowerer.lowerExpression(expression.Right, &thenRegion)
		elseValue = elseLowerer.emitBool(&elseRegion, false, expression.Token)
	} else {
		thenValue = thenLowerer.emitBool(&thenRegion, true, expression.Token)
		elseValue, err = elseLowerer.lowerExpression(expression.Right, &elseRegion)
	}
	if err != nil {
		return optir.Value{}, err
	}
	return lowerer.finishConditional(condition, thenValue, elseValue, thenLowerer, elseLowerer, thenRegion, elseRegion, expression.Token, region)
}

func (lowerer *optIRLowerer) lowerCall(call *ast.InvocationExpression, resultType optir.Type, region *optir.Region) (optir.Value, error) {
	callee, named := call.Function.(*ast.Identifier)
	if !named || call.ResolvedMethod != "" {
		return optir.Value{}, refuseOptIR(call.Token, "indirect and method calls are outside the first OptIR subset")
	}
	if lowerer.tc.FixedWidthName(callee.Value) != "" {
		if len(call.Arguments) != 1 {
			return optir.Value{}, refuseOptIR(call.Token, "integer construction requires one scalar operand")
		}
		if _, ok := optIRIntegerType(resultType); !ok {
			return optir.Value{}, refuseOptIR(call.Token, "integer constructor %s has non-integer result %s", callee.Value, resultType)
		}
		// The typechecker handles a constructor's literal directly while
		// checking its fit, so that child intentionally has no separate
		// expression-type record. The constructor's checked result supplies
		// the exact OptIR type.
		if literal, isLiteral := call.Arguments[0].(*ast.IntegerLiteral); isLiteral {
			spelling := strconv.FormatInt(literal.Value, 10)
			if literal.Wide {
				spelling = strconv.FormatUint(literal.Magnitude(), 10)
			}
			return lowerer.emit(region, optir.OpConstInt, resultType, "integer", literal.Token, nil, nil, []optir.Attribute{{Name: optir.AttributeValue, Value: spelling}}), nil
		}
		operand, err := lowerer.lowerExpression(call.Arguments[0], region)
		if err != nil {
			return optir.Value{}, err
		}
		if _, ok := optIRIntegerType(operand.Type); !ok {
			return optir.Value{}, refuseOptIR(call.Token, "integer constructor %s has non-integer operand %s", callee.Value, operand.Type)
		}
		return lowerer.emit(region, optir.OpCastInt, resultType, "cast", call.Token, []optir.ValueID{operand.ID}, nil, nil), nil
	}
	operands := make([]optir.ValueID, 0, len(call.Arguments))
	for _, argument := range call.Arguments {
		value, err := lowerer.lowerExpression(argument, region)
		if err != nil {
			return optir.Value{}, err
		}
		operands = append(operands, value.ID)
	}
	var callID string
	if lowerer.memory.authorizeCall == nil {
		lowerer.memory.unsummarizedCall = true
	} else {
		summary, err := lowerer.memory.authorizeCall(callee.Value)
		if err != nil {
			var unsupported *optIRUnsupported
			if errors.As(err, &unsupported) {
				return optir.Value{}, refuseOptIR(call.Token, "call to %s has no checked call-effect summary: %s", callee.Value, unsupported.reason)
			}
			return optir.Value{}, err
		}
		record, err := optir.NewCheckedMemoryCallRecordWithAccesses(optIRSource(call.Token), callee.Value, summary.Fingerprint(), summary.Accesses())
		if err != nil {
			return optir.Value{}, fmt.Errorf("compiler: checked memory call to %s: %w", callee.Value, err)
		}
		if _, duplicate := lowerer.memory.callRecords[record.ID]; duplicate {
			return optir.Value{}, fmt.Errorf("compiler: checked memory call %s is emitted more than once", record.ID)
		}
		lowerer.memory.callRecords[record.ID] = record
		callID = record.ID
	}
	result := lowerer.ids.value(resultType, "call", optIRSource(call.Token))
	operation := &optir.Operation{
		Code: optir.OpCall, Results: []optir.Value{result}, Operands: operands,
		Effects:    []optir.Effect{optir.EffectCall},
		Attributes: []optir.Attribute{{Name: optir.AttributeCallee, Value: callee.Value}},
		Facts:      lowerer.checkedTypeFact(call.Token, result), Source: optIRSource(call.Token), MemoryCallID: callID,
	}
	region.Nodes = append(region.Nodes, optir.Node{Operation: operation})
	return result, nil
}

func (lowerer *optIRLowerer) lowerBooleanMatch(match *ast.MatchExpression, resultType optir.Type, region *optir.Region) (optir.Value, error) {
	condition, err := lowerer.lowerExpression(match.Scrutinee, region)
	if err != nil {
		return optir.Value{}, err
	}
	if condition.Type != optir.TypeBool {
		return optir.Value{}, refuseOptIR(match.Token, "only exhaustive Bool matches are in the first OptIR subset")
	}
	trueBody, falseBody, err := booleanMatchBodies(match)
	if err != nil {
		return optir.Value{}, err
	}
	thenLowerer, elseLowerer := lowerer.clone(), lowerer.clone()
	thenRegion, elseRegion := optir.Region{}, optir.Region{}
	thenValue, err := thenLowerer.lowerExpression(trueBody, &thenRegion)
	if err != nil {
		return optir.Value{}, err
	}
	elseValue, err := elseLowerer.lowerExpression(falseBody, &elseRegion)
	if err != nil {
		return optir.Value{}, err
	}
	if thenValue.Type != resultType || elseValue.Type != resultType {
		return optir.Value{}, fmt.Errorf("compiler: checked Bool match arms disagree with result %s", resultType)
	}
	return lowerer.finishConditional(condition, thenValue, elseValue, thenLowerer, elseLowerer, thenRegion, elseRegion, match.Token, region)
}

func booleanMatchBodies(match *ast.MatchExpression) (ast.Expression, ast.Expression, error) {
	var whenTrue, whenFalse, wildcard ast.Expression
	for _, arm := range match.Arms {
		if arm == nil || arm.Body == nil {
			return nil, nil, refuseOptIR(match.Token, "Bool match has an empty arm")
		}
		switch pattern := arm.Pattern.(type) {
		case *ast.LiteralPattern:
			literal, isBool := pattern.Value.(*ast.Boolean)
			if !isBool {
				return nil, nil, refuseOptIR(pattern.Token, "Bool match has a non-Bool literal pattern")
			}
			if literal.Value {
				if whenTrue != nil {
					return nil, nil, refuseOptIR(pattern.Token, "Bool match repeats true")
				}
				whenTrue = arm.Body
			} else {
				if whenFalse != nil {
					return nil, nil, refuseOptIR(pattern.Token, "Bool match repeats false")
				}
				whenFalse = arm.Body
			}
		case *ast.WildcardPattern:
			if wildcard != nil {
				return nil, nil, refuseOptIR(pattern.Token, "Bool match repeats wildcard")
			}
			wildcard = arm.Body
		default:
			return nil, nil, refuseOptIR(arm.Token, "Bool match pattern %T is outside the first OptIR subset", arm.Pattern)
		}
	}
	if wildcard != nil {
		if whenTrue == nil && whenFalse != nil {
			whenTrue = wildcard
		} else if whenFalse == nil && whenTrue != nil {
			whenFalse = wildcard
		} else {
			return nil, nil, refuseOptIR(match.Token, "Bool wildcard must complement exactly one literal arm")
		}
	}
	if whenTrue == nil || whenFalse == nil {
		return nil, nil, refuseOptIR(match.Token, "Bool match is not exactly exhaustive")
	}
	return whenTrue, whenFalse, nil
}

func (lowerer *optIRLowerer) lowerIfStatement(statement *ast.IfStatement, region *optir.Region) error {
	condition, err := lowerer.lowerExpression(statement.Condition, region)
	if err != nil {
		return err
	}
	if condition.Type != optir.TypeBool || statement.Consequence == nil {
		return refuseOptIR(statement.Token, "if requires a Bool condition and consequence")
	}
	thenLowerer, elseLowerer := lowerer.clone(), lowerer.clone()
	thenRegion, elseRegion := optir.Region{}, optir.Region{}
	if _, err := thenLowerer.lowerBlock(statement.Consequence, &thenRegion, false, true); err != nil {
		return err
	}
	if statement.Alternative != nil {
		switch alternative := statement.Alternative.(type) {
		case *ast.BlockStatement:
			if _, err := elseLowerer.lowerBlock(alternative, &elseRegion, false, true); err != nil {
				return err
			}
		case *ast.IfStatement:
			if err := elseLowerer.lowerIfStatement(alternative, &elseRegion); err != nil {
				return err
			}
		default:
			return refuseOptIR(statement.Token, "if alternative %T is outside the first OptIR subset", statement.Alternative)
		}
	}
	thenYield, elseYield, results, err := lowerer.mergeEnvironments(thenLowerer, elseLowerer, statement.Token)
	if err != nil {
		return err
	}
	thenRegion.Yield = thenYield
	elseRegion.Yield = elseYield
	region.Nodes = append(region.Nodes, optir.Node{If: &optir.If{Condition: condition.ID, Results: results, Then: thenRegion, Else: elseRegion}})
	return nil
}

func (lowerer *optIRLowerer) finishConditional(condition, thenValue, elseValue optir.Value, thenLowerer, elseLowerer *optIRLowerer, thenRegion, elseRegion optir.Region, tok token.Token, region *optir.Region) (optir.Value, error) {
	if thenValue.Type != elseValue.Type {
		return optir.Value{}, fmt.Errorf("compiler: OptIR conditional arm types differ: %s and %s", thenValue.Type, elseValue.Type)
	}
	result := lowerer.ids.value(thenValue.Type, "if.result", optIRSource(tok))
	thenRegion.Yield = append(thenRegion.Yield, thenValue.ID)
	elseRegion.Yield = append(elseRegion.Yield, elseValue.ID)
	thenEnvironment, elseEnvironment, environmentResults, err := lowerer.mergeEnvironments(thenLowerer, elseLowerer, tok)
	if err != nil {
		return optir.Value{}, err
	}
	thenRegion.Yield = append(thenRegion.Yield, thenEnvironment...)
	elseRegion.Yield = append(elseRegion.Yield, elseEnvironment...)
	results := append([]optir.Value{result}, environmentResults...)
	region.Nodes = append(region.Nodes, optir.Node{If: &optir.If{Condition: condition.ID, Results: results, Then: thenRegion, Else: elseRegion}})
	return result, nil
}

func (lowerer *optIRLowerer) mergeEnvironments(thenLowerer, elseLowerer *optIRLowerer, tok token.Token) ([]optir.ValueID, []optir.ValueID, []optir.Value, error) {
	names := make([]string, 0, len(lowerer.env))
	for name := range lowerer.env {
		names = append(names, name)
	}
	sort.Strings(names)
	var thenYield, elseYield []optir.ValueID
	var results []optir.Value
	for _, name := range names {
		incoming := lowerer.env[name]
		thenValue, thenExists := thenLowerer.env[name]
		elseValue, elseExists := elseLowerer.env[name]
		if !thenExists || !elseExists {
			return nil, nil, nil, fmt.Errorf("compiler: OptIR conditional lost checked local %s", name)
		}
		if thenValue.ID == elseValue.ID {
			lowerer.env[name] = thenValue
			continue
		}
		if thenValue.Type != incoming.Type || elseValue.Type != incoming.Type {
			return nil, nil, nil, fmt.Errorf("compiler: OptIR conditional changed checked local %s from %s to %s/%s", name, incoming.Type, thenValue.Type, elseValue.Type)
		}
		result := lowerer.ids.value(incoming.Type, name, optIRSource(tok))
		thenYield = append(thenYield, thenValue.ID)
		elseYield = append(elseYield, elseValue.ID)
		results = append(results, result)
		lowerer.env[name] = result
	}
	return thenYield, elseYield, results, nil
}

func (lowerer *optIRLowerer) lowerWhile(loop *ast.WhileStatement, region *optir.Region) error {
	carriedNames := assignedOuterNames(loop.Body, lowerer.env)
	carried := make(map[string]int, len(carriedNames))
	initial := make([]optir.ValueID, len(carriedNames))
	results := make([]optir.Value, len(carriedNames))
	conditionArguments := make([]optir.Value, len(carriedNames))
	bodyArguments := make([]optir.Value, len(carriedNames))
	conditionLowerer, bodyLowerer := lowerer.clone(), lowerer.clone()
	for index, name := range carriedNames {
		carried[name] = index
		current := lowerer.env[name]
		initial[index] = current.ID
		results[index] = lowerer.ids.value(current.Type, name, optIRSource(loop.Token))
		conditionArguments[index] = lowerer.ids.value(current.Type, name+".condition", current.Source)
		bodyArguments[index] = lowerer.ids.value(current.Type, name+".body", current.Source)
		conditionLowerer.env[name] = conditionArguments[index]
		bodyLowerer.env[name] = bodyArguments[index]
	}
	conditionRegion := optir.Region{Arguments: conditionArguments}
	condition, err := conditionLowerer.lowerExpression(loop.Condition, &conditionRegion)
	if err != nil {
		return err
	}
	if condition.Type != optir.TypeBool {
		return refuseOptIR(loop.Token, "while condition is not Bool")
	}
	for name, before := range conditionLowerer.env {
		if original, exists := lowerer.env[name]; exists {
			expected := original.ID
			if index, isCarried := carried[name]; isCarried {
				expected = conditionArguments[index].ID
			}
			if before.ID != expected {
				return refuseOptIR(loop.Token, "while conditions that assign outer locals are outside the first OptIR subset")
			}
		}
	}
	conditionRegion.Yield = []optir.ValueID{condition.ID}
	bodyRegion := optir.Region{Arguments: bodyArguments}
	if _, err := bodyLowerer.lowerBlock(loop.Body, &bodyRegion, false, true); err != nil {
		return err
	}
	for name, original := range lowerer.env {
		bodyValue, exists := bodyLowerer.env[name]
		if !exists {
			return fmt.Errorf("compiler: OptIR while body lost checked local %s", name)
		}
		if _, isCarried := carried[name]; !isCarried && bodyValue.ID != original.ID {
			return refuseOptIR(loop.Token, "while body mutates outer local %s through an unsupported expression shape", name)
		}
	}
	for _, name := range carriedNames {
		bodyValue, exists := bodyLowerer.env[name]
		if !exists {
			return fmt.Errorf("compiler: OptIR while body lost loop-carried local %s", name)
		}
		bodyRegion.Yield = append(bodyRegion.Yield, bodyValue.ID)
	}
	region.Nodes = append(region.Nodes, optir.Node{While: &optir.While{Initial: initial, Results: results, Condition: conditionRegion, Body: bodyRegion}})
	for index, name := range carriedNames {
		lowerer.env[name] = results[index]
	}
	return nil
}

func assignedOuterNames(block *ast.BlockStatement, environment map[string]optir.Value) []string {
	assigned := map[string]bool{}
	var walkBlock func(*ast.BlockStatement)
	var walkStatement func(ast.Statement)
	walkBlock = func(current *ast.BlockStatement) {
		if current == nil {
			return
		}
		for _, statement := range current.Statements {
			walkStatement(statement)
		}
	}
	walkStatement = func(statement ast.Statement) {
		switch current := statement.(type) {
		case *ast.AssignmentStatement:
			if current.Name != nil {
				if _, exists := environment[current.Name.Value]; exists {
					assigned[current.Name.Value] = true
				}
			}
		case *ast.IfStatement:
			walkBlock(current.Consequence)
			switch alternative := current.Alternative.(type) {
			case *ast.BlockStatement:
				walkBlock(alternative)
			case *ast.IfStatement:
				walkStatement(alternative)
			}
		case *ast.WhileStatement:
			walkBlock(current.Body)
		}
	}
	walkBlock(block)
	names := make([]string, 0, len(assigned))
	for name := range assigned {
		names = append(names, name)
	}
	sort.Strings(names)
	return names
}

func (lowerer *optIRLowerer) emit(region *optir.Region, code string, typ optir.Type, name string, tok token.Token, operands []optir.ValueID, effects []optir.Effect, attributes []optir.Attribute) optir.Value {
	result := lowerer.ids.value(typ, name, optIRSource(tok))
	facts := lowerer.checkedTypeFact(tok, result)
	operation := &optir.Operation{
		Code:       code,
		Results:    []optir.Value{result},
		Operands:   append([]optir.ValueID(nil), operands...),
		Effects:    append([]optir.Effect(nil), effects...),
		Attributes: append([]optir.Attribute(nil), attributes...),
		Facts:      facts,
		Source:     optIRSource(tok),
	}
	region.Nodes = append(region.Nodes, optir.Node{Operation: operation})
	return result
}

func (lowerer *optIRLowerer) emitGlobalLoad(region *optir.Region, name string, regionID optir.RegionID, typ optir.Type, tok token.Token) optir.Value {
	result := lowerer.ids.value(typ, name+".load", optIRSource(tok))
	record := lowerer.checkedMemoryAccess(name, regionID, typ, optir.MemoryRead, false, tok)
	operation := &optir.Operation{
		Code: optir.OpLoadRegion, Results: []optir.Value{result},
		Effects: []optir.Effect{optir.EffectReadMemory}, Facts: lowerer.checkedTypeFact(tok, result),
		Source: optIRSource(tok), MemoryAccessID: record.ID,
	}
	region.Nodes = append(region.Nodes, optir.Node{Operation: operation})
	return result
}

func (lowerer *optIRLowerer) emitGlobalStore(region *optir.Region, name string, regionID optir.RegionID, value optir.Value, tok token.Token) {
	record := lowerer.checkedMemoryAccess(name, regionID, value.Type, optir.MemoryWrite, true, tok)
	operation := &optir.Operation{
		Code: optir.OpStoreRegion, Operands: []optir.ValueID{value.ID},
		Effects: []optir.Effect{optir.EffectWriteMemory}, Source: optIRSource(tok), MemoryAccessID: record.ID,
	}
	region.Nodes = append(region.Nodes, optir.Node{Operation: operation})
}

func (lowerer *optIRLowerer) checkedMemoryAccess(name string, regionID optir.RegionID, typ optir.Type, kind optir.MemoryAccessKind, whole bool, tok token.Token) optir.CheckedMemoryAccessRecord {
	if lowerer.memory == nil || lowerer.memory.err != nil {
		return optir.CheckedMemoryAccessRecord{}
	}
	declared, exists := lowerer.memory.globals[name]
	if !exists || declared != typ {
		lowerer.memory.err = fmt.Errorf("compiler: checked memory access to global %s has type %s, want %s", name, typ, declared)
		return optir.CheckedMemoryAccessRecord{}
	}
	if regionID == "" {
		lowerer.memory.err = fmt.Errorf("compiler: checked memory access to global %s has no region identity", name)
		return optir.CheckedMemoryAccessRecord{}
	}
	record, err := optir.NewCheckedMemoryAccessRecord(optIRSource(tok), regionID, kind, typ, whole, false)
	if err != nil {
		lowerer.memory.err = fmt.Errorf("compiler: checked memory access to global %s: %w", name, err)
		return optir.CheckedMemoryAccessRecord{}
	}
	if _, duplicate := lowerer.memory.records[record.ID]; duplicate {
		lowerer.memory.err = fmt.Errorf("compiler: checked memory access %s is emitted more than once", record.ID)
		return optir.CheckedMemoryAccessRecord{}
	}
	lowerer.memory.records[record.ID] = record
	return record
}

func (lowerer *optIRLowerer) checkedTypeFact(tok token.Token, result optir.Value) []optir.Fact {
	if lowerer.tc == nil || lowerer.facts == nil || lowerer.facts.err != nil {
		return nil
	}
	proof, exists := lowerer.tc.ExpressionTypeProof(tok)
	if !exists {
		return nil
	}
	checked, exists := lowerer.tc.ExpressionTypeAt(tok)
	if !exists || checked == nil {
		lowerer.facts.err = fmt.Errorf("compiler: checked type proof %s has no expression type authority", proof.ID)
		return nil
	}
	canonical, supported := checkedOptIRType(lowerer.tc, checked)
	if !supported || canonical != result.Type {
		lowerer.facts.err = fmt.Errorf("compiler: checked type proof %s has type %s, OptIR value %d has type %s", proof.ID, checked, result.ID, result.Type)
		return nil
	}
	record := optir.CheckedFactRecord{
		ID: proof.ID, Name: proof.Proposition, ValueType: canonical,
		Provenance: proof.Provenance, Witness: proof.Witness, Scope: proof.Scope,
		Dependencies: append([]string(nil), proof.Dependencies...),
	}
	if prior, duplicate := lowerer.facts.values[proof.ID]; duplicate && prior != result.ID {
		lowerer.facts.err = fmt.Errorf("compiler: checked type proof %s is bound to both OptIR values %d and %d", proof.ID, prior, result.ID)
		return nil
	}
	lowerer.facts.values[proof.ID] = result.ID
	lowerer.facts.records[proof.ID] = record
	return []optir.Fact{{
		ID: proof.ID, Name: proof.Proposition, Values: []optir.ValueID{result.ID},
		Provenance: proof.Provenance, Witness: proof.Witness, Scope: proof.Scope,
		Dependencies: append([]string(nil), proof.Dependencies...),
	}}
}

func verifyOptIRAnalysisFacts(authority optir.CheckedFactAuthority, analyses optIRAnalysisArtifacts) error {
	candidates := []optir.CFG{analyses.sccpSimplified, analyses.simplified, analyses.loopInvariant}
	if analyses.hasMemory {
		candidates = append(candidates, analyses.deadStores, analyses.regionLoads,
			analyses.memoryCleanup.SCCPSimplified, analyses.memoryCleanup.ScalarCFG,
			analyses.memoryCleanup.DeadStores, analyses.memoryCleanup.CFG)
	}
	for _, cfg := range candidates {
		if err := optir.VerifyCFGCheckedFacts(cfg, authority); err != nil {
			return err
		}
	}
	return nil
}

func (lowerer *optIRLowerer) emitBool(region *optir.Region, value bool, tok token.Token) optir.Value {
	return lowerer.emit(region, optir.OpConstBool, optir.TypeBool, "boolean", tok, nil, nil, []optir.Attribute{{Name: optir.AttributeValue, Value: strconv.FormatBool(value)}})
}

func (lowerer *optIRLowerer) emitUnit(region *optir.Region, tok token.Token) optir.Value {
	return lowerer.emit(region, optir.OpConstUnit, optir.Type("()"), "unit", tok, nil, nil, nil)
}

func optIRIntegerType(typ optir.Type) (int, bool) {
	name := string(typ)
	if len(name) < 2 || (name[0] != 'i' && name[0] != 'u') {
		return 0, false
	}
	width, err := strconv.Atoi(name[1:])
	if err != nil || (width != 8 && width != 16 && width != 32 && width != 64 && width != 128) {
		return 0, false
	}
	return width, true
}

func optIRSource(tok token.Token) optir.Source {
	return optir.Source{Context: tok.SemanticContext, Line: tok.Line, Column: tok.Column}
}

func refuseOptIR(tok token.Token, format string, arguments ...any) error {
	return &optIRUnsupported{reason: fmt.Sprintf(format, arguments...), source: optIRSource(tok)}
}

func statementToken(statement ast.Statement) token.Token {
	switch current := statement.(type) {
	case *ast.ExpressionStatement:
		return current.Token
	case *ast.VariableDeclaration:
		return current.Token
	case *ast.AssignmentStatement:
		return current.Token
	case *ast.IfStatement:
		return current.Token
	case *ast.WhileStatement:
		return current.Token
	case *ast.BreakStatement:
		return current.Token
	}
	return token.Token{}
}
