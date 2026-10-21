package compiler

// The explicit raw profile reuses the ordinary checked lowerer and Project,
// but cannot enter the optimization graph or any target candidate selector.
// Admission below checks logical typing/authority, not frontend correctness or
// semantic refinement; the exported graph is the input to that separate proof.

import (
	"fmt"
	"reflect"
	"sort"
	"strings"

	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/modules"
	"github.com/SCKelemen/oak/optir"
	"github.com/SCKelemen/oak/stdlib"
	"github.com/SCKelemen/oak/token"
	"github.com/SCKelemen/oak/typechecker"
)

type StatefulIndexProof struct {
	AccessID string
	Proof    typechecker.IndexProof
}

// CheckedStatefulOptIR is an owned raw projection, never an optimized artifact.
// Parsed Oak source-file bytes are retained rather than replaced by a digest.
// Sources does not retain original oak.mod bytes or attest a complete module
// manifest. Package resolution and checked source -> exported data remain
// tested trust boundaries.
type CheckedStatefulOptIR struct {
	program optir.StatefulProgram
	sources []PackageSource
	proofs  []StatefulIndexProof
}

func (a CheckedStatefulOptIR) Program() optir.StatefulProgram { return a.program }
func (a CheckedStatefulOptIR) Sources() []PackageSource {
	return append([]PackageSource(nil), a.sources...)
}
func (a CheckedStatefulOptIR) IndexProofs() []StatefulIndexProof {
	out := append([]StatefulIndexProof(nil), a.proofs...)
	for i := range out {
		out[i].Proof.Dependencies = append([]string(nil), out[i].Proof.Dependencies...)
	}
	return out
}

// StatefulCopyOptIR admits only the named frozen raw two-function closure.
// Compilation.OptIR, scalar Wasm and native selection are deliberately unchanged.
func (comp Compilation) StatefulCopyOptIR() Stage[CheckedStatefulOptIR] {
	return comp.Check().Then(func(model *SemanticModel) (CheckedStatefulOptIR, error) {
		if len(comp.syntaxRewrites) != 0 {
			return CheckedStatefulOptIR{}, fmt.Errorf("compiler: stateful raw profile refuses external syntax rewrites")
		}
		return lowerStatefulCopyOptIR(model)
	})
}

type optIRStatefulLowering struct {
	tc       *typechecker.TypeChecker
	name     string
	types    map[optir.Type]optir.StatefulTypeRecord
	accesses []optir.ByteAccessRecord
	calls    []optir.StatefulCallRecord
	proofs   []StatefulIndexProof
	formals  map[optir.ValueID]int
}

func (lowerer *optIRLowerer) checkedType(t typechecker.Type) (optir.Type, bool) {
	if lowerer.stateful != nil {
		return lowerer.stateful.checkedType(t)
	}
	return checkedOptIRType(lowerer.tc, t)
}
func (s *optIRStatefulLowering) checkedType(t typechecker.Type) (optir.Type, bool) {
	if typ, ok := checkedOptIRType(s.tc, t); ok {
		_, present := s.types[typ]
		return typ, present
	}
	switch t := t.(type) {
	case *typechecker.ArrayType:
		element, ok := checkedOptIRType(s.tc, t.ElementType)
		if !ok || element != "u8" || t.Align != 0 || t.Length != -1 || t.IsSlice == t.IsSpan {
			return "", false
		}
		if t.IsSpan {
			return optir.TypeByteSpan, true
		}
		return optir.TypeByteView, true
	case *typechecker.ADTType:
		_, ok := s.types[optir.Type(t.Name)]
		return optir.Type(t.Name), ok && t.Name == string(optir.TypeCopyError)
	case *typechecker.GenericType:
		if t.Name != "Result" || len(t.TypeArgs) != 2 {
			return "", false
		}
		left, lok := s.checkedType(t.TypeArgs[0])
		right, rok := s.checkedType(t.TypeArgs[1])
		return optir.TypeCopyResult, lok && rok && left == "u32" && right == optir.TypeCopyError
	case *typechecker.NarrowedADTVariantType:
		parent, ok := s.checkedType(&typechecker.GenericType{Name: t.ADTName, TypeArgs: t.TypeArgs})
		if len(t.TypeArgs) == 0 {
			parent, ok = s.checkedType(&typechecker.ADTType{Name: t.ADTName})
		}
		if !ok {
			return "", false
		}
		for _, v := range s.types[parent].Constructors {
			if v.Name == t.VariantName {
				return parent, true
			}
		}
	}
	return "", false
}

func lowerStatefulCopyOptIR(model *SemanticModel) (CheckedStatefulOptIR, error) {
	if model == nil || model.Tree == nil || model.Tree.Root == nil || model.TypeChecker == nil || model.Tree.Modules == nil {
		return CheckedStatefulOptIR{}, fmt.Errorf("compiler: stateful raw profile requires an ordinary checked package")
	}
	info := model.Tree.Modules
	if model.Tree.Prelude != "core" || !info.StandardLibrary["bytes"] || len(info.Packages) != 2 || len(info.NestedModules) != 0 || len(info.Abstract) != 0 || len(info.Links) != 0 || len(info.AsmUnits) != 0 || !reflect.DeepEqual(info.Imports[info.RootPackage], []string{"bytes"}) {
		return CheckedStatefulOptIR{}, fmt.Errorf("compiler: stateful raw profile requires the exact root/stdlib-bytes dependency closure")
	}
	for name, kind := range map[string]modules.MemberKind{"copy_into": modules.KindValue, "CopyError": modules.KindType} {
		member, outcome := modules.Lookup(info.Exports["bytes"], nil, name)
		if outcome != modules.Resolved || member.Kind != kind {
			return CheckedStatefulOptIR{}, fmt.Errorf("compiler: stateful raw dependency member bytes.%s did not resolve", name)
		}
	}
	functions := map[string]*ast.FunctionStatement{}
	templates := map[string]*ast.ADTType{}
	adts := map[string]*ast.ADTType{}
	for _, statement := range model.Tree.Root.Statements {
		switch n := statement.(type) {
		case *ast.FunctionStatement:
			if n.Name.Value == "len" {
				return CheckedStatefulOptIR{}, refuseOptIR(n.Token, "raw descriptor length refuses a shadowed builtin binding")
			}
			functions[n.Name.Value] = n
		case *ast.VariableDeclaration:
			return CheckedStatefulOptIR{}, refuseOptIR(n.Token, "raw stateful closure refuses package value declarations and initialization")
		case *ast.ADTType:
			if len(n.TypeParams) > 0 {
				templates[n.Name.Value] = n
			} else {
				adts[n.Name.Value] = n
			}
		case *ast.PackageStatement, *ast.ImportStatement:
			// Original package/type declarations remain source authority, not
			// executable initialization or extra reachable functions.
		default:
			return CheckedStatefulOptIR{}, refuseOptIR(statementToken(statement), "top-level %T is outside the raw stateful closure", statement)
		}
	}
	// Same specialization routine as native lowering, using recorded checker
	// instantiations; no fabricated monomorphic Result declaration.
	specializeInstantiations(model.TypeChecker, templates, map[string]*ast.RecordLiteral{}, adts)
	result := adts[string(optir.TypeCopyResult)]
	copyError := adts[string(optir.TypeCopyError)]
	if result == nil || copyError == nil || templates["Result"] == nil {
		return CheckedStatefulOptIR{}, fmt.Errorf("compiler: missing checked concrete Result/CopyError declarations")
	}
	inventory := []optir.StatefulTypeRecord{}
	for _, typ := range []optir.Type{"u8", "u32", optir.TypeBool, "()"} {
		inventory = append(inventory, optir.StatefulTypeRecord{Type: typ, Kind: "scalar"})
	}
	inventory = append(inventory, optir.StatefulTypeRecord{Type: optir.TypeByteView, Kind: "descriptor-read", TypeArguments: []optir.Type{"u8"}}, optir.StatefulTypeRecord{Type: optir.TypeByteSpan, Kind: "descriptor-write", TypeArguments: []optir.Type{"u8"}})
	for _, decl := range []*ast.ADTType{copyError, result} {
		record := optir.StatefulTypeRecord{Type: optir.Type(decl.Name.Value), Kind: "adt", Declaration: optIRSource(decl.Token), Template: decl.Name.Value}
		if decl == result {
			record.Template = "Result"
			record.TypeArguments = []optir.Type{"u32", optir.TypeCopyError}
		}
		if len(decl.TagValues) != 0 {
			return CheckedStatefulOptIR{}, fmt.Errorf("compiler: raw stateful ADTs refuse explicit tag encoding")
		}
		for _, variant := range decl.Variants {
			if variant == nil || variant.Name == nil || variant.Literal != nil || variant.Result != nil {
				return CheckedStatefulOptIR{}, fmt.Errorf("compiler: stateful ADT has unsupported constructor shape")
			}
			constructor := optir.StatefulConstructor{Name: variant.Name.Value, Declaration: optIRSource(variant.Token)}
			if variant.Payload != nil {
				ident, ok := variant.Payload.(*ast.Identifier)
				if !ok {
					return CheckedStatefulOptIR{}, fmt.Errorf("compiler: stateful constructor payload is not a checked atom")
				}
				constructor.Payload = []optir.Type{optir.Type(ident.Value)}
			}
			record.Constructors = append(record.Constructors, constructor)
		}
		inventory = append(inventory, record)
	}
	types := map[optir.Type]optir.StatefulTypeRecord{}
	for _, typ := range inventory {
		types[typ.Type] = typ
	}
	var lowered []optir.StatefulFunction
	var accesses []optir.ByteAccessRecord
	var calls []optir.StatefulCallRecord
	var proofs []StatefulIndexProof
	for _, name := range []string{"copy_checked", modules.Mangle("bytes", "copy_into")} {
		function := functions[name]
		if function == nil || function.Body == nil || function.ExternSymbol != "" || function.AsmBacked || function.Receiver != nil || len(function.TypeParams) != 0 || len(function.Dispatch) != 0 {
			return CheckedStatefulOptIR{}, fmt.Errorf("compiler: stateful raw closure lacks concrete internal function %s", name)
		}
		stateful := &optIRStatefulLowering{tc: model.TypeChecker, name: name, types: types, formals: map[optir.ValueID]int{1: 0, 2: 1}}
		structured, facts, memory, err := lowerCheckedOptIRFunctionProfile(function, model.TypeChecker, nil, nil, stateful)
		if err != nil {
			return CheckedStatefulOptIR{}, err
		}
		if len(memory.Records()) != 0 || len(memory.CallRecords()) != 0 {
			return CheckedStatefulOptIR{}, fmt.Errorf("compiler: stateful raw projection leaked legacy whole-cell authority")
		}
		cfg, err := projectCheckedOptIRFunction(structured, memory)
		if err != nil {
			return CheckedStatefulOptIR{}, err
		}
		lowered = append(lowered, optir.StatefulFunction{Structured: structured, CFG: cfg, Facts: facts})
		accesses = append(accesses, stateful.accesses...)
		calls = append(calls, stateful.calls...)
		proofs = append(proofs, stateful.proofs...)
	}
	program, err := optir.NewStatefulProgram("copy_checked", lowered, inventory, accesses, calls)
	if err != nil {
		return CheckedStatefulOptIR{}, err
	}
	sources := append([]PackageSource(nil), info.Sources...)
	sources = append(sources, PackageSource{Package: "std", Path: "stdlib.oak", Text: stdlib.Prelude})
	sort.Slice(sources, func(i, j int) bool {
		if sources[i].Package != sources[j].Package {
			return sources[i].Package < sources[j].Package
		}
		return sources[i].Path < sources[j].Path
	})
	if err := verifyStatefulSourceInventory(program, sources); err != nil {
		return CheckedStatefulOptIR{}, err
	}
	return CheckedStatefulOptIR{program: program, sources: sources, proofs: proofs}, nil
}

func (lowerer *optIRLowerer) lowerStatefulCall(call *ast.InvocationExpression, resultType optir.Type, region *optir.Region) (optir.Value, error) {
	callee, ok := call.Function.(*ast.Identifier)
	if !ok || call.ResolvedMethod != "" {
		return optir.Value{}, refuseOptIR(call.Token, "stateful raw profile refuses indirect/method call")
	}
	var operands []optir.ValueID
	var types []optir.Type
	for _, arg := range call.Arguments {
		value, err := lowerer.lowerExpression(arg, region)
		if err != nil {
			return optir.Value{}, err
		}
		operands = append(operands, value.ID)
		types = append(types, value.Type)
	}
	if callee.Value == "len" {
		if _, shadowed := lowerer.env["len"]; shadowed {
			return optir.Value{}, refuseOptIR(call.Token, "raw descriptor length refuses a shadowed local/parameter builtin binding")
		}
		if len(types) != 1 || (types[0] != optir.TypeByteView && types[0] != optir.TypeByteSpan) || resultType != "u32" {
			return optir.Value{}, refuseOptIR(call.Token, "stateful len requires one checked byte descriptor")
		}
		return lowerer.emit(region, optir.OpDescriptorLen, resultType, "length", call.Token, operands, nil, nil), nil
	}
	if lowerer.stateful.name != "copy_checked" || callee.Value != "bytes__copy_uinto" || !reflect.DeepEqual(types, []optir.Type{optir.TypeByteSpan, optir.TypeByteView}) || resultType != optir.TypeCopyResult {
		return optir.Value{}, refuseOptIR(call.Token, "call is outside the exact stateful raw closure")
	}
	record, err := optir.NewStatefulCallRecord(optir.StatefulCallRecord{Function: lowerer.stateful.name, Source: optIRSource(call.Token), Callee: callee.Value, Operands: operands, Effects: []optir.StatefulFormalEffect{{Formal: 0, Kind: optir.MemoryWrite}, {Formal: 1, Kind: optir.MemoryRead}}})
	if err != nil {
		return optir.Value{}, err
	}
	result := lowerer.emit(region, optir.OpCall, resultType, "call", call.Token, operands, []optir.Effect{optir.EffectCall, optir.EffectReadMemory, optir.EffectWriteMemory, optir.EffectTrap}, []optir.Attribute{{Name: optir.AttributeCallee, Value: callee.Value}})
	region.Nodes[len(region.Nodes)-1].Operation.MemoryCallID = record.ID
	lowerer.stateful.calls = append(lowerer.stateful.calls, record)
	return result, nil
}
func (lowerer *optIRLowerer) statefulIndexOperands(index *ast.IndexExpression, region *optir.Region) (optir.Value, optir.Value, error) {
	if index == nil || index.Dot {
		return optir.Value{}, optir.Value{}, refuseOptIR(token.Token{}, "raw byte access requires bracket index")
	}
	descriptor, err := lowerer.lowerExpression(index.Left, region)
	if err != nil {
		return optir.Value{}, optir.Value{}, err
	}
	offset, err := lowerer.lowerExpression(index.Index, region)
	if err != nil {
		return optir.Value{}, optir.Value{}, err
	}
	return descriptor, offset, nil
}
func (lowerer *optIRLowerer) statefulAccess(index *ast.IndexExpression, descriptor, offset, value optir.Value, write bool, region *optir.Region) (optir.Value, error) {
	formal, ok := lowerer.stateful.formals[descriptor.ID]
	if !ok || offset.Type != "u32" || (descriptor.Type != optir.TypeByteSpan && descriptor.Type != optir.TypeByteView) || (write && (descriptor.Type != optir.TypeByteSpan || value.Type != "u8")) {
		return optir.Value{}, refuseOptIR(index.Token, "raw byte access lacks exact descriptor formal/index/value type")
	}
	kind := optir.MemoryRead
	code := optir.OpByteLoad
	effect := optir.EffectReadMemory
	operands := []optir.ValueID{descriptor.ID, offset.ID}
	record := optir.ByteAccessRecord{Function: lowerer.stateful.name, Source: optIRSource(index.Token), Formal: formal, Descriptor: descriptor.ID, Index: offset.ID, Kind: kind, Width: 1, Element: "u8", CheckPolicy: optir.StatefulBoundsTrap}
	proof, hasProof := lowerer.tc.IndexProof(index.Token)
	if hasProof {
		record.IndexProofID = proof.ID
	}
	if write {
		record.Kind = optir.MemoryWrite
		record.Value = value.ID
		code = optir.OpByteStore
		effect = optir.EffectWriteMemory
		operands = append(operands, value.ID)
	}
	record, err := optir.NewByteAccessRecord(record)
	if err != nil {
		return optir.Value{}, err
	}
	var result optir.Value
	if write {
		region.Nodes = append(region.Nodes, optir.Node{Operation: &optir.Operation{Code: code, Operands: operands, Effects: []optir.Effect{effect, optir.EffectTrap}, Source: optIRSource(index.Token), MemoryAccessID: record.ID}})
	} else {
		result = lowerer.emit(region, code, "u8", "byte", index.Token, operands, []optir.Effect{effect, optir.EffectTrap}, nil)
		region.Nodes[len(region.Nodes)-1].Operation.MemoryAccessID = record.ID
	}
	lowerer.stateful.accesses = append(lowerer.stateful.accesses, record)
	if hasProof {
		lowerer.stateful.proofs = append(lowerer.stateful.proofs, StatefulIndexProof{AccessID: record.ID, Proof: proof})
	}
	return result, nil
}
func (lowerer *optIRLowerer) lowerStatefulLoad(index *ast.IndexExpression, resultType optir.Type, region *optir.Region) (optir.Value, error) {
	if resultType != "u8" {
		return optir.Value{}, refuseOptIR(index.Token, "raw byte load result must be u8")
	}
	descriptor, offset, err := lowerer.statefulIndexOperands(index, region)
	if err != nil {
		return optir.Value{}, err
	}
	return lowerer.statefulAccess(index, descriptor, offset, optir.Value{}, false, region)
}
func (lowerer *optIRLowerer) lowerStatefulStore(store *ast.IndexAssignmentStatement, region *optir.Region) error {
	// Preserve Oak's descriptor, index, then RHS evaluation order even when
	// profile rejection occurs later; the frozen lvalue operands are locals.
	descriptor, offset, err := lowerer.statefulIndexOperands(store.Target, region)
	if err != nil {
		return err
	}
	value, err := lowerer.lowerExpression(store.Value, region)
	if err != nil {
		return err
	}
	_, err = lowerer.statefulAccess(store.Target, descriptor, offset, value, true, region)
	return err
}
func (lowerer *optIRLowerer) lowerStatefulVariant(variant *ast.VariantExpression, resultType optir.Type, region *optir.Region) (optir.Value, error) {
	resolution, ok := lowerer.tc.VariantResolution(variant)
	if !ok || resolution != string(resultType) || variant.Variant == nil {
		return optir.Value{}, refuseOptIR(variant.Token, "raw constructor has no exact checked concrete ADT resolution")
	}
	record, ok := lowerer.stateful.types[resultType]
	if !ok || record.Kind != "adt" {
		return optir.Value{}, refuseOptIR(variant.Token, "raw constructor type is outside the closed inventory")
	}
	var constructor *optir.StatefulConstructor
	for i := range record.Constructors {
		if record.Constructors[i].Name == variant.Variant.Value {
			constructor = &record.Constructors[i]
		}
	}
	if constructor == nil {
		return optir.Value{}, refuseOptIR(variant.Token, "unknown concrete constructor")
	}
	var operands []optir.ValueID
	if variant.Payload != nil {
		value, err := lowerer.lowerExpression(variant.Payload, region)
		if err != nil {
			return optir.Value{}, err
		}
		if len(constructor.Payload) != 1 || constructor.Payload[0] != value.Type {
			return optir.Value{}, refuseOptIR(variant.Token, "constructor payload disagrees with checked declaration")
		}
		operands = []optir.ValueID{value.ID}
	} else if len(constructor.Payload) != 0 {
		return optir.Value{}, refuseOptIR(variant.Token, "constructor omitted checked payload")
	}
	return lowerer.emit(region, optir.OpADTConstruct, resultType, "variant", variant.Token, operands, nil, []optir.Attribute{{Name: optir.AttributeVariant, Value: string(resultType) + "." + constructor.Name}}), nil
}
func (lowerer *optIRLowerer) lowerStatefulMatch(match *ast.MatchExpression, resultType optir.Type, region *optir.Region) (optir.Value, error) {
	typ, err := lowerer.expressionType(match.Scrutinee)
	if err != nil {
		return optir.Value{}, err
	}
	if typ == optir.TypeBool {
		return lowerer.lowerBooleanMatch(match, resultType, region)
	}
	resolution, ok := lowerer.tc.MatchResolution(match)
	if !ok || resolution != string(optir.TypeCopyResult) || typ != optir.TypeCopyResult || len(match.Arms) != 2 {
		return optir.Value{}, refuseOptIR(match.Token, "raw match requires the exhaustive concrete Result")
	}
	scrutinee, err := lowerer.lowerExpression(match.Scrutinee, region)
	if err != nil {
		return optir.Value{}, err
	}
	arms := map[string]*ast.MatchArm{}
	for _, arm := range match.Arms {
		if arm == nil {
			return optir.Value{}, refuseOptIR(match.Token, "nil Result arm")
		}
		pattern, ok := arm.Pattern.(*ast.VariantPattern)
		if !ok || pattern.Variant == nil || (pattern.Variant.Value != "Ok" && pattern.Variant.Value != "Err") || arms[pattern.Variant.Value] != nil {
			return optir.Value{}, refuseOptIR(match.Token, "raw Result match repeats/omits a constructor")
		}
		arms[pattern.Variant.Value] = arm
	}
	condition := lowerer.emit(region, optir.OpADTIsVariant, optir.TypeBool, "is.Ok", match.Token, []optir.ValueID{scrutinee.ID}, nil, []optir.Attribute{{Name: optir.AttributeVariant, Value: string(typ) + ".Ok"}})
	thenLowerer, elseLowerer := lowerer.clone(), lowerer.clone()
	thenRegion, elseRegion := optir.Region{}, optir.Region{}
	lowerArm := func(name string, l *optIRLowerer, r *optir.Region) (optir.Value, error) {
		arm := arms[name]
		pattern := arm.Pattern.(*ast.VariantPattern)
		binding, ok := pattern.Payload.(*ast.BindingPattern)
		if !ok || binding.Name == nil {
			return optir.Value{}, refuseOptIR(pattern.Token, "raw Result arm requires one checked payload binding")
		}
		if _, shadowed := lowerer.env[binding.Name.Value]; shadowed {
			return optir.Value{}, refuseOptIR(pattern.Token, "raw Result payload binding must not shadow a live outer value")
		}
		payloadType := optir.Type("u32")
		if name == "Err" {
			payloadType = optir.TypeCopyError
		}
		// Projection faults on an inactive constructor. The CFG proof establishes
		// the matching branch, rather than trusting a user-supplied branch flag.
		payload := l.ids.value(payloadType, binding.Name.Value, optIRSource(binding.Token))
		r.Nodes = append(r.Nodes, optir.Node{Operation: &optir.Operation{Code: optir.OpADTPayload, Results: []optir.Value{payload}, Operands: []optir.ValueID{scrutinee.ID}, Effects: []optir.Effect{optir.EffectTrap}, Attributes: []optir.Attribute{{Name: optir.AttributeVariant, Value: string(typ) + "." + name}}, Source: optIRSource(binding.Token)}})
		l.env[binding.Name.Value] = payload
		return l.lowerExpression(arm.Body, r)
	}
	thenValue, err := lowerArm("Ok", thenLowerer, &thenRegion)
	if err != nil {
		return optir.Value{}, err
	}
	elseValue, err := lowerArm("Err", elseLowerer, &elseRegion)
	if err != nil {
		return optir.Value{}, err
	}
	if thenValue.Type != resultType || elseValue.Type != resultType {
		return optir.Value{}, fmt.Errorf("compiler: concrete Result match result mismatch")
	}
	return lowerer.finishConditional(condition, thenValue, elseValue, thenLowerer, elseLowerer, thenRegion, elseRegion, match.Token, region)
}

// Every retained code/type source occurrence must resolve to the actual parsed
// package/file bytes. This is a concrete custody check, not frontend soundness.
func verifyStatefulSourceInventory(program optir.StatefulProgram, sources []PackageSource) error {
	contexts := map[string]string{}
	for _, s := range sources {
		key := s.Package + "#" + s.Path
		if s.Package == "" || s.Path == "" || s.Text == "" {
			return fmt.Errorf("compiler: incomplete raw source inventory")
		}
		if _, duplicate := contexts[key]; duplicate {
			return fmt.Errorf("compiler: duplicate raw source identity %s", key)
		}
		contexts[key] = s.Text
	}
	check := func(s optir.Source) error {
		text, ok := contexts[s.Context]
		if !ok {
			return fmt.Errorf("compiler: raw source occurrence has no exact package/file identity: %+v", s)
		}
		lines := strings.Split(text, "\n")
		if s.Line <= 0 || s.Line > len(lines) || s.Column <= 0 || s.Column > len(lines[s.Line-1])+1 {
			return fmt.Errorf("compiler: raw source occurrence lies outside parsed bytes: %+v", s)
		}
		return nil
	}
	for _, f := range program.Functions() {
		for _, b := range f.CFG.Blocks {
			for _, v := range b.Parameters {
				if err := check(v.Source); err != nil {
					return err
				}
			}
			for _, op := range b.Operations {
				if err := check(op.Source); err != nil {
					return err
				}
				for _, v := range op.Results {
					if err := check(v.Source); err != nil {
						return err
					}
				}
			}
		}
	}
	for _, typ := range program.Types() {
		if typ.Kind != "adt" {
			continue
		}
		if err := check(typ.Declaration); err != nil {
			return err
		}
		for _, ctor := range typ.Constructors {
			if err := check(ctor.Declaration); err != nil {
				return err
			}
		}
	}
	return nil
}
