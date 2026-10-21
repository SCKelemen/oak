package optir

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"reflect"
	"sort"
)

// StatefulCopyProfileV1 admits raw, unoptimized OptIR only. It is not an
// optimization permission, frontend theorem, target ABI, or copy-refinement
// verdict. Copy refinement is a separate translation-validation obligation.
const StatefulCopyProfileV1 = "oak.optir.stateful-copy.raw.v1"
const StatefulBoundsTrap = "bounds-mapped-initialized-or-trap"

const (
	TypeByteView     Type = "[]u8"
	TypeByteSpan     Type = "[*]u8"
	TypeCopyError    Type = "bytes__CopyError"
	TypeCopyResult   Type = "Result_u32_bytes__CopyError"
	OpDescriptorLen       = "descriptor.length"
	OpByteLoad            = "memory.byte-load"
	OpByteStore           = "memory.byte-store"
	OpADTConstruct        = "adt.construct"
	OpADTIsVariant        = "adt.is-variant"
	OpADTPayload          = "adt.payload"
	AttributeVariant      = "variant"
)

// StatefulConstructor retains checked declaration identity and ordered logical
// payload types, not a target tag encoding or physical layout.
type StatefulConstructor struct {
	Name        string
	Declaration Source
	Payload     []Type
}

// StatefulTypeRecord is the closed logical inventory supplied by the checked
// declaration/instantiation path. Source/declaration correspondence remains a
// compiler boundary; matching a spelling or digest cannot prove that boundary.
type StatefulTypeRecord struct {
	Type          Type
	Kind          string
	Declaration   Source
	Template      string
	TypeArguments []Type
	Constructors  []StatefulConstructor
}

// ByteAccessRecord binds one source occurrence to its structured SSA operands.
// CFG operand substitution is checked by exact reprojection and exposed by
// ProjectedByteAccesses. These partial byte accesses intentionally do not enter
// CheckedMemoryAuthority's whole-cell optimization vocabulary.
type ByteAccessRecord struct {
	ID           string
	Function     string
	Source       Source
	Formal       int
	Descriptor   ValueID
	Index        ValueID
	Value        ValueID
	Kind         MemoryAccessKind
	Width        uint32
	Element      Type
	CheckPolicy  string
	IndexProofID string
}

// StatefulFormalEffect is a may-effect relative to a callee descriptor formal.
// No field can promote a byte write to whole-region or must-write authority.
type StatefulFormalEffect struct {
	Formal int
	Kind   MemoryAccessKind
}

// StatefulCallRecord binds the exact call operands to callee-formal effects.
// The verifier independently derives effects from the callee's byte accesses;
// a caller-provided empty summary cannot turn this call into NoModRef.
type StatefulCallRecord struct {
	ID       string
	Function string
	Source   Source
	Callee   string
	Operands []ValueID
	Effects  []StatefulFormalEffect
}

type StatefulFunction struct {
	Structured Function
	CFG        CFG
	Facts      CheckedFactAuthority
}

type StatefulProjectedByteAccess struct {
	RecordID   string
	Function   string
	Site       OperationSite
	Descriptor ValueID
	Index      ValueID
	Value      ValueID
}

// StatefulProgram owns private snapshots. All accessors return defensive
// copies. A valid value is created only by NewStatefulProgram; its fingerprint
// is an input identity, never the reason for admission.
type StatefulProgram struct {
	root        string
	functions   []StatefulFunction
	types       []StatefulTypeRecord
	accesses    []ByteAccessRecord
	calls       []StatefulCallRecord
	projected   []StatefulProjectedByteAccess
	fingerprint string
}

func NewByteAccessRecord(record ByteAccessRecord) (ByteAccessRecord, error) {
	record.ID = ""
	if err := validateByteAccessRecord(record); err != nil {
		return ByteAccessRecord{}, err
	}
	record.ID = statefulIdentity("byte-access", record)
	return record, nil
}

func NewStatefulCallRecord(record StatefulCallRecord) (StatefulCallRecord, error) {
	record.ID = ""
	record.Operands = append([]ValueID(nil), record.Operands...)
	record.Effects = append([]StatefulFormalEffect(nil), record.Effects...)
	if err := validateStatefulCallRecord(record); err != nil {
		return StatefulCallRecord{}, err
	}
	record.ID = statefulIdentity("formal-call", record)
	return record, nil
}

func NewStatefulProgram(root string, functions []StatefulFunction, types []StatefulTypeRecord, accesses []ByteAccessRecord, calls []StatefulCallRecord) (StatefulProgram, error) {
	p := StatefulProgram{root: root, functions: cloneStatefulFunctions(functions), types: cloneStatefulTypes(types), accesses: append([]ByteAccessRecord(nil), accesses...), calls: cloneStatefulCalls(calls)}
	sort.Slice(p.functions, func(i, j int) bool { return p.functions[i].Structured.Name < p.functions[j].Structured.Name })
	sort.Slice(p.types, func(i, j int) bool { return p.types[i].Type < p.types[j].Type })
	sort.Slice(p.accesses, func(i, j int) bool { return p.accesses[i].ID < p.accesses[j].ID })
	sort.Slice(p.calls, func(i, j int) bool { return p.calls[i].ID < p.calls[j].ID })
	if err := VerifyStatefulProgram(p); err != nil {
		return StatefulProgram{}, err
	}
	for _, f := range p.functions {
		for _, b := range f.CFG.Blocks {
			for i, op := range b.Operations {
				if op.Code != OpByteLoad && op.Code != OpByteStore {
					continue
				}
				a := StatefulProjectedByteAccess{RecordID: op.MemoryAccessID, Function: f.CFG.Name, Site: OperationSite{Block: b.ID, Index: i}, Descriptor: op.Operands[0], Index: op.Operands[1]}
				if op.Code == OpByteStore {
					a.Value = op.Operands[2]
				}
				p.projected = append(p.projected, a)
			}
		}
	}
	p.fingerprint = statefulIdentity("program", p.identitySnapshot())
	return p, nil
}

func (p StatefulProgram) Root() string                  { return p.root }
func (p StatefulProgram) Profile() string               { return StatefulCopyProfileV1 }
func (p StatefulProgram) Fingerprint() string           { return p.fingerprint }
func (p StatefulProgram) Functions() []StatefulFunction { return cloneStatefulFunctions(p.functions) }
func (p StatefulProgram) Types() []StatefulTypeRecord   { return cloneStatefulTypes(p.types) }
func (p StatefulProgram) ByteAccesses() []ByteAccessRecord {
	return append([]ByteAccessRecord(nil), p.accesses...)
}
func (p StatefulProgram) Calls() []StatefulCallRecord { return cloneStatefulCalls(p.calls) }
func (p StatefulProgram) ProjectedByteAccesses() []StatefulProjectedByteAccess {
	return append([]StatefulProjectedByteAccess(nil), p.projected...)
}

// ExactStatefulProgramEqual compares owned normalized data, including every
// authority field, without relying on collision resistance.
func ExactStatefulProgramEqual(a, b StatefulProgram) (bool, error) {
	if err := VerifyStatefulProgram(a); err != nil {
		return false, err
	}
	if err := VerifyStatefulProgram(b); err != nil {
		return false, err
	}
	return reflect.DeepEqual(a.identitySnapshot(), b.identitySnapshot()), nil
}

type statefulFunctionIdentity struct {
	Structured Function
	CFG        CFG
	Facts      []CheckedFactRecord
}
type statefulProgramIdentity struct {
	Profile, Root string
	Functions     []statefulFunctionIdentity
	Types         []StatefulTypeRecord
	Accesses      []ByteAccessRecord
	Calls         []StatefulCallRecord
}

func (p StatefulProgram) identitySnapshot() statefulProgramIdentity {
	out := statefulProgramIdentity{Profile: StatefulCopyProfileV1, Root: p.root, Types: p.Types(), Accesses: p.ByteAccesses(), Calls: p.Calls()}
	for _, f := range p.functions {
		out.Functions = append(out.Functions, statefulFunctionIdentity{cloneFunction(f.Structured), cloneCFG(f.CFG), f.Facts.Records()})
	}
	return out
}
func statefulIdentity(kind string, value any) string {
	data, err := json.Marshal(value)
	if err != nil {
		panic("optir: internal stateful identity is not serializable")
	}
	hash := sha256.Sum256(append([]byte(StatefulCopyProfileV1+":"+kind+":"), data...))
	return hex.EncodeToString(hash[:])
}
func cloneStatefulFunctions(in []StatefulFunction) []StatefulFunction {
	out := make([]StatefulFunction, len(in))
	for i, f := range in {
		out[i] = StatefulFunction{Structured: cloneFunction(f.Structured), CFG: cloneCFG(f.CFG), Facts: f.Facts}
	}
	return out
}
func cloneStatefulTypes(in []StatefulTypeRecord) []StatefulTypeRecord {
	out := make([]StatefulTypeRecord, len(in))
	for i, t := range in {
		out[i] = t
		out[i].TypeArguments = append([]Type(nil), t.TypeArguments...)
		out[i].Constructors = make([]StatefulConstructor, len(t.Constructors))
		for j, c := range t.Constructors {
			out[i].Constructors[j] = c
			out[i].Constructors[j].Payload = append([]Type(nil), c.Payload...)
		}
	}
	return out
}
func cloneStatefulCalls(in []StatefulCallRecord) []StatefulCallRecord {
	out := make([]StatefulCallRecord, len(in))
	for i, c := range in {
		out[i] = c
		out[i].Operands = append([]ValueID(nil), c.Operands...)
		out[i].Effects = append([]StatefulFormalEffect(nil), c.Effects...)
	}
	return out
}
func statefulSource(source Source) bool {
	return source.Context != "" && source.Line > 0 && source.Column > 0
}
func validateByteAccessRecord(r ByteAccessRecord) error {
	if r.Function != "bytes__copy_uinto" || !statefulSource(r.Source) || r.Descriptor == 0 || r.Index == 0 || r.Width != 1 || r.Element != "u8" || r.CheckPolicy != StatefulBoundsTrap {
		return fmt.Errorf("optir: malformed raw byte access")
	}
	if (r.Kind == MemoryRead && (r.Formal != 1 || r.Value != 0)) || (r.Kind == MemoryWrite && (r.Formal != 0 || r.Value == 0)) || (r.Kind != MemoryRead && r.Kind != MemoryWrite) {
		return fmt.Errorf("optir: raw byte access has invalid formal, kind, or value")
	}
	return nil
}
func validateStatefulCallRecord(r StatefulCallRecord) error {
	if r.Function != "copy_checked" || r.Callee != "bytes__copy_uinto" || !statefulSource(r.Source) || len(r.Operands) != 2 || r.Operands[0] == 0 || r.Operands[1] == 0 || !reflect.DeepEqual(r.Effects, []StatefulFormalEffect{{0, MemoryWrite}, {1, MemoryRead}}) {
		return fmt.Errorf("optir: malformed raw formal call record")
	}
	return nil
}

// VerifyStatefulProgram is a closed semantic-profile check, not a proof that
// the program implements copying. It independently checks all CFG operation
// signatures and effects, exact structured projection, and occurrence-bound
// byte/formal-call authority. Copy equations are checked by the separate
// translation validator against the actual admitted graph.
func VerifyStatefulProgram(p StatefulProgram) error {
	fail := func(format string, args ...any) error { return fmt.Errorf("optir: stateful profile: "+format, args...) }
	if p.root != "copy_checked" || len(p.functions) != 2 {
		return fail("requires exactly the frozen two-function rooted closure")
	}
	if err := verifyStatefulTypes(p.types); err != nil {
		return err
	}
	accesses := map[string]ByteAccessRecord{}
	for _, r := range p.accesses {
		want, err := NewByteAccessRecord(r)
		if err != nil {
			return err
		}
		if r.ID == "" || r.ID != want.ID {
			return fail("byte authority identity mismatch")
		}
		if _, dup := accesses[r.ID]; dup {
			return fail("duplicate byte authority")
		}
		accesses[r.ID] = r
	}
	calls := map[string]StatefulCallRecord{}
	for _, r := range p.calls {
		want, err := NewStatefulCallRecord(r)
		if err != nil {
			return err
		}
		if r.ID == "" || r.ID != want.ID {
			return fail("call authority identity mismatch")
		}
		if _, dup := calls[r.ID]; dup {
			return fail("duplicate call authority")
		}
		calls[r.ID] = r
	}
	if len(accesses) != 2 || len(calls) != 1 {
		return fail("requires exactly one read, one write, and one direct call authority")
	}
	seenFunctions := map[string]bool{}
	seenAccesses := map[string]bool{}
	seenCalls := map[string]bool{}
	var derived []StatefulFormalEffect
	for _, f := range p.functions {
		name := f.Structured.Name
		if seenFunctions[name] || (name != "copy_checked" && name != "bytes__copy_uinto") {
			return fail("duplicate or unknown function %q", name)
		}
		seenFunctions[name] = true
		if len(f.Structured.Parameters) != 2 || f.Structured.Parameters[0].Type != TypeByteSpan || f.Structured.Parameters[1].Type != TypeByteView {
			return fail("%s has wrong descriptor signature", name)
		}
		result := TypeCopyResult
		if name == p.root {
			result = TypeBool
		}
		if !sameTypes(f.Structured.Results, []Type{result}) {
			return fail("%s has wrong result signature", name)
		}
		projected, err := Project(f.Structured)
		if err != nil {
			return fail("%s structured projection: %v", name, err)
		}
		exact, err := ExactCFGEqual(projected, f.CFG)
		if err != nil {
			return err
		}
		if !exact {
			return fail("%s CFG is not the exact raw projection", name)
		}
		if err := VerifyFunctionCheckedFacts(f.Structured, f.Facts); err != nil {
			return err
		}
		if err := VerifyCFGCheckedFacts(f.CFG, f.Facts); err != nil {
			return err
		}
		for _, r := range f.Facts.Records() {
			if !statefulType(r.ValueType) {
				return fail("unrecognized checked fact type %s", r.ValueType)
			}
		}
		types := map[ValueID]Type{}
		for _, b := range f.CFG.Blocks {
			for _, v := range b.Parameters {
				if !statefulType(v.Type) || !statefulSource(v.Source) {
					return fail("invalid CFG parameter type/source")
				}
				types[v.ID] = v.Type
			}
			for _, op := range b.Operations {
				for _, v := range op.Results {
					if !statefulType(v.Type) || !statefulSource(v.Source) {
						return fail("invalid CFG result type/source")
					}
					types[v.ID] = v.Type
				}
			}
		}
		if err := statefulFacts(f.CFG.Facts); err != nil {
			return err
		}
		for _, b := range f.CFG.Blocks {
			for _, op := range b.Operations {
				if err := verifyStatefulOperation(op, types); err != nil {
					return fail("%s block %d: %v", name, b.ID, err)
				}
			}
		}
		err = walkStatefulOperations(f.Structured.Body, func(op Operation) error {
			if op.Code == OpByteLoad || op.Code == OpByteStore {
				r, ok := accesses[op.MemoryAccessID]
				if !ok || seenAccesses[r.ID] {
					return fail("missing or duplicated byte access authority")
				}
				seenAccesses[r.ID] = true
				operands := []ValueID{r.Descriptor, r.Index}
				if r.Kind == MemoryWrite {
					operands = append(operands, r.Value)
				}
				if r.Function != name || r.Source != op.Source || !reflect.DeepEqual(op.Operands, operands) || r.Descriptor != f.Structured.Parameters[r.Formal].ID || (op.Code == OpByteLoad) != (r.Kind == MemoryRead) {
					return fail("byte authority does not bind exact source/formal/operands")
				}
				derived = append(derived, StatefulFormalEffect{r.Formal, r.Kind})
			} else if op.MemoryAccessID != "" {
				return fail("non-byte operation has byte authority")
			}
			if op.Code == OpCall {
				r, ok := calls[op.MemoryCallID]
				if !ok || seenCalls[r.ID] {
					return fail("missing or duplicated call authority")
				}
				seenCalls[r.ID] = true
				if name != p.root || r.Function != name || r.Source != op.Source || !reflect.DeepEqual(r.Operands, op.Operands) || op.Attributes[0].Value != r.Callee {
					return fail("call authority does not bind exact source/operands/callee")
				}
				if !reflect.DeepEqual(op.Operands, []ValueID{f.Structured.Parameters[0].ID, f.Structured.Parameters[1].ID}) {
					return fail("call formal substitution is not dst/src in order")
				}
			} else if op.MemoryCallID != "" {
				return fail("non-call operation has call authority")
			}
			return nil
		})
		if err != nil {
			return err
		}
	}
	if len(seenAccesses) != len(accesses) || len(seenCalls) != len(calls) {
		return fail("unused byte or call authority")
	}
	sort.Slice(derived, func(i, j int) bool {
		if derived[i].Formal != derived[j].Formal {
			return derived[i].Formal < derived[j].Formal
		}
		return derived[i].Kind < derived[j].Kind
	})
	for _, r := range p.calls {
		if !reflect.DeepEqual(derived, r.Effects) {
			return fail("formal call summary differs from callee accesses")
		}
	}
	if p.fingerprint != "" && p.fingerprint != statefulIdentity("program", p.identitySnapshot()) {
		return fail("owned snapshot fingerprint mismatch")
	}
	return nil
}

func statefulType(t Type) bool {
	switch t {
	case "u8", "u32", TypeBool, "()", TypeByteView, TypeByteSpan, TypeCopyError, TypeCopyResult:
		return true
	}
	return false
}
func verifyStatefulTypes(records []StatefulTypeRecord) error {
	if len(records) != 8 {
		return fmt.Errorf("optir: stateful type inventory must contain exactly eight logical types")
	}
	seen := map[Type]bool{}
	for _, r := range records {
		if !statefulType(r.Type) || seen[r.Type] {
			return fmt.Errorf("optir: unknown or duplicate stateful type %s", r.Type)
		}
		seen[r.Type] = true
		switch r.Type {
		case "u8", "u32", TypeBool, "()":
			if r.Kind != "scalar" || r.Template != "" || len(r.TypeArguments) != 0 || len(r.Constructors) != 0 {
				return fmt.Errorf("optir: malformed scalar type record %s", r.Type)
			}
		case TypeByteView, TypeByteSpan:
			kind := "descriptor-read"
			if r.Type == TypeByteSpan {
				kind = "descriptor-write"
			}
			if r.Kind != kind || r.Template != "" || !sameTypes(r.TypeArguments, []Type{"u8"}) || len(r.Constructors) != 0 {
				return fmt.Errorf("optir: malformed byte descriptor type record %s", r.Type)
			}
		case TypeCopyError, TypeCopyResult:
			template := "bytes__CopyError"
			var arguments []Type
			names := []string{"DestinationTooSmall"}
			payloads := [][]Type{nil}
			if r.Type == TypeCopyResult {
				template = "Result"
				arguments = []Type{"u32", TypeCopyError}
				names = []string{"Ok", "Err"}
				payloads = [][]Type{{"u32"}, {TypeCopyError}}
			}
			if r.Kind != "adt" || !statefulSource(r.Declaration) || r.Template != template || !sameTypes(r.TypeArguments, arguments) || len(r.Constructors) != len(names) {
				return fmt.Errorf("optir: malformed checked ADT identity %s", r.Type)
			}
			for i, c := range r.Constructors {
				if c.Name != names[i] || !statefulSource(c.Declaration) || !sameTypes(c.Payload, payloads[i]) {
					return fmt.Errorf("optir: malformed ADT constructor %s.%s", r.Type, c.Name)
				}
			}
		}
	}
	return nil
}
func walkStatefulOperations(region Region, visit func(Operation) error) error {
	for _, node := range region.Nodes {
		switch {
		case node.Operation != nil:
			if err := visit(*node.Operation); err != nil {
				return err
			}
		case node.If != nil:
			if err := walkStatefulOperations(node.If.Then, visit); err != nil {
				return err
			}
			if err := walkStatefulOperations(node.If.Else, visit); err != nil {
				return err
			}
		case node.While != nil:
			if err := walkStatefulOperations(node.While.Condition, visit); err != nil {
				return err
			}
			if err := walkStatefulOperations(node.While.Body, visit); err != nil {
				return err
			}
		default:
			return fmt.Errorf("optir: empty stateful structured node")
		}
	}
	return nil
}
func statefulFacts(facts []Fact) error {
	for _, f := range facts {
		if f.ID == "" || f.Name != checkedTypeFactName || f.Provenance != "checked" {
			return fmt.Errorf("optir: unknown fact in closed stateful profile")
		}
	}
	return nil
}
func verifyStatefulOperation(op Operation, types map[ValueID]Type) error {
	if !statefulSource(op.Source) {
		return fmt.Errorf("operation lacks stable source")
	}
	if err := statefulFacts(op.Facts); err != nil {
		return err
	}
	signature := func(results []Type, operands []Type) error {
		if len(op.Results) != len(results) || len(op.Operands) != len(operands) {
			return fmt.Errorf("%s has wrong arity", op.Code)
		}
		for i, t := range results {
			if op.Results[i].Type != t {
				return fmt.Errorf("%s has wrong result type", op.Code)
			}
		}
		for i, t := range operands {
			if types[op.Operands[i]] != t {
				return fmt.Errorf("%s has wrong operand type", op.Code)
			}
		}
		return nil
	}
	var effects []Effect
	var attributes []string
	switch op.Code {
	case OpConstInt, OpConstBool, OpConstUnit, OpIntAdd, OpLess, OpEqual:
		if err := validateSCCPOperation(op, types); err != nil {
			return err
		}
		if op.Code == OpConstInt || op.Code == OpConstBool {
			attributes = []string{AttributeValue}
		}
		if op.Code == OpIntAdd {
			if err := signature([]Type{"u32"}, []Type{"u32", "u32"}); err != nil {
				return err
			}
		}
		if op.Code == OpLess || op.Code == OpEqual {
			if err := signature([]Type{TypeBool}, []Type{"u32", "u32"}); err != nil {
				return err
			}
		}
	case OpDescriptorLen:
		if len(op.Operands) != 1 || (types[op.Operands[0]] != TypeByteView && types[op.Operands[0]] != TypeByteSpan) {
			return fmt.Errorf("descriptor length requires a byte descriptor")
		}
		if err := signature([]Type{"u32"}, []Type{types[op.Operands[0]]}); err != nil {
			return err
		}
	case OpByteLoad:
		if err := signature([]Type{"u8"}, []Type{TypeByteView, "u32"}); err != nil {
			return err
		}
		effects = []Effect{EffectReadMemory, EffectTrap}
		if op.MemoryAccessID == "" {
			return fmt.Errorf("byte load has no access authority")
		}
	case OpByteStore:
		if err := signature(nil, []Type{TypeByteSpan, "u32", "u8"}); err != nil {
			return err
		}
		effects = []Effect{EffectWriteMemory, EffectTrap}
		if op.MemoryAccessID == "" {
			return fmt.Errorf("byte store has no access authority")
		}
	case OpADTConstruct, OpADTIsVariant, OpADTPayload:
		attributes = []string{AttributeVariant}
		if len(op.Attributes) != 1 || op.Attributes[0].Name != AttributeVariant {
			return fmt.Errorf("ADT operation has no unique variant identity")
		}
		variant := op.Attributes[0].Value
		var adt, payload Type
		switch variant {
		case string(TypeCopyError) + ".DestinationTooSmall":
			adt = TypeCopyError
		case string(TypeCopyResult) + ".Ok":
			adt = TypeCopyResult
			payload = "u32"
		case string(TypeCopyResult) + ".Err":
			adt = TypeCopyResult
			payload = TypeCopyError
		default:
			return fmt.Errorf("unknown qualified ADT constructor %s", variant)
		}
		switch op.Code {
		case OpADTConstruct:
			var args []Type
			if payload != "" {
				args = []Type{payload}
			}
			if err := signature([]Type{adt}, args); err != nil {
				return err
			}
		case OpADTIsVariant:
			if adt != TypeCopyResult {
				return fmt.Errorf("only concrete Result variant tests are admitted")
			}
			if err := signature([]Type{TypeBool}, []Type{adt}); err != nil {
				return err
			}
		case OpADTPayload:
			if adt != TypeCopyResult || payload == "" {
				return fmt.Errorf("payload projection has no concrete Result payload")
			}
			if err := signature([]Type{payload}, []Type{adt}); err != nil {
				return err
			}
			effects = []Effect{EffectTrap}
		}
	case OpCall:
		if err := signature([]Type{TypeCopyResult}, []Type{TypeByteSpan, TypeByteView}); err != nil {
			return err
		}
		attributes = []string{AttributeCallee}
		if len(op.Attributes) != 1 || op.Attributes[0].Name != AttributeCallee || op.Attributes[0].Value != "bytes__copy_uinto" || op.MemoryCallID == "" {
			return fmt.Errorf("call does not bind concrete callee")
		}
		effects = []Effect{EffectCall, EffectReadMemory, EffectWriteMemory, EffectTrap}
	default:
		return fmt.Errorf("unknown operation %q in closed stateful profile", op.Code)
	}
	if len(op.Attributes) != len(attributes) {
		return fmt.Errorf("%s has unexpected attributes", op.Code)
	}
	for i, name := range attributes {
		if op.Attributes[i].Name != name {
			return fmt.Errorf("%s has unknown attribute", op.Code)
		}
	}
	if !sameStatefulEffects(op.Effects, effects) {
		return fmt.Errorf("%s has effects %v, want %v", op.Code, op.Effects, effects)
	}
	if op.Code != OpByteLoad && op.Code != OpByteStore && op.MemoryAccessID != "" {
		return fmt.Errorf("non-byte operation carries access authority")
	}
	if op.Code != OpCall && op.MemoryCallID != "" {
		return fmt.Errorf("non-call carries call authority")
	}
	return nil
}
func sameStatefulEffects(a, b []Effect) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}
