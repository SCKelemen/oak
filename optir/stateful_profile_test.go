package optir

import (
	"testing"
)

// These small graphs exercise the profile checker. Production-source admission
// is exercised separately in compiler; these unit fixtures are not the exported
// program or the copy-refinement proof.
func statefulProfileFixture(t *testing.T) StatefulProgram {
	t.Helper()
	source := func(line int) Source { return Source{Context: "profile-unit.oak", Line: line, Column: 1} }
	value := func(id ValueID, typ Type) Value { return Value{ID: id, Type: typ, Source: source(int(id) + 1)} }
	op := func(code string, id ValueID, typ Type, operands ...ValueID) Operation {
		out := Operation{Code: code, Operands: operands, Source: source(int(id) + 20)}
		if id != 0 {
			out.Results = []Value{value(id, typ)}
		}
		return out
	}
	node := func(o Operation) Node { return Node{Operation: &o} }
	constant := func(id ValueID, v string) Operation {
		o := op(OpConstInt, id, "u32")
		o.Attributes = []Attribute{{AttributeValue, v}}
		return o
	}
	construct := func(id ValueID, typ Type, variant string, args ...ValueID) Operation {
		o := op(OpADTConstruct, id, typ, args...)
		o.Attributes = []Attribute{{AttributeVariant, string(typ) + "." + variant}}
		return o
	}
	params := []Value{value(1, TypeByteSpan), value(2, TypeByteView)}
	load := op(OpByteLoad, 14, "u8", 2, 12)
	load.Effects = []Effect{EffectReadMemory, EffectTrap}
	read, err := NewByteAccessRecord(ByteAccessRecord{Function: "bytes__copy_uinto", Source: load.Source, Formal: 1, Descriptor: 2, Index: 12, Kind: MemoryRead, Width: 1, Element: "u8", CheckPolicy: StatefulBoundsTrap})
	if err != nil {
		t.Fatal(err)
	}
	load.MemoryAccessID = read.ID
	store := op(OpByteStore, 0, "", 1, 12, 14)
	store.Source = source(50)
	store.Effects = []Effect{EffectWriteMemory, EffectTrap}
	write, err := NewByteAccessRecord(ByteAccessRecord{Function: "bytes__copy_uinto", Source: store.Source, Formal: 0, Descriptor: 1, Index: 12, Value: 14, Kind: MemoryWrite, Width: 1, Element: "u8", CheckPolicy: StatefulBoundsTrap})
	if err != nil {
		t.Fatal(err)
	}
	store.MemoryAccessID = write.ID
	loop := While{Initial: []ValueID{9}, Results: []Value{value(10, "u32")}, Condition: Region{Arguments: []Value{value(11, "u32")}, Nodes: []Node{node(op(OpLess, 13, TypeBool, 11, 3))}, Yield: []ValueID{13}}, Body: Region{Arguments: []Value{value(12, "u32")}, Nodes: []Node{node(load), node(store), node(constant(15, "1")), node(op(OpIntAdd, 16, "u32", 12, 15))}, Yield: []ValueID{16}}}
	branch := If{Condition: 5, Results: []Value{value(6, TypeCopyResult)}, Then: Region{Nodes: []Node{node(construct(7, TypeCopyError, "DestinationTooSmall")), node(construct(8, TypeCopyResult, "Err", 7))}, Yield: []ValueID{8}}, Else: Region{Nodes: []Node{node(constant(9, "0")), {While: &loop}, node(construct(17, TypeCopyResult, "Ok", 3))}, Yield: []ValueID{17}}}
	callee := Function{Name: "bytes__copy_uinto", Parameters: params, Results: []Type{TypeCopyResult}, Body: Region{Nodes: []Node{node(op(OpDescriptorLen, 3, "u32", 2)), node(op(OpDescriptorLen, 4, "u32", 1)), node(op(OpLess, 5, TypeBool, 4, 3)), {If: &branch}}, Yield: []ValueID{6}}}
	call := op(OpCall, 4, TypeCopyResult, 1, 2)
	call.Attributes = []Attribute{{AttributeCallee, callee.Name}}
	call.Effects = []Effect{EffectCall, EffectReadMemory, EffectWriteMemory, EffectTrap}
	cr, err := NewStatefulCallRecord(StatefulCallRecord{Function: "copy_checked", Source: call.Source, Callee: callee.Name, Operands: []ValueID{1, 2}, Effects: []StatefulFormalEffect{{0, MemoryWrite}, {1, MemoryRead}}})
	if err != nil {
		t.Fatal(err)
	}
	call.MemoryCallID = cr.ID
	test := op(OpADTIsVariant, 5, TypeBool, 4)
	test.Attributes = []Attribute{{AttributeVariant, string(TypeCopyResult) + ".Ok"}}
	payload := op(OpADTPayload, 7, "u32", 4)
	payload.Attributes = []Attribute{{AttributeVariant, string(TypeCopyResult) + ".Ok"}}
	payload.Effects = []Effect{EffectTrap}
	no := op(OpConstBool, 9, TypeBool)
	no.Attributes = []Attribute{{AttributeValue, "false"}}
	choose := If{Condition: 5, Results: []Value{value(6, TypeBool)}, Then: Region{Nodes: []Node{node(payload), node(op(OpEqual, 8, TypeBool, 7, 3))}, Yield: []ValueID{8}}, Else: Region{Nodes: []Node{node(no)}, Yield: []ValueID{9}}}
	caller := Function{Name: "copy_checked", Parameters: params, Results: []Type{TypeBool}, Body: Region{Nodes: []Node{node(op(OpDescriptorLen, 3, "u32", 2)), node(call), node(test), {If: &choose}}, Yield: []ValueID{6}}}
	facts, err := NewCheckedFactAuthority(nil)
	if err != nil {
		t.Fatal(err)
	}
	var functions []StatefulFunction
	for _, f := range []Function{caller, callee} {
		cfg, err := Project(f)
		if err != nil {
			t.Fatal(err)
		}
		functions = append(functions, StatefulFunction{Structured: f, CFG: cfg, Facts: facts})
	}
	types := []StatefulTypeRecord{{Type: "u8", Kind: "scalar"}, {Type: "u32", Kind: "scalar"}, {Type: TypeBool, Kind: "scalar"}, {Type: "()", Kind: "scalar"}, {Type: TypeByteView, Kind: "descriptor-read", TypeArguments: []Type{"u8"}}, {Type: TypeByteSpan, Kind: "descriptor-write", TypeArguments: []Type{"u8"}}, {Type: TypeCopyError, Kind: "adt", Declaration: source(1), Template: string(TypeCopyError), Constructors: []StatefulConstructor{{Name: "DestinationTooSmall", Declaration: source(1)}}}, {Type: TypeCopyResult, Kind: "adt", Declaration: source(2), Template: "Result", TypeArguments: []Type{"u32", TypeCopyError}, Constructors: []StatefulConstructor{{Name: "Ok", Declaration: source(2), Payload: []Type{"u32"}}, {Name: "Err", Declaration: source(2), Payload: []Type{TypeCopyError}}}}}
	p, err := NewStatefulProgram(caller.Name, functions, types, []ByteAccessRecord{read, write}, []StatefulCallRecord{cr})
	if err != nil {
		t.Fatal(err)
	}
	return p
}

func TestStatefulRawProfileExactProjectionAndSnapshots(t *testing.T) {
	p := statefulProfileFixture(t)
	if err := VerifyStatefulProgram(p); err != nil {
		t.Fatal(err)
	}
	rebuilt, err := NewStatefulProgram(p.Root(), p.Functions(), p.Types(), p.ByteAccesses(), p.Calls())
	if err != nil {
		t.Fatal(err)
	}
	if eq, err := ExactStatefulProgramEqual(p, rebuilt); err != nil || !eq {
		t.Fatalf("exact rebuild = %v, %v", eq, err)
	}
	if p.Fingerprint() == "" || p.Fingerprint() != rebuilt.Fingerprint() {
		t.Fatal("nondeterministic snapshot fingerprint")
	}
	funcs := p.Functions()
	funcs[0].Structured.Parameters[0].Type = "u64"
	funcs[0].CFG.Blocks[0].Operations[0].Code = "invented"
	types := p.Types()
	types[len(types)-1].Kind = "invented"
	calls := p.Calls()
	calls[0].Operands[0] = 900
	access := p.ByteAccesses()
	access[0].Width = 8
	projected := p.ProjectedByteAccesses()
	projected[0].Index = 900
	if err := VerifyStatefulProgram(p); err != nil {
		t.Fatalf("getter mutation changed snapshot: %v", err)
	}
	if p.Fingerprint() != rebuilt.Fingerprint() {
		t.Fatal("getter mutation changed identity")
	}
	for _, bound := range p.ProjectedByteAccesses() {
		var original ByteAccessRecord
		for _, a := range p.ByteAccesses() {
			if a.ID == bound.RecordID {
				original = a
			}
		}
		if bound.Index == original.Index || bound.Descriptor != original.Descriptor {
			t.Fatal("loop operand remapping not reflected in projected byte binding")
		}
	}
}

func TestStatefulRawProfileRefusesMutations(t *testing.T) {
	mutateOp := func(functions []StatefulFunction, code string, change func(*Operation)) {
		var walk func(*Region)
		walk = func(r *Region) {
			for i := range r.Nodes {
				n := &r.Nodes[i]
				if n.Operation != nil && n.Operation.Code == code {
					change(n.Operation)
					return
				}
				if n.If != nil {
					walk(&n.If.Then)
					walk(&n.If.Else)
				}
				if n.While != nil {
					walk(&n.While.Condition)
					walk(&n.While.Body)
				}
			}
		}
		for i := range functions {
			walk(&functions[i].Structured.Body)
		}
	}
	cases := []struct {
		name      string
		change    func([]StatefulFunction, []StatefulTypeRecord, []ByteAccessRecord, []StatefulCallRecord)
		reproject bool
	}{
		{"unknown-op", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpDescriptorLen, func(o *Operation) { o.Code = "descriptor.oracle" })
		}, true},
		{"unknown-attribute", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpDescriptorLen, func(o *Operation) { o.Attributes = []Attribute{{"oracle", "true"}} })
		}, true},
		{"missing-read-effect", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpByteLoad, func(o *Operation) { o.Effects = []Effect{EffectTrap} })
		}, true},
		{"missing-write-trap", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpByteStore, func(o *Operation) { o.Effects = []Effect{EffectWriteMemory} })
		}, true},
		{"missing-call-effect", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpCall, func(o *Operation) { o.Effects = o.Effects[1:] })
		}, true},
		{"payload-pure", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpADTPayload, func(o *Operation) { o.Effects = nil })
		}, true},
		{"wrong-constructor", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpADTConstruct, func(o *Operation) { o.Attributes[0].Value = "Other.Ok" })
		}, true},
		{"wrong-callee", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpCall, func(o *Operation) { o.Attributes[0].Value = "bytes__copy_other" })
		}, true},
		{"wrong-index-binding", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpByteLoad, func(o *Operation) { o.Operands[1] = 3 })
		}, true},
		{"forged-access", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpByteStore, func(o *Operation) { o.MemoryAccessID = "forged" })
		}, true},
		{"whole-cell-disguise", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpByteStore, func(o *Operation) { o.Code = OpStoreRegion })
		}, true},
		{"wrong-width", func(_ []StatefulFunction, _ []StatefulTypeRecord, a []ByteAccessRecord, _ []StatefulCallRecord) {
			a[0].Width = 8
		}, true},
		{"wrong-source", func(_ []StatefulFunction, _ []StatefulTypeRecord, a []ByteAccessRecord, _ []StatefulCallRecord) {
			a[0].Source.Context = "other"
		}, true},
		{"wrong-formal", func(_ []StatefulFunction, _ []StatefulTypeRecord, a []ByteAccessRecord, _ []StatefulCallRecord) {
			a[0].Formal = 99
		}, true},
		{"NoModRef", func(_ []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, c []StatefulCallRecord) {
			c[0].Effects = nil
		}, true},
		{"wrong-constructor-order", func(_ []StatefulFunction, types []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			for i := range types {
				if types[i].Type == TypeCopyResult {
					types[i].Constructors[0], types[i].Constructors[1] = types[i].Constructors[1], types[i].Constructors[0]
				}
			}
		}, true},
		{"unknown-type", func(_ []StatefulFunction, types []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			types[0].Type = "[*]u16"
		}, true},
		{"structured-only", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			mutateOp(f, OpConstInt, func(o *Operation) { o.Attributes[0].Value = "2" })
		}, false},
		{"CFG-only", func(f []StatefulFunction, _ []StatefulTypeRecord, _ []ByteAccessRecord, _ []StatefulCallRecord) {
			f[0].CFG.Blocks[0].Operations[0].Operands[0] = 1
		}, false},
	}
	for _, tc := range cases {
		t.Run(tc.name, func(t *testing.T) {
			p := statefulProfileFixture(t)
			f, types, a, c := p.Functions(), p.Types(), p.ByteAccesses(), p.Calls()
			tc.change(f, types, a, c)
			if tc.reproject {
				for i := range f {
					cfg, err := Project(f[i].Structured)
					if err != nil {
						return
					}
					f[i].CFG = cfg
				}
			}
			if _, err := NewStatefulProgram(p.Root(), f, types, a, c); err == nil {
				t.Fatal("mutation admitted")
			}
		})
	}
}

func TestStatefulRawProfileRequiresExactAuthorityInventory(t *testing.T) {
	p := statefulProfileFixture(t)
	for _, accesses := range [][]ByteAccessRecord{p.ByteAccesses()[:1], append(p.ByteAccesses(), p.ByteAccesses()[0])} {
		if _, err := NewStatefulProgram(p.Root(), p.Functions(), p.Types(), accesses, p.Calls()); err == nil {
			t.Fatal("missing/duplicate authority admitted")
		}
	}
	if _, err := NewStatefulProgram(p.Root(), p.Functions(), p.Types(), p.ByteAccesses(), nil); err == nil {
		t.Fatal("missing call authority admitted")
	}
}
