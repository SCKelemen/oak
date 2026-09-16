package optir

import (
	"reflect"
	"slices"
	"strconv"
	"testing"
)

func TestSCCPConstantIdentitiesAtEveryIntegerWidth(t *testing.T) {
	for _, scalar := range []struct {
		typ  Type
		ones string
	}{
		{"i8", "-1"}, {"u8", "255"},
		{"i16", "-1"}, {"u16", "65535"},
		{"i32", "-1"}, {"u32", "4294967295"},
		{"i64", "-1"}, {"u64", "18446744073709551615"},
		{"i128", "-1"}, {"u128", "340282366920938463463374607431768211455"},
	} {
		for _, test := range []struct {
			name     string
			code     string
			operands []ValueID
			integer  string
			boolean  bool
		}{
			{"subtract-self", OpIntSub, []ValueID{1, 1}, "0", false},
			{"xor-self", OpIntXor, []ValueID{1, 1}, "0", false},
			{"equal-self", OpEqual, []ValueID{1, 1}, "", true},
			{"unequal-self", OpNotEqual, []ValueID{1, 1}, "", false},
			{"less-self", OpLess, []ValueID{1, 1}, "", false},
			{"less-equal-self", OpLessEqual, []ValueID{1, 1}, "", true},
			{"greater-self", OpGreater, []ValueID{1, 1}, "", false},
			{"greater-equal-self", OpGreaterEqual, []ValueID{1, 1}, "", true},
			{"multiply-zero-left", OpIntMul, []ValueID{2, 1}, "0", false},
			{"multiply-zero-right", OpIntMul, []ValueID{1, 2}, "0", false},
			{"and-zero-left", OpIntAnd, []ValueID{2, 1}, "0", false},
			{"and-zero-right", OpIntAnd, []ValueID{1, 2}, "0", false},
			{"or-ones-left", OpIntOr, []ValueID{3, 1}, scalar.ones, false},
			{"or-ones-right", OpIntOr, []ValueID{1, 3}, scalar.ones, false},
		} {
			t.Run(string(scalar.typ)+"/"+test.name, func(t *testing.T) {
				resultType := scalar.typ
				want := Constant{Kind: ConstantInteger, Type: scalar.typ, Integer: test.integer}
				if test.integer == "" {
					resultType = TypeBool
					want = Constant{Kind: ConstantBool, Type: TypeBool, Bool: test.boolean}
				}
				cfg := CFG{Name: test.name, Entry: 0, Results: []Type{resultType}, Blocks: []Block{{
					ID: 0, Parameters: []Value{sccpValue(1, scalar.typ)},
					Operations: []Operation{
						integerConstant(2, scalar.typ, "0"), integerConstant(3, scalar.typ, scalar.ones),
						{Code: test.code, Results: []Value{sccpValue(4, resultType)}, Operands: test.operands},
					},
					Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}},
				}}}
				analysis, err := AnalyzeSCCP(cfg)
				if err != nil {
					t.Fatal(err)
				}
				value, _ := analysis.Value(4)
				if value.State != LatticeConstant || value.Constant != want {
					t.Fatalf("identity = %+v, want %+v", value, want)
				}
				rewritten, report, err := SimplifyWithSCCP(cfg, analysis)
				if err != nil || !reflect.DeepEqual(report.RewrittenValues, []ValueID{4}) || !operationIsConstant(rewritten.Blocks[0].Operations[2], want) {
					t.Fatalf("identity was not rewritten: %+v, %v", report, err)
				}
			})
		}
	}
}

func TestSCCPAbsorbingTransferIsMonotone(t *testing.T) {
	for _, typ := range []Type{"i8", "u8", "i64", "u64", "i128", "u128"} {
		ones, err := normalizeInteger("-1", typ)
		if err != nil {
			t.Fatal(err)
		}
		states := []latticeValue{{state: LatticeUnknown}, {state: LatticeOverdefined}}
		for _, value := range []string{"0", "1", "2", ones} {
			states = append(states, latticeValue{state: LatticeConstant, constant: Constant{Kind: ConstantInteger, Type: typ, Integer: value}})
		}
		for _, code := range []string{OpIntMul, OpIntAnd, OpIntOr} {
			operation := Operation{Code: code, Results: []Value{sccpValue(3, typ)}, Operands: []ValueID{1, 2}}
			evaluate := func(left, right latticeValue) latticeValue {
				t.Helper()
				values, err := evaluateSCCPOperation(operation, map[ValueID]latticeValue{1: left, 2: right})
				if err != nil || len(values) != 1 {
					t.Fatalf("%s transfer failed: %v", code, err)
				}
				return values[0]
			}
			for _, left := range states {
				for _, right := range states {
					before := evaluate(left, right)
					for _, nextLeft := range states {
						if joinLattice(left, nextLeft) != nextLeft {
							continue
						}
						for _, nextRight := range states {
							if joinLattice(right, nextRight) != nextRight {
								continue
							}
							after := evaluate(nextLeft, nextRight)
							if joinLattice(before, after) != after {
								t.Fatalf("%s %s not monotone: (%+v, %+v) -> (%+v, %+v): %+v -> %+v", typ, code, left, right, nextLeft, nextRight, before, after)
							}
						}
					}
				}
			}
		}
	}
}

func TestSCCPAbsorbingIdentitiesExhaustiveByteSemantics(t *testing.T) {
	for _, typ := range []Type{"i8", "u8"} {
		for _, code := range []string{OpIntMul, OpIntAnd, OpIntOr} {
			absorber := uint8(0)
			if code == OpIntOr {
				absorber = 255
			}
			spell := func(value uint8) string {
				if typ == "i8" {
					return strconv.Itoa(int(int8(value)))
				}
				return strconv.Itoa(int(value))
			}
			for _, reverse := range []bool{false, true} {
				operands := []ValueID{1, 2}
				if reverse {
					operands = []ValueID{2, 1}
				}
				operation := Operation{Code: code, Results: []Value{sccpValue(3, typ)}, Operands: operands}
				values, err := evaluateSCCPOperation(operation, map[ValueID]latticeValue{
					1: {state: LatticeOverdefined},
					2: {state: LatticeConstant, constant: Constant{Kind: ConstantInteger, Type: typ, Integer: spell(absorber)}},
				})
				if err != nil || len(values) != 1 || values[0].state != LatticeConstant {
					t.Fatalf("%s %s identity not constant: %+v, %v", typ, code, values, err)
				}
				for input := 0; input < 256; input++ {
					left, right := uint8(input), absorber
					if reverse {
						left, right = right, left
					}
					var want uint8
					switch code {
					case OpIntMul:
						want = left * right
					case OpIntAnd:
						want = left & right
					case OpIntOr:
						want = left | right
					}
					if values[0].constant.Integer != spell(want) {
						t.Fatalf("%s %s(%d,%d) = %+v, want %s", typ, code, left, right, values[0], spell(want))
					}
				}
			}
		}
	}
}

func TestSCCPIdentityRequiresExactValueAndClosedTotalOperation(t *testing.T) {
	for _, test := range []struct {
		name      string
		typ       Type
		code      string
		distinct  bool
		effects   []Effect
		attrs     []Attribute
		wantError bool
	}{
		{name: "different-subtract", typ: "u32", code: OpIntSub, distinct: true},
		{name: "different-xor", typ: "u32", code: OpIntXor, distinct: true},
		{name: "different-equality", typ: TypeBool, code: OpEqual, distinct: true},
		{name: "division-self", typ: "u32", code: OpIntDiv, effects: []Effect{EffectTrap}},
		{name: "shift-self", typ: "u32", code: OpIntShl, effects: []Effect{EffectTrap}},
		{name: "effectful-subtract", typ: "u32", code: OpIntSub, effects: []Effect{EffectTrap}},
		{name: "attributed-subtract", typ: "u32", code: OpIntSub, attrs: []Attribute{{Name: "future-semantics", Value: "checked"}}},
		{name: "unknown-operation", typ: "u32", code: "future.operation"},
		{name: "float-equality", typ: "f32", code: OpEqual, wantError: true},
	} {
		t.Run(test.name, func(t *testing.T) {
			resultType := test.typ
			if test.code == OpEqual {
				resultType = TypeBool
			}
			operands := []ValueID{1, 1}
			if test.distinct {
				operands[1] = 2
			}
			cfg := CFG{Name: test.name, Entry: 0, Results: []Type{resultType}, Blocks: []Block{{
				ID: 0, Parameters: []Value{{ID: 1, Type: test.typ, Name: "same-name"}, {ID: 2, Type: test.typ, Name: "same-name"}},
				Operations: []Operation{{Code: test.code, Results: []Value{sccpValue(3, resultType)}, Operands: operands, Effects: test.effects, Attributes: test.attrs}},
				Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}},
			}}}
			result, err := AnalyzeSCCP(cfg)
			if test.wantError {
				if err == nil {
					t.Fatal("accepted unsupported float equality")
				}
				return
			}
			if err != nil {
				t.Fatal(err)
			}
			if value, _ := result.Value(3); value.State != LatticeOverdefined {
				t.Fatalf("unjustified identity: %+v", value)
			}
		})
	}
}

func TestSCCPBoolReflexiveIdentity(t *testing.T) {
	for _, code := range []string{OpEqual, OpNotEqual} {
		cfg := CFG{Name: "bool-self", Entry: 0, Results: []Type{TypeBool}, Blocks: []Block{{
			ID: 0, Parameters: []Value{sccpValue(1, TypeBool)},
			Operations: []Operation{{Code: code, Results: []Value{sccpValue(2, TypeBool)}, Operands: []ValueID{1, 1}}},
			Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{2}},
		}}}
		result, err := AnalyzeSCCP(cfg)
		if err != nil {
			t.Fatal(err)
		}
		if value, _ := result.Value(2); value.State != LatticeConstant || value.Constant.Bool != (code == OpEqual) {
			t.Fatalf("%s reflexive Bool = %+v", code, value)
		}
	}
}

func TestSCCPIdentityRetainsEffectfulProducers(t *testing.T) {
	for _, producer := range []Operation{
		validSCCPCall(),
		{Code: OpLoadRegion, Results: []Value{sccpValue(2, "u32")}, Effects: []Effect{EffectReadMemory}},
		{Code: OpIntDiv, Results: []Value{sccpValue(2, "u32")}, Operands: []ValueID{1, 1}, Effects: []Effect{EffectTrap}},
	} {
		t.Run(producer.Code, func(t *testing.T) {
			cfg := sccpCallCFG(producer)
			cfg.Blocks[0].Operations = append(cfg.Blocks[0].Operations, integerConstant(3, "u32", "0"), Operation{
				Code: OpIntMul, Results: []Value{sccpValue(4, "u32")}, Operands: []ValueID{2, 3},
			})
			cfg.Blocks[0].Terminator.Values = []ValueID{4}
			analysis, err := AnalyzeSCCP(cfg)
			if err != nil {
				t.Fatal(err)
			}
			rewritten, report, err := SimplifyWithSCCP(cfg, analysis)
			if err != nil || !reflect.DeepEqual(report.RewrittenValues, []ValueID{4}) {
				t.Fatalf("effect result not folded: %+v, %v", report, err)
			}
			cleaned, _, err := SimplifyGVNDCE(rewritten)
			if err != nil {
				t.Fatal(err)
			}
			if len(cleaned.Blocks[0].Operations) != 2 {
				t.Fatalf("folding result changed producer: %+v", cleaned.Blocks[0].Operations)
			}
			kept := cleaned.Blocks[0].Operations[0]
			if kept.Code != producer.Code || !slices.Equal(kept.Results, producer.Results) || !slices.Equal(kept.Operands, producer.Operands) || !slices.Equal(kept.Effects, producer.Effects) || !slices.Equal(kept.Attributes, producer.Attributes) {
				t.Fatalf("folding result changed producer: %+v", kept)
			}
		})
	}
}

func TestSCCPAbsorbingLoopPhiConvergesIndependentOfBlockOrder(t *testing.T) {
	cfg := CFG{Name: "changing-absorber", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{
		{ID: 0, Parameters: []Value{sccpValue(1, "u32")}, Operations: []Operation{integerConstant(2, "u32", "0")}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{2}}}},
		{ID: 1, Parameters: []Value{sccpValue(3, "u32")}, Operations: []Operation{
			{Code: OpIntMul, Results: []Value{sccpValue(4, "u32")}, Operands: []ValueID{1, 3}},
			{Code: OpEqual, Results: []Value{sccpValue(5, TypeBool)}, Operands: []ValueID{4, 2}},
		}, Terminator: Terminator{Kind: TerminatorCondBranch, Condition: 5, True: Edge{Target: 2}, False: Edge{Target: 3}}},
		{ID: 2, Operations: []Operation{integerConstant(6, "u32", "1"), {Code: OpIntAdd, Results: []Value{sccpValue(7, "u32")}, Operands: []ValueID{3, 6}}}, Terminator: Terminator{Kind: TerminatorBranch, True: Edge{Target: 1, Arguments: []ValueID{7}}}},
		{ID: 3, Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{4}}},
	}}
	var checkOrders func(int)
	checkOrders = func(index int) {
		if index < len(cfg.Blocks) {
			for next := index; next < len(cfg.Blocks); next++ {
				cfg.Blocks[index], cfg.Blocks[next] = cfg.Blocks[next], cfg.Blocks[index]
				checkOrders(index + 1)
				cfg.Blocks[index], cfg.Blocks[next] = cfg.Blocks[next], cfg.Blocks[index]
			}
			return
		}
		result, err := AnalyzeSCCP(cfg)
		if err != nil {
			t.Fatal(err)
		}
		for _, id := range []ValueID{3, 4, 5} {
			if value, _ := result.Value(id); value.State != LatticeOverdefined {
				t.Fatalf("phi lost its later nonzero backedge input: %+v", value)
			}
		}
		if len(result.ExecutableBlocks) != 4 || len(result.Branches) != 0 {
			t.Fatalf("constant from first iteration incorrectly pruned loop exit: %+v", result)
		}
	}
	checkOrders(0)
}

func TestSCCPIdentityRejectsStaleAndForgedEvidence(t *testing.T) {
	cfg := CFG{Name: "identity-evidence", Entry: 0, Results: []Type{"u32"}, Blocks: []Block{{
		ID: 0, Parameters: []Value{sccpValue(1, "u32"), sccpValue(2, "u32")},
		Operations: []Operation{{Code: OpIntSub, Results: []Value{sccpValue(3, "u32")}, Operands: []ValueID{1, 1}}},
		Terminator: Terminator{Kind: TerminatorReturn, Values: []ValueID{3}},
	}}}
	evidence, err := AnalyzeSCCP(cfg)
	if err != nil {
		t.Fatal(err)
	}
	changed := cloneCFG(cfg)
	changed.Blocks[0].Operations[0].Operands[1] = 2
	if _, _, err := SimplifyWithSCCP(changed, evidence); err == nil {
		t.Fatal("accepted identity evidence for different SSA operands")
	}
	for index := range evidence.Values {
		if evidence.Values[index].Value == 3 {
			evidence.Values[index].Constant.Integer = "1"
		}
	}
	if _, _, err := SimplifyWithSCCP(cfg, evidence); err == nil {
		t.Fatal("accepted a forged identity result")
	}
}
