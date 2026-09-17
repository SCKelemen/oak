package machine

import (
	"bytes"
	"math"
	"reflect"
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
)

func reallocationCacheFixture(rv bool) *asm.Function {
	if rv {
		return rvfn(ins("mv", rx(5), rx(10)), ins("addiw", rx(6), rx(5), imm(1)), ins("mv", rx(10), rx(6)), ins("ret"))
	}
	return fn(ins("mov", w(9), w(0)), ins("add", w(10), w(9), imm(1)), ins("mov", w(0), w(10)), ins("ret"))
}

func TestReallocationCacheColdHitAndNil(t *testing.T) {
	for _, rv := range []bool{false, true} {
		function := reallocationCacheFixture(rv)
		want, allocation, err := ReallocateWith(function, nil)
		if err != nil {
			t.Fatal(err)
		}
		var cache ReallocationCache
		for call := 0; call < 3; call++ {
			got, summary, err := cache.Apply(function, nil)
			if err != nil || !reflect.DeepEqual(got, want) || summary != (ReallocationSummary{Sites: allocation.Sites(), Promoted: allocation.Promoted}) {
				t.Fatalf("rv=%v call=%d: result differs from normal reallocation: %v %+v", rv, call, err, summary)
			}
			if got == function || got == want {
				t.Fatal("cache returned a caller's function pointer")
			}
		}
		stats := cache.Stats()
		if stats.Requests != 3 || stats.Hits != 2 || stats.Entries != 1 || stats.PayloadBytes <= 0 {
			t.Fatalf("unexpected stats: %+v", stats)
		}
		stats.Requests = 100
		if cache.Stats().Requests != 3 {
			t.Fatal("Stats did not return a snapshot")
		}
		var uncached *ReallocationCache
		got, summary, err := uncached.Apply(function, nil)
		if err != nil || !reflect.DeepEqual(got, want) || summary.Sites != allocation.Sites() || uncached.Stats() != (ReallocationCacheStats{}) {
			t.Fatalf("nil receiver changed ordinary behavior: %v %+v", err, summary)
		}
	}
}

func reallocationRichPayload() *asm.Function {
	index := w(2)
	store := ins("str", w(0), asm.Memory{Base: x(1), Index: &index, Shift: 2, Extend: "uxtw"})
	store.Line, store.OptIRCallSite = 17, 23
	store.CheckedFacts = []asm.CheckedFactRef{{ID: "id", Kind: "kind", Container: "words", Operand: 1, Extent: 8}}
	return fn(store, ins("st1", asm.RegisterList{Regs: []asm.Register{v(0, "4s"), v(1, "4s")}}, mem(x(3), 0)), ins("ret"))
}

func encodedCachePayload(t *testing.T, function *asm.Function, summary ReallocationSummary) []byte {
	t.Helper()
	encoded, ok := encodeReallocation(reallocationPayload{Items: function.Items, Clobbers: function.Clobbers, Summary: summary}, reallocationCacheBytes)
	if !ok {
		t.Fatal("fixture output was not encodable")
	}
	return encoded
}

func mutateReallocationPayload(function *asm.Function) {
	for _, item := range function.Items {
		instruction, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		for _, operand := range instruction.Operands {
			switch value := operand.(type) {
			case asm.Memory:
				if value.Index != nil {
					value.Index.Num = 14
				}
			case asm.RegisterList:
				value.Regs[0].Num = 15
			}
		}
		if len(instruction.CheckedFacts) != 0 {
			instruction.CheckedFacts[0].ID = "changed"
		}
		if len(instruction.Operands) != 0 {
			instruction.Operands[0] = w(7)
		}
	}
	function.Clobbers[0].Num = 16
}

func TestReallocationCacheFreezesStoreAndHitPayloads(t *testing.T) {
	var cache ReallocationCache
	input := reallocationRichPayload()
	first, summary, err := cache.Apply(input, nil)
	if err != nil {
		t.Fatal(err)
	}
	want := encodedCachePayload(t, first, summary)
	mutateReallocationPayload(first)
	mutateReallocationPayload(input)
	for i := 0; i < 2; i++ {
		hit, gotSummary, err := cache.Apply(reallocationRichPayload(), nil)
		if err != nil || !bytes.Equal(encodedCachePayload(t, hit, gotSummary), want) {
			t.Fatalf("cached payload retained mutable aliases: %v", err)
		}
		mutateReallocationPayload(hit)
	}
	if got := cache.Stats(); got.Hits != 2 || got.Entries != 1 {
		t.Fatalf("mutation fixture did not exercise actual hits: %+v", got)
	}
}

func TestReallocationCacheKeepsCurrentMetadata(t *testing.T) {
	var cache ReallocationCache
	old := reallocationCacheFixture(false)
	old.Body = &ast.Identifier{Value: "old"}
	old.Signature = &ast.FunctionStatement{Name: &ast.Identifier{Value: "old"}}
	old.Constants = map[string]asm.Constant{"old": {Type: "u32", Value: 1}}
	if _, _, err := cache.Apply(old, nil); err != nil {
		t.Fatal(err)
	}
	current := reallocationCacheFixture(false)
	current.Name, current.Line = "current", 123
	current.Body = &ast.Identifier{Value: "current"}
	current.Signature = &ast.FunctionStatement{Name: &ast.Identifier{Value: "current"}}
	current.Constants = map[string]asm.Constant{"current": {Type: "u64", Value: 2}}
	current.Records = map[string]*ast.RecordLiteral{"record": {}}
	current.Callees = map[string]*ast.FunctionStatement{"callee": current.Signature}
	current.FrameObjects = []asm.FrameObject{{Offset: 99, Size: 99, Name: "metadata-only"}}
	current.Bindings = []asm.Binding{{Register: w(0), Param: "value"}}
	current.Compressed, current.System, current.Align = true, true, 64
	got, _, err := cache.Apply(current, nil)
	if err != nil {
		t.Fatal(err)
	}
	// Payloads may differ, but every other field must be the current
	// caller's shallow metadata, never the first request's AST or maps.
	metadata := *got
	metadata.Items, metadata.Clobbers = current.Items, current.Clobbers
	if !reflect.DeepEqual(&metadata, current) || got.Body != current.Body || got.Signature != current.Signature || cache.Stats().Hits != 1 {
		t.Fatal("hit reused old metadata or missed because of irrelevant syntax/maps")
	}
	got.Constants["shared"] = asm.Constant{Type: "u32", Value: 3}
	if _, shared := current.Constants["shared"]; !shared {
		t.Fatal("hit did not preserve the current caller's shallow metadata")
	}
}

func TestReallocationCacheDecisionInputsMiss(t *testing.T) {
	for _, kind := range []string{"arch", "frame", "items", "line", "call-site", "checked-facts", "clobbers", "objects", "empty-objects"} {
		t.Run(kind, func(t *testing.T) {
			var cache ReallocationCache
			first := reallocationCacheFixture(false)
			if _, _, err := cache.Apply(first, nil); err != nil {
				t.Fatal(err)
			}
			changed := reallocationCacheFixture(false)
			var objects []FrameObject
			switch kind {
			case "arch":
				changed.Arch = "" // equivalent lane, but distinct exact input
			case "frame":
				changed.Frame = 16
			case "items":
				changed.Items = append([]asm.Item{ins("nop")}, changed.Items...)
			case "line", "call-site", "checked-facts":
				instruction := changed.Items[1].(asm.Instruction)
				switch kind {
				case "line":
					instruction.Line = 77
				case "call-site":
					instruction.OptIRCallSite = 91
				case "checked-facts":
					instruction.CheckedFacts = []asm.CheckedFactRef{{ID: "other", Operand: 1}}
				}
				changed.Items[1] = instruction
			case "clobbers":
				changed.Clobbers[0], changed.Clobbers[1] = changed.Clobbers[1], changed.Clobbers[0]
			case "objects":
				objects = []FrameObject{{Offset: 0, Size: 4, Name: "words", Elem: 4}}
			case "empty-objects":
				objects = []FrameObject{}
			}
			got, summary, err := cache.Apply(changed, objects)
			if err != nil {
				t.Fatal(err)
			}
			want, allocation, err := ReallocateWith(changed, objects)
			if err != nil || !reflect.DeepEqual(got, want) || summary.Sites != allocation.Sites() || cache.Stats().Hits != 0 || cache.Stats().Entries != 2 {
				t.Fatalf("decision change did not miss cleanly: %v %+v", err, cache.Stats())
			}
		})
	}
}

type unsupportedCacheItem struct{ asm.Instruction }
type unsupportedCacheOperand struct{ asm.Register }

func TestReallocationCacheEncodingRegistry(t *testing.T) {
	seen := map[uint64]reflect.Type{}
	for typ, tag := range reallocationEncodingTypes {
		if tag == 0 || seen[tag] != nil {
			t.Fatalf("zero or duplicate type tag %d for %s and %v", tag, typ, seen[tag])
		}
		seen[tag] = typ
		if typ.Kind() == reflect.Struct && reallocationEncodingFields[typ] != typ.NumField() {
			t.Fatalf("%s field guard=%d, actual=%d", typ, reallocationEncodingFields[typ], typ.NumField())
		}
	}
	// Tags are uint64 throughout, with one positive contiguous identifier
	// per allowed type: no byte truncation or duplicate registry entry.
	for tag := uint64(1); tag <= uint64(len(reallocationEncodingTypes)); tag++ {
		if seen[tag] == nil {
			t.Fatalf("missing type tag %d (duplicate or narrowed registry entry)", tag)
		}
	}
	for typ := range reallocationEncodingFields {
		if _, allowed := reallocationEncodingTypes[typ]; !allowed {
			t.Fatalf("field guard for unregistered type %s", typ)
		}
	}
}

func TestReallocationCacheClosedEncoding(t *testing.T) {
	for _, unsupported := range []any{
		&asm.Function{}, &ast.Identifier{}, map[string]int{"x": 1},
		reallocationDecision{Items: []asm.Item{unsupportedCacheItem{}}},
		reallocationDecision{Items: []asm.Item{ins("mov", unsupportedCacheOperand{})}},
		reallocationDecision{Items: []asm.Item{ins("mov", &asm.Register{})}},
		reallocationDecision{Items: []asm.Item{ins("mov", (*asm.Register)(nil))}},
	} {
		if _, ok := encodeReallocation(unsupported, reallocationCacheBytes); ok {
			t.Fatalf("open traversal admitted %T", unsupported)
		}
	}
	operands := []asm.Operand{
		w(1), asm.Memory{Base: x(1), Index: func() *asm.Register { reg := w(2); return &reg }()},
		asm.RegisterList{Regs: []asm.Register{v(0, "4s")}}, imm(4), asm.FloatImmediate{Value: 1},
		sym("label"), asm.Condition{Code: "eq"}, asm.Option{Name: "ish", Mul: 2}, asm.SysReg{Name: "nzcv"},
		asm.Shifted{Reg: x(1), Kind: "lsl", Amount: 2}, asm.Extended{Reg: w(2), Kind: "uxtw", Amount: 2},
		asm.TileSlice{Text: "za", Tile: -1, Index: w(12), Count: 1},
	}
	items := []asm.Item{asm.Label{Name: "label", Line: 3}, asm.Align{Bytes: 16, Line: 4}, ins("closed-types", operands...)}
	if _, ok := encodeReallocation(reallocationDecision{Items: items}, reallocationCacheBytes); !ok {
		t.Fatal("known closed assembly type was rejected")
	}
	copied, _ := cloneReallocationPayload(items, nil)
	if !reflect.DeepEqual(copied, items) {
		t.Fatal("copying changed a value operand")
	}
}

func TestReallocationCacheCanonicalBytesAreExact(t *testing.T) {
	values := []any{
		asm.FloatImmediate{Value: 0}, asm.FloatImmediate{Value: math.Copysign(0, -1)},
		asm.FloatImmediate{Value: math.Float64frombits(0x7ff8000000000001)},
		asm.FloatImmediate{Value: math.Float64frombits(0x7ff8000000000002)},
		asm.Symbol{Name: "\xff"}, asm.Symbol{Name: "\xfe"}, asm.Symbol{Name: "\ufffd"},
		[]asm.Operand(nil), []asm.Operand{}, asm.Memory{}, asm.Memory{Index: &asm.Register{}},
		asm.Immediate{Value: 1}, asm.Immediate{Value: 1, Shift: 16}, asm.Immediate{Value: 1, MSL: true},
		asm.CheckedFactRef{ID: "a", Kind: "bc"}, asm.CheckedFactRef{ID: "ab", Kind: "c"},
	}
	seen := map[string]bool{}
	for _, value := range values {
		encoded, ok := encodeReallocation(value, reallocationCacheBytes)
		if !ok || seen[string(encoded)] {
			t.Fatalf("distinct raw value collided or refused: %T %+v", value, value)
		}
		seen[string(encoded)] = true
	}
}

func TestReallocationCacheDoesNotCacheErrors(t *testing.T) {
	for _, function := range []*asm.Function{
		fn(ins("not-a-machine-instruction")), fn(unsupportedCacheItem{}), fn(ins("mov", unsupportedCacheOperand{})), nil,
	} {
		var cache ReallocationCache
		for call := 0; call < 2; call++ {
			if _, _, err := cache.Apply(function, nil); err == nil {
				t.Fatal("invalid machine body succeeded")
			}
		}
		if stats := cache.Stats(); stats.Requests != 2 || stats.Hits != 0 || stats.Entries != 0 || stats.PayloadBytes != 0 {
			t.Fatalf("error retained a cache entry: %+v", stats)
		}
	}
}

func TestReallocationCacheEntryAndTraceLimits(t *testing.T) {
	var cache ReallocationCache
	for i := 0; i < reallocationCacheEntries+2; i++ {
		function := fn(ins("ret"))
		instruction := function.Items[0].(asm.Instruction)
		instruction.Line = i
		function.Items[0] = instruction
		if _, _, err := cache.Apply(function, nil); err != nil {
			t.Fatal(err)
		}
	}
	if stats := cache.Stats(); stats.Entries != reallocationCacheEntries || stats.Hits != 0 || stats.PayloadBytes > reallocationCacheBytes {
		t.Fatalf("entry cap exceeded: %+v", stats)
	}
	if _, _, err := cache.Apply(fn(ins("ret")), nil); err != nil || cache.Stats().Hits != 1 {
		t.Fatal("full cache stopped serving existing hits")
	}
	t.Setenv("OAK_MACHINE_TRACE_SLOTS", "1")
	if _, _, err := cache.Apply(fn(ins("ret")), nil); err != nil || cache.Stats().Hits != 1 {
		t.Fatal("trace mode reused a cached result")
	}
	var empty ReallocationCache
	if _, _, err := empty.Apply(fn(ins("ret")), nil); err != nil || empty.Stats().Entries != 0 {
		t.Fatal("trace mode retained a new result")
	}
}

func TestReallocationCachePayloadAndEncoderLimits(t *testing.T) {
	encoder := reallocationEncoder{limit: 64}
	if encoder.value(reflect.ValueOf(reallocationDecision{Arch: strings.Repeat("x", 1024)})) || len(encoder.bytes) > 64 || cap(encoder.bytes) > 64 {
		t.Fatal("encoder growth was not bounded before rejecting oversized input")
	}
	var cache ReallocationCache
	padding := strings.Repeat("x", 1<<20)
	for i := 0; i < 9; i++ {
		instruction := ins("ret")
		instruction.Line = i
		instruction.CheckedFacts = []asm.CheckedFactRef{{ID: padding}}
		if _, _, err := cache.Apply(fn(instruction), nil); err != nil {
			t.Fatal(err)
		}
	}
	if stats := cache.Stats(); stats.PayloadBytes > reallocationCacheBytes || stats.Entries == 0 || stats.Entries >= 9 {
		t.Fatalf("canonical input+output payload cap was not enforced: %+v", stats)
	}
	var oversized ReallocationCache
	instruction := ins("ret")
	instruction.CheckedFacts = []asm.CheckedFactRef{{ID: strings.Repeat("x", reallocationCacheBytes+1)}}
	if _, _, err := oversized.Apply(fn(instruction), nil); err != nil || oversized.Stats().Entries != 0 {
		t.Fatal("oversized input was cached or changed ordinary reallocation")
	}
}
