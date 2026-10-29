package optir

import (
	"math"
	"reflect"
	"testing"
)

func TestStatefulExecutionCopyShortEmptyAndFrames(t *testing.T) {
	p := statefulProfileFixture(t)
	for length := uint32(0); length <= 8; length++ {
		for capacity := uint32(0); capacity <= 10; capacity++ {
			for _, sharedBacking := range []bool{false, true} {
				// When sharedBacking is true both disjoint views lie in one contiguous
				// initialized owner-shaped backing. Owner/grant validity itself is a Lean
				// Invocation premise, not inferred by this finite memory model.
				dstBase, srcBase := uint64(120), uint64(1000)
				if sharedBacking {
					srcBase = 104
				}
				memory := StatefulMemory{}
				for i := uint64(99); i < 140; i++ {
					memory[i] = uint8(i * 17)
				}
				if !sharedBacking {
					for i := uint64(998); i < 1020; i++ {
						memory[i] = uint8(i)
					}
				}
				bytes := []uint8{0, 128, 255, 1, 0, 254, 129, 42}
				for i := uint32(0); i < length; i++ {
					memory[srcBase+uint64(i)] = bytes[i]
				}
				before := cloneStatefulMemory(memory)
				got, err := ExecuteStatefulProgram(p, StatefulDescriptor{dstBase, capacity}, StatefulDescriptor{srcBase, length}, memory, 1000)
				if err != nil {
					t.Fatal(err)
				}
				if got.Outcome != StatefulReturned || got.Value.Type != TypeBool || len(got.Calls) != 1 {
					t.Fatalf("n=%d capacity=%d shared=%v: %+v", length, capacity, sharedBacking, got)
				}
				result := got.Calls[0].Value
				if result.Type != TypeCopyResult || result.Payload == nil {
					t.Fatal("call omitted real concrete Result/payload")
				}
				expected := cloneStatefulMemory(before)
				if capacity < length {
					if got.Value.Bool || result.Variant != string(TypeCopyResult)+".Err" || result.Payload.Type != TypeCopyError || result.Payload.Variant != string(TypeCopyError)+".DestinationTooSmall" || result.Payload.Payload != nil {
						t.Fatal("short capacity did not return exact nested error")
					}
				} else {
					if !got.Value.Bool || result.Variant != string(TypeCopyResult)+".Ok" || result.Payload.Type != "u32" || result.Payload.Uint != length {
						t.Fatal("successful copy lost count or caller saved length")
					}
					for i := uint32(0); i < length; i++ {
						expected[dstBase+uint64(i)] = before[srcBase+uint64(i)]
					}
				}
				if !reflect.DeepEqual(got.Memory, expected) {
					t.Fatalf("wrong byte update/frame n=%d capacity=%d shared=%v", length, capacity, sharedBacking)
				}
				if !reflect.DeepEqual(memory, before) {
					t.Fatal("executor mutated caller-owned input map")
				}
				if _, mapped := got.Memory[99999]; mapped {
					t.Fatal("executor allocated unmapped external memory")
				}
			}
		}
	}
}

func TestStatefulExecutionFuelIsSeparateFromResult(t *testing.T) {
	p := statefulProfileFixture(t)
	for _, test := range []struct{ src, dst uint32 }{{0, 0}, {1, 0}, {3, 5}} {
		memory := StatefulMemory{10: 128, 11: 0, 12: 255, 20: 1, 21: 1, 22: 1, 23: 1, 24: 1}
		dst, src := StatefulDescriptor{20, test.dst}, StatefulDescriptor{10, test.src}
		complete, err := ExecuteStatefulProgram(p, dst, src, memory, 1000)
		if err != nil || complete.Outcome != StatefulReturned {
			t.Fatalf("%+v %v", complete, err)
		}
		exact, err := ExecuteStatefulProgram(p, dst, src, memory, complete.Steps)
		if err != nil || exact.Outcome != StatefulReturned || exact.Steps != complete.Steps {
			t.Fatal("exact IR fuel does not terminate")
		}
		for fuel := uint64(0); fuel < complete.Steps; fuel++ {
			short, err := ExecuteStatefulProgram(p, dst, src, memory, fuel)
			if err != nil || short.Outcome != StatefulExhausted || short.Steps != fuel || short.Fault != "" {
				t.Fatalf("fuel %d produced %s / %s instead of exhaustion (%v)", fuel, short.Outcome, short.Fault, err)
			}
		}
	}
}

func TestStatefulExecutionFaultsOnInvalidByteMemory(t *testing.T) {
	p := statefulProfileFixture(t)
	tests := []struct {
		name     string
		dst, src StatefulDescriptor
		memory   StatefulMemory
	}{
		{"unmapped-read", StatefulDescriptor{20, 1}, StatefulDescriptor{10, 1}, StatefulMemory{20: 0}},
		{"uninitialized-write", StatefulDescriptor{20, 1}, StatefulDescriptor{10, 1}, StatefulMemory{10: 7}},
		{"source-address-wrap", StatefulDescriptor{20, 2}, StatefulDescriptor{math.MaxUint64, 2}, StatefulMemory{math.MaxUint64: 7, 20: 0, 21: 0}},
		{"destination-address-wrap", StatefulDescriptor{math.MaxUint64, 2}, StatefulDescriptor{10, 2}, StatefulMemory{math.MaxUint64: 0, 10: 7, 11: 8}},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			got, err := ExecuteStatefulProgram(p, test.dst, test.src, test.memory, 1000)
			if err != nil || got.Outcome != StatefulFault || got.Fault == "" {
				t.Fatalf("%+v %v", got, err)
			}
		})
	}
}

func TestStatefulExecutionInactivePayloadFault(t *testing.T) {
	// The closed typing/effect profile permits a potentially faulting projection;
	// the separate copy translation validator must prove the accepted source graph
	// takes it only under its matching branch. Never turn a wrong variant into an
	// arbitrary count or a DestinationTooSmall result.
	p := statefulProfileFixture(t)
	functions := p.Functions()
	for i := range functions {
		if functions[i].Structured.Name == p.Root() {
			functions[i].Structured.Body.Nodes[2].Operation.Attributes[0].Value = string(TypeCopyResult) + ".Err"
			cfg, err := Project(functions[i].Structured)
			if err != nil {
				t.Fatal(err)
			}
			functions[i].CFG = cfg
		}
	}
	changed, err := NewStatefulProgram(p.Root(), functions, p.Types(), p.ByteAccesses(), p.Calls())
	if err != nil {
		t.Fatal(err)
	}
	got, err := ExecuteStatefulProgram(changed, StatefulDescriptor{20, 0}, StatefulDescriptor{10, 1}, StatefulMemory{10: 7}, 1000)
	if err != nil || got.Outcome != StatefulFault || got.Fault != "inactive ADT payload projection" {
		t.Fatalf("%+v %v", got, err)
	}
}
