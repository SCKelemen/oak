package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/ast"
	"github.com/SCKelemen/oak/nativegen"
)

const nativeArrayResultProgram = `
literal_words: (x: u32): [8]u32 {
  out: [8]u32 = [8]u32{ x, x + u32(1), x + u32(2), x + u32(3), x + u32(4), x + u32(5), x + u32(6), x + u32(7) }
  out[0] = out[0] + x
  out
}

zero_words: (x: u32): [6]u32 {
  out: [6]u32
  out[5] = x
  out
}

copy_words: (input: [8]u32): [8]u32 {
  out: [8]u32 = input
  out[0] = input[7]
  out[7] = input[0]
  out
}

signed_words: (x: i64): [3]i64 {
  out: [3]i64 = [3]i64{ x, x + i64(1), -x }
  out
}

// The loop prevents both inliners from replacing this call with a body.
scalar_step: (x: u32): u32 {
  total: u32 = x
  i: u32 = u32(0)
  while i < u32(3) {
    total = total + i
    i = i + u32(1)
  }
  total
}

call_live_words: (x: u32): [8]u32 {
  out: [8]u32
  out[0] = x
  stepped: u32 = scalar_step(x)
  out[7] = stepped + out[0]
  out
}

loop_words: (input: [8]u32, by: u32): [8]u32 {
  out: [8]u32 = input
  i: u32 = u32(0)
  while i < u32(8) {
    out[i] = out[i] + by
    i = i + u32(1)
  }
  out
}

relay_words: (input: [8]u32): [8]u32 {
  out: [8]u32 = loop_words(input, u32(3))
  out[1] = out[0] + input[1]
  out
}

permuted_words: (input: [8]u32): [8]u32 {
  out: [8]u32 = input
  out = [8]u32{ out[1], out[0], out[3], out[2], out[5], out[4], out[7], out[6] }
  out
}

replaced_words: (input: [8]u32): [8]u32 {
  out: [8]u32 = input
  out = loop_words(out, u32(2))
  out
}

parameter_words: (input: [8]u32): [8]u32 = input

borrowed_words: (x: u32): [8]u32 {
  out: [8]u32
  true ? {
    view_out: [*]u32 = span(&out)
    view_out[0] = x
  } | { }
  out
}

main: (): i32 {
  words: [8]u32 = literal_words(u32(10))
  assert(words[0] == u32(20) && words[7] == u32(17))
  words = copy_words(words)
  assert(words[0] == u32(17) && words[7] == u32(20) && words[1] == u32(11))
  words = loop_words(words, u32(2))
  assert(words[0] == u32(19) && words[7] == u32(22))
  words = relay_words(words)
  assert(words[0] == u32(22) && words[1] == u32(35) && words[7] == u32(25))
  copy: [8]u32 = parameter_words(words)
  assert(copy[0] == words[0] && copy[7] == words[7])
  permuted: [8]u32 = permuted_words(words)
  assert(permuted[0] == words[1] && permuted[1] == words[0] && permuted[6] == words[7])
  replaced: [8]u32 = replaced_words(words)
  assert(replaced[0] == words[0] + u32(2) && replaced[7] == words[7] + u32(2))
  zeros: [6]u32 = zero_words(u32(42))
  assert(zeros[0] == u32(0) && zeros[4] == u32(0) && zeros[5] == u32(42))
  signed: [3]i64 = signed_words(i64(-7))
  assert(signed[0] == i64(-7) && signed[1] == i64(-6) && signed[2] == i64(7))
  called: [8]u32 = call_live_words(u32(11))
  assert(called[0] == u32(11) && called[1] == u32(0) && called[7] == u32(25))
  borrowed: [8]u32 = borrowed_words(u32(42))
  assert(borrowed[0] == u32(42) && borrowed[7] == u32(0))
  42
}
`

func TestE2ENativeArrayResultStorage(t *testing.T) {
	requireArm64Host(t)
	comp := New().WithSource("array_result.oak", nativeArrayResultProgram).WithNativeBodies().WithNativeAsm()
	model, err := comp.Check().Get()
	if err != nil {
		t.Fatal(err)
	}
	functions := map[string]*ast.FunctionStatement{}
	symbols := map[string]bool{}
	for _, statement := range model.Tree.Root.Statements {
		if function, ok := statement.(*ast.FunctionStatement); ok {
			functions[function.Name.Value] = function
			symbols[function.Name.Value] = true
		}
	}
	for _, name := range []string{"literal_words", "zero_words", "copy_words", "signed_words", "permuted_words", "call_live_words"} {
		if verdict := model.NativeVerdicts[name]; verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s selected verdict = %s (%s), want proven", name, verdict.Kind, verdict.Message)
		}
		source := functions[name]
		if source == nil {
			t.Fatalf("missing %s source", name)
		}
		body, err := nativegen.CompileFor(nativegen.Lane{Arch: asm.ArchArm64}, source, functions, nil, nil, nil, model.TypeChecker)
		if err != nil {
			t.Fatalf("%s direct lowering: %v", name, err)
		}
		// Native search attaches the program's checked callee bodies before
		// admission and verification; direct candidates need that context too.
		body.Callees = functions
		if findings := asm.Check(body, source, symbols); len(findings) != 0 {
			t.Fatalf("%s direct admission: %v", name, findings)
		}
		if verdict := asm.Verify(body, source, source.Body); verdict.Kind != asm.VerdictProven {
			t.Fatalf("%s direct verdict = %s (%s), want proven", name, verdict.Kind, verdict.Message)
		}
		if name == "call_live_words" {
			calls := 0
			for _, item := range body.Items {
				if instruction, ok := item.(asm.Instruction); ok && instruction.Mnemonic == "bl" {
					calls++
				}
			}
			if calls != 1 {
				t.Fatalf("result-pointer lifetime fixture must retain one native call, got %d", calls)
			}
		}
		objects := nativegen.FrameObjects(body)
		if name == "permuted_words" {
			if len(objects) != 1 || objects[0].Size != 32 {
				t.Fatalf("permutation must keep its one frame array, without a temporary copy: %+v", objects)
			}
		} else if len(objects) != 0 {
			t.Fatalf("%s still allocates array frame backing: %+v", name, objects)
		}
	}
	for _, name := range []string{"loop_words", "relay_words", "parameter_words", "borrowed_words", "replaced_words"} {
		verdict, present := model.NativeVerdicts[name]
		if !present || (verdict.Kind != asm.VerdictProven && verdict.Kind != asm.VerdictWitnessed) {
			t.Fatalf("%s lost native verification: %s (%s)", name, verdict.Kind, verdict.Message)
		}
	}
	_, native, abnormal := buildAndRunFrom(t, "native_array_result", comp)
	_, viaC, abnormalC := buildAndRunFrom(t, "native_array_result_c", New().WithSource("array_result.oak", nativeArrayResultProgram))
	if abnormal || abnormalC || native != 42 || viaC != 42 {
		t.Fatalf("native %d (abnormal %v), C %d (abnormal %v); want 42", native, abnormal, viaC, abnormalC)
	}
}
