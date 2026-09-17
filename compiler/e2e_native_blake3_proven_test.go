package compiler

import (
	"strings"
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/nativegen"
	"github.com/SCKelemen/oak/target"
)

const nativeBlake3CompressName = "hash__blake3_ucompress"

func nativeBlake3Module(t *testing.T, inputs [][]byte) string {
	t.Helper()
	return writeModule(t, map[string]string{
		"oak.mod":  "module example.com/native_blake3_proven\noak 0.1.0\n",
		"main.oak": "package main\n" + blake3Program(inputs),
	})
}

// requireNativeBlake3StrongProfile admits only the two measured production
// shapes: complete constant unrolling with no residual loop, or the original
// two-loop lowering when that larger candidate is unavailable. The bounds are
// profile-specific so a third shape cannot pass by being merely smaller in one
// unrelated dimension.
func requireNativeBlake3StrongProfile(t *testing.T, selected *asm.Function) int {
	t.Helper()
	if selected == nil {
		t.Fatal("missing native compressor")
	}
	stackMemory, rotateAt := 0, -1
	for i, item := range selected.Items {
		instruction, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		if instruction.Mnemonic == "ror" && rotateAt < 0 {
			rotateAt = i
		}
		if strings.HasPrefix(instruction.Mnemonic, "ld") || strings.HasPrefix(instruction.Mnemonic, "st") {
			for _, operand := range instruction.Operands {
				if memory, ok := operand.(asm.Memory); ok && memory.Base.Class == asm.ClassSP {
					stackMemory++
				}
			}
		}
	}
	metrics := nativegen.Metrics(selected)
	full, small, promoted := nativegen.UnrolledConstant(selected), nativegen.UnrolledSmall(selected), nativegen.PromotedSlots(selected)
	if rotateAt < 0 || promoted == 0 {
		t.Fatalf("compressor lost its rotate or frame-word promotion: rotate=%d promoted=%d", rotateAt, promoted)
	}
	switch {
	case full > 0 && small == 0:
		if metrics.Loops != 0 || metrics.Instructions > 1175 || selected.Frame > 288 || stackMemory > 306 {
			t.Fatalf("fully unrolled compressor left its measured profile: full=%d loops=%d instructions=%d frame=%d SP-memory=%d promoted=%d",
				full, metrics.Loops, metrics.Instructions, selected.Frame, stackMemory, promoted)
		}
	case full == 0 && small == 0:
		if metrics.Loops != 2 || metrics.Instructions > 283 || selected.Frame > 160 || stackMemory > 10 {
			t.Fatalf("rolled compressor left its measured fallback profile: loops=%d instructions=%d frame=%d SP-memory=%d promoted=%d",
				metrics.Loops, metrics.Instructions, selected.Frame, stackMemory, promoted)
		}
	default:
		t.Fatalf("compressor selected an unpinned unroll profile: full=%d small=%d metrics=%s", full, small, metrics)
	}
	return rotateAt
}

// Exercise the real standard-library body, not a reduced quarter-round
// fixture: all seven rounds, six permutations, final derived indices, and
// every returned chunk must prove with the normal decision budget.
func TestNativeBlake3CompressionProven(t *testing.T) {
	t.Setenv("OAK_OPT_SKIP", "")
	t.Setenv("OAK_NATIVE_UNROLL_SMALL", "0")
	t.Setenv("OAK_NATIVE_LOOP_RESULT_HOMES", "0")
	t.Setenv("OAK_NATIVE_ONLY", nativeBlake3CompressName)
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	root := nativeBlake3Module(t, [][]byte{nil})
	comp := New().WithPackageDir(root).
		WithTarget(target.Target{OS: target.OSDarwin, Arch: target.ArchArm64}).
		WithNativeBodies().WithNativeAsm()
	comp.options.InlineHelpers = true // the configuration EmitNative selects
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	verdict, found := model.NativeVerdicts[nativeBlake3CompressName]
	if !found || verdict.Kind != asm.VerdictProven || !strings.Contains(verdict.Message, "all 8 result chunks") {
		t.Fatalf("real compressor must prove every chunk, got %s: %s", verdict.Kind, verdict.Message)
	}
	var selected *asm.Function
	for _, fn := range model.AsmFunctions {
		if fn.Name == nativeBlake3CompressName {
			selected = fn
			break
		}
	}
	if selected == nil || selected.Signature == nil {
		t.Fatal("missing native compressor or its source signature")
	}
	rotateAt := requireNativeBlake3StrongProfile(t, selected)
	if nativegen.UnrolledConstant(selected) == 0 {
		t.Fatal("default exact-trip costing did not select complete constant unrolling")
	}
	// Same legal instructions/footprint, wrong rotation: the normalization
	// must refute a changed computation rather than recognizing a hash name.
	changed := *selected
	changed.Items = append([]asm.Item(nil), selected.Items...)
	ins := changed.Items[rotateAt].(asm.Instruction)
	ins.Operands = append([]asm.Operand(nil), ins.Operands...)
	count, ok := ins.Operands[2].(asm.Immediate)
	if !ok {
		t.Fatal("expected fixed rotate count")
	}
	count.Value = (count.Value + 1) % 32
	ins.Operands[2] = count
	changed.Items[rotateAt] = ins
	if got := asm.Verify(&changed, selected.Signature, verifiedBody(selected, selected.Signature)); got.Kind != asm.VerdictMismatch {
		t.Fatalf("changed rotate must be refuted, got %s: %s", got.Kind, got.Message)
	}
}

// Only compression is native in this comparison; it is not a claim that
// the surrounding hash API or complete source-to-ASL path is proven.
func TestE2ENativeBlake3CompressionBoundaries(t *testing.T) {
	requireArm64Host(t)
	t.Setenv("OAK_NATIVE_ONLY", nativeBlake3CompressName)
	t.Setenv("OAK_VERIFY_CACHE", "0")
	var inputs [][]byte
	for _, size := range []int{0, 1, 63, 64, 65, 1023, 1024, 1025, 2048, 2049, 3072, 4096, 5000} {
		input := make([]byte, size)
		for i := range input {
			input[i] = byte(i % 251)
		}
		inputs = append(inputs, input)
	}
	root := nativeBlake3Module(t, inputs)
	for _, comp := range []Compilation{
		New().WithPackageDir(root).WithNativeBodies().WithNativeAsm(),
		New().WithPackageDir(root),
	} {
		if _, code, abnormal := buildAndRunFrom(t, "blake3_boundaries", comp); abnormal || code != 42 {
			t.Fatalf("hash boundary/reference checks failed: code=%d abnormal=%v", code, abnormal)
		}
	}
}
