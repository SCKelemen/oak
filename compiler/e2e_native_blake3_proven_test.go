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

// Exercise the real standard-library body, not a reduced quarter-round
// fixture: all seven rounds, six permutations, final derived indices, and
// every returned chunk must prove with the normal decision budget.
func TestNativeBlake3CompressionProven(t *testing.T) {
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
	stackMemory, rotateAt := 0, -1
	for i, item := range selected.Items {
		ins, ok := item.(asm.Instruction)
		if !ok {
			continue
		}
		if ins.Mnemonic == "ror" && rotateAt < 0 {
			rotateAt = i
		}
		if strings.HasPrefix(ins.Mnemonic, "ld") || strings.HasPrefix(ins.Mnemonic, "st") {
			for _, operand := range ins.Operands {
				if mem, ok := operand.(asm.Memory); ok && mem.Base.Class == asm.ClassSP {
					stackMemory++
				}
			}
		}
	}
	if rotateAt < 0 || selected.Frame > 144 || stackMemory > 32 || nativegen.PromotedSlots(selected) == 0 {
		t.Fatalf("proof must retain frame-word promotion: rotate=%d frame=%d stack memory=%d promoted=%d",
			rotateAt, selected.Frame, stackMemory, nativegen.PromotedSlots(selected))
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
