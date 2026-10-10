package compiler

import (
	"testing"

	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/target"
)

// The full update must prove even on a non-ARM host. Native execution and
// reference digests remain required by TestE2ENativeBlake3PackageAgreesWithReference.
// Partial helper inlining must not make equivalent call summaries opaque to
// one another and send this ordinary-budget proof back to witness evidence.
func TestNativeBlake3UpdateProven(t *testing.T) {
	t.Setenv("OAK_OPT_SKIP", "")
	t.Setenv("OAK_NATIVE_ONLY", "hash__blake3_uupdate")
	t.Setenv("OAK_VERIFY_CACHE", "0")
	t.Setenv("OAK_VERIFY_BUDGET", "")
	root := writeModule(t, map[string]string{
		"oak.mod": "module example.com/native_blake3_update_probe\noak 0.1.0\n",
		"main.oak": `package main
import("hash")
main: (): i32 {
  bytes: [1]u8
  state: hash.Blake3State = hash.blake3_update(hash.blake3_init(), view(&bytes))
  state.block_len == u32(1) ? 42 | 1
}
`,
	})
	comp := New().WithPackageDir(root).
		WithTarget(target.Target{OS: target.OSLinux, Arch: target.ArchArm64}).
		WithNativeBodies().WithNativeAsm()
	comp.options.InlineHelpers = true
	model, err := comp.SemanticModel().Get()
	if err != nil {
		t.Fatal(err)
	}
	verdict, ok := model.NativeVerdicts["hash__blake3_uupdate"]
	if !ok || verdict.Kind != asm.VerdictProven {
		t.Fatalf("complete update must prove: present=%v kind=%s message=%s", ok, verdict.Kind, verdict.Message)
	}
}
