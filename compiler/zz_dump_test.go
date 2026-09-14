package compiler

import (
	"os"
	"testing"

	"github.com/SCKelemen/oak/target"
)

func TestZZDumpFloatLoops(t *testing.T) {
	src, _ := os.ReadFile(os.Getenv("OAK_PROBE_SRC"))
	for _, tgt := range []target.Target{{OS: target.OSDarwin, Arch: target.ArchArm64}, {OS: target.OSLinux, Arch: target.ArchRiscv64}} {
		comp := New().WithSource("p.oak", string(src)).WithNativeBodies().WithNativeAsm().WithTarget(tgt)
		if _, err := comp.EmitNative(ObjectFormat(tgt)).Get(); err != nil {
			t.Log(err)
		}
	}
}
