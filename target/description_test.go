package target

import "testing"

func TestTargetDescription(t *testing.T) {
	for _, target := range Supported() {
		d, err := target.Describe()
		if err != nil || d.Validate() != nil || d.Target != target || d.NativeISA != target.AsmArch() {
			t.Fatalf("%s: %+v, %v", target, d, err)
		}
		i, p := target.DataModel()
		if d.PointerBits != p || d.ByteOrder != "little" || d.Container == "" || d.Environment == "" {
			t.Fatalf("incomplete description: %+v", d)
		}
		if target.CoreWasm() {
			if d.Backend != BackendWasm || d.Environment != "core-import-free" || d.Container != "wasm" || d.CIntBits != 0 {
				t.Fatalf("Wasm described as a C/hosted/native target: %+v", d)
			}
		} else if d.Backend != BackendC || d.CIntBits != i {
			t.Fatalf("C data model drift: %+v", d)
		}
		for _, mutate := range []func(*Description){
			func(d *Description) { d.PointerBits++ },
			func(d *Description) { d.NativeISA = "unknown" },
			func(d *Description) { d.Environment = "wasi" },
			func(d *Description) { d.ByteOrder = "big" },
			func(d *Description) { d.Container = "unknown" },
			func(d *Description) { d.Backend = "unknown" },
		} {
			bad := d
			mutate(&bad)
			if bad.Validate() == nil {
				t.Fatalf("forged description accepted: %+v", bad)
			}
		}
	}
	for _, bad := range []Target{{}, {OSLinux, "m68k"}, {"wasi", ArchWasm32}, {OSCore, ArchArm64}, {OSDarwin, ArchRiscv64}} {
		if d, err := bad.Describe(); err == nil || d != (Description{}) {
			t.Fatalf("unknown profile inherited defaults: %+v, %v", d, err)
		}
	}
}
