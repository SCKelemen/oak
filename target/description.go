package target

import "fmt"

// Backend describes the compiler output route, not its proof coverage.
type Backend string

const (
	BackendC    Backend = "c"
	BackendWasm Backend = "wasm"
)

// Description separates architecture, execution environment and output route.
// It is a value-only baseline description, not a CPU-feature/ABI manifest or
// permission to emit a verified program. NativeISA names an implemented Oak
// assembler lane; empty means no native lane, not an AArch64 default.
type Description struct {
	Target      Target  `json:"target"`
	Backend     Backend `json:"backend"`
	Environment string  `json:"environment"`
	Container   string  `json:"container"`
	NativeISA   string  `json:"nativeISA,omitempty"`
	CIntBits    int     `json:"cIntBits,omitempty"`
	PointerBits int     `json:"pointerBits"`
	ByteOrder   string  `json:"byteOrder"`
}

// Describe fails closed even when a Target was constructed without Parse.
// Keep the switches exhaustive: adding a spelling alone must not silently
// inherit another architecture's widths, object format or native semantics.
func (t Target) Describe() (Description, error) {
	if !t.Supported() {
		return Description{}, fmt.Errorf("target %s is not supported", t)
	}
	d := Description{Target: t, Backend: BackendC, CIntBits: 32, ByteOrder: "little"}
	switch t.Arch {
	case ArchArm64:
		d.PointerBits, d.NativeISA = 64, "arm64"
	case ArchRiscv64:
		d.PointerBits, d.NativeISA = 64, "rv64"
	case ArchAmd64:
		d.PointerBits = 64
	case ArchArm, ArchRiscv32:
		d.PointerBits = 32
	case ArchWasm32:
		d.PointerBits, d.CIntBits, d.Backend = 32, 0, BackendWasm
	default:
		return Description{}, fmt.Errorf("target %s has no architecture description", t)
	}
	switch t.OS {
	case OSLinux:
		d.Environment, d.Container = "hosted", "elf"
	case OSDarwin:
		d.Environment, d.Container = "hosted", "macho"
	case OSFreestanding:
		d.Environment, d.Container = "freestanding", "elf"
	case OSCore:
		d.Environment, d.Container = "core-import-free", "wasm"
	default:
		return Description{}, fmt.Errorf("target %s has no environment description", t)
	}
	return d, nil
}

// Validate rejects stale or caller-forged descriptions at pipeline boundaries.
func (d Description) Validate() error {
	want, err := d.Target.Describe()
	if err != nil {
		return err
	}
	if d != want {
		return fmt.Errorf("target %s description does not match its registered profile", d.Target)
	}
	return nil
}
