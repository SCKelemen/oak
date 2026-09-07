package semir

import "fmt"

// MmioAccess is the static authority carried by an MMIO register handle.
// There is deliberately no dynamic access-mode field on the runtime path.
type MmioAccess string

const (
	MmioReadOnly  MmioAccess = "read-only"
	MmioWriteOnly MmioAccess = "write-only"
	MmioReadWrite MmioAccess = "read-write"
)

func (a MmioAccess) CanRead() bool {
	return a == MmioReadOnly || a == MmioReadWrite
}

func (a MmioAccess) CanWrite() bool {
	return a == MmioWriteOnly || a == MmioReadWrite
}

// MmioWidth is the exact observable machine access width.
type MmioWidth uint8

const (
	Mmio8  MmioWidth = 8
	Mmio16 MmioWidth = 16
	Mmio32 MmioWidth = 32
	Mmio64 MmioWidth = 64
)

func (w MmioWidth) Bytes() uint64 { return uint64(w) / 8 }

func (w MmioWidth) Carrier() string {
	switch w {
	case Mmio8:
		return "u8"
	case Mmio16:
		return "u16"
	case Mmio32:
		return "u32"
	case Mmio64:
		return "u64"
	default:
		return ""
	}
}

func (w MmioWidth) Valid() bool { return w.Carrier() != "" }

// MmioAddressAligned is the v1 constructor proof obligation. Device-memory
// attributes and mapping authority are separate assumptions; this predicate
// proves only that an access of the declared width is naturally aligned.
func MmioAddressAligned(address uint64, width MmioWidth) bool {
	return width.Valid() && address%width.Bytes() == 0
}

type MmioOperation string

const (
	MmioConstruct MmioOperation = "construct"
	MmioRead      MmioOperation = "read"
	MmioWrite     MmioOperation = "write"
)

// MmioSpec is the one semantic catalog row shared by type checking, effects,
// code generation, tests, and documentation projections.
type MmioSpec struct {
	Member    string
	Operation MmioOperation
	Width     MmioWidth
	Access    MmioAccess
	Arity     uint8
}

func (s MmioSpec) Legal() bool {
	if !s.Width.Valid() {
		return false
	}
	switch s.Operation {
	case MmioConstruct:
		return s.Arity == 1
	case MmioRead:
		return s.Arity == 1 && s.Access.CanRead()
	case MmioWrite:
		return s.Arity == 2 && s.Access.CanWrite()
	default:
		return false
	}
}

func (s MmioSpec) Effect() (Effect, error) {
	if !s.Legal() {
		return Effect{}, fmt.Errorf("illegal MMIO specification %q", s.Member)
	}
	switch s.Operation {
	case MmioConstruct:
		return Effect{Namespace: "Machine", Name: "AssumeMmioRegister", Parameters: []string{s.Width.Carrier(), string(s.Access)}}, nil
	case MmioRead:
		return Effect{Namespace: "Memory", Name: "MMIORead", Parameters: []string{s.Width.Carrier()}}, nil
	case MmioWrite:
		return Effect{Namespace: "Memory", Name: "MMIOWrite", Parameters: []string{s.Width.Carrier()}}, nil
	default:
		return Effect{}, fmt.Errorf("unknown MMIO operation %q", s.Operation)
	}
}

func mmioMember(op string, access MmioAccess, carrier string) string {
	accessName := ""
	switch access {
	case MmioReadOnly:
		accessName = "ro"
	case MmioWriteOnly:
		accessName = "wo"
	case MmioReadWrite:
		accessName = "rw"
	}
	return "mmio_" + op + "_" + accessName + "_" + carrier
}

var mmioCatalog = func() []MmioSpec {
	widths := []MmioWidth{Mmio8, Mmio16, Mmio32, Mmio64}
	accesses := []MmioAccess{MmioReadOnly, MmioWriteOnly, MmioReadWrite}
	out := make([]MmioSpec, 0, 28)
	for _, width := range widths {
		carrier := width.Carrier()
		for _, access := range accesses {
			out = append(out, MmioSpec{Member: "mmio_unsafe_" + string(map[MmioAccess]string{MmioReadOnly: "ro", MmioWriteOnly: "wo", MmioReadWrite: "rw"}[access]) + "_" + carrier, Operation: MmioConstruct, Width: width, Access: access, Arity: 1})
			if access.CanRead() {
				out = append(out, MmioSpec{Member: mmioMember("read", access, carrier), Operation: MmioRead, Width: width, Access: access, Arity: 1})
			}
			if access.CanWrite() {
				out = append(out, MmioSpec{Member: mmioMember("write", access, carrier), Operation: MmioWrite, Width: width, Access: access, Arity: 2})
			}
		}
	}
	return out
}()

// Arm64MmioMembers returns a copy so callers cannot mutate the language catalog.
func Arm64MmioMembers() []MmioSpec {
	out := make([]MmioSpec, len(mmioCatalog))
	copy(out, mmioCatalog)
	return out
}

// LookupArm64Mmio uses a bounded scan of a compile-time-sized catalog. This is
// compiler-side only; generated MMIO operations contain no lookup/dispatch.
func LookupArm64Mmio(member string) (MmioSpec, bool) {
	for i := range mmioCatalog {
		if mmioCatalog[i].Member == member {
			return mmioCatalog[i], true
		}
	}
	return MmioSpec{}, false
}
