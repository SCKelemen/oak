package object

import (
	"fmt"
	"sync/atomic"
)

const ATOMIC_CELL_OBJ ObjectType = "ATOMIC_CELL"

// AtomicCell is evaluator-only storage identity for Atomic[T]. The interpreter
// currently represents every Oak integer as int64, so the reference evaluator
// stores that carrier while the native backend preserves the exact fixed width.
// There is no secondary heap object per operation: loads/stores/RMW mutate this
// one cell in place.
type AtomicCell struct {
	Value atomic.Int64
}

func (a *AtomicCell) Type() ObjectType { return ATOMIC_CELL_OBJ }
func (a *AtomicCell) Inspect() string {
	if a == nil {
		return "Atomic[?](nil)"
	}
	return fmt.Sprintf("Atomic(%d)", a.Value.Load())
}
