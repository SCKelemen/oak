package nativegen

import (
	"github.com/SCKelemen/oak/asm"
	"github.com/SCKelemen/oak/machine"
)

// CompileSession reuses deterministic allocation proposals across one
// function's candidate search. Its zero value is ready to use. It is scoped
// to that search, not shared globally or safe for concurrent use; it retains
// no verdicts or checked-source authority. Every candidate is still lowered
// independently and must pass the caller's usual admission and verification.
type CompileSession struct {
	allocations machine.ReallocationCache
}

// ReallocationStats reports proposal reuse, not proof-cache activity.
func (session *CompileSession) ReallocationStats() machine.ReallocationCacheStats {
	if session == nil {
		return machine.ReallocationCacheStats{}
	}
	return session.allocations.Stats()
}

func (session *CompileSession) reallocate(out *asm.Function) error {
	var cache *machine.ReallocationCache
	if session != nil {
		cache = &session.allocations
	}
	re, summary, err := cache.Apply(out, FrameObjects(out))
	if err != nil {
		return unsupported("%v", err)
	}
	// Keep the fresh candidate's source, signature, maps, and pointer-keyed
	// lowering metadata. Only this deterministic stage's payload is reused.
	out.Items, out.Clobbers = re.Items, re.Clobbers
	reallocated[out], promotedSlots[out] = summary.Sites, summary.Promoted
	return nil
}
