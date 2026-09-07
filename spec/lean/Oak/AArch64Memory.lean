import Oak.MemoryOrder

namespace Oak.AArch64Memory

open Oak.MemoryOrder

/-- The local ordering capabilities required/provided by one machine operation.
    RCsc acquire is tracked separately from acquire so LDAPR/RCpc cannot be
    silently accepted where Oak's OS profile requires LDAR-style RCsc acquire. -/
structure LocalOrdering where
  acquire : Bool
  release : Bool
  rcscAcquire : Bool
  deriving DecidableEq, Repr

def none : LocalOrdering := ⟨false, false, false⟩
def acquireRCsc : LocalOrdering := ⟨true, false, true⟩
def releaseOnly : LocalOrdering := ⟨false, true, false⟩
def acquireReleaseRCsc : LocalOrdering := ⟨true, true, true⟩

/-- Required local ordering for a legal Oak load. Sequential consistency has
    additional global constraints in Oak.SequentialConsistency; locally its load
    requires RCsc acquire. -/
def requiredLoad : Order -> Option LocalOrdering
  | .relaxed => some none
  | .acquire => some acquireRCsc
  | .seqCst => some acquireRCsc
  | .release | .acqRel => none

/-- Required local ordering for a legal Oak store. -/
def requiredStore : Order -> Option LocalOrdering
  | .relaxed => some none
  | .release => some releaseOnly
  | .seqCst => some releaseOnly
  | .acquire | .acqRel => none

/-- Required local ordering for RMW. RCsc acquire is required whenever the RMW
    has acquire semantics. -/
def requiredRMW : Order -> LocalOrdering
  | .relaxed => none
  | .acquire => acquireRCsc
  | .release => releaseOnly
  | .acqRel | .seqCst => acquireReleaseRCsc

/-- Required local ordering for fences. -/
def requiredFence : Order -> Option LocalOrdering
  | .acquire => some acquireRCsc
  | .release => some releaseOnly
  | .acqRel | .seqCst => some acquireReleaseRCsc
  | .relaxed => none

/-- A provided instruction class satisfies required local ordering when it
    contains every requested capability. -/
def satisfies (provided required : LocalOrdering) : Bool :=
  (!required.acquire || provided.acquire) &&
  (!required.release || provided.release) &&
  (!required.rcscAcquire || provided.rcscAcquire)

inductive LoadInstruction where
  | ldr
  | ldar
  | ldapr
  deriving DecidableEq, Repr

def loadProvided : LoadInstruction -> LocalOrdering
  | .ldr => none
  | .ldar => acquireRCsc
  | .ldapr => ⟨true, false, false⟩

inductive StoreInstruction where
  | str
  | stlr
  deriving DecidableEq, Repr

def storeProvided : StoreInstruction -> LocalOrdering
  | .str => none
  | .stlr => releaseOnly

inductive FenceInstruction where
  | dmbIshld
  | dmbIsh
  deriving DecidableEq, Repr

def fenceProvided : FenceInstruction -> LocalOrdering
  | .dmbIshld => acquireRCsc
  | .dmbIsh => acquireReleaseRCsc

inductive ExclusivePair where
  | ldxrStxr
  | ldaxrStxr
  | ldxrStlxr
  | ldaxrStlxr
  deriving DecidableEq, Repr

def exclusiveProvided : ExclusivePair -> LocalOrdering
  | .ldxrStxr => none
  | .ldaxrStxr => acquireRCsc
  | .ldxrStlxr => releaseOnly
  | .ldaxrStlxr => acquireReleaseRCsc

inductive LSEInstruction where
  | relaxed
  | acquire
  | release
  | acqRel
  deriving DecidableEq, Repr

def lseProvided : LSEInstruction -> LocalOrdering
  | .relaxed => none
  | .acquire => acquireRCsc
  | .release => releaseOnly
  | .acqRel => acquireReleaseRCsc

/-- Baseline AArch64 load profile used by Oak's backend evidence gate. -/
def baselineLoad : Order -> Option LoadInstruction
  | .relaxed => some .ldr
  | .acquire | .seqCst => some .ldar
  | .release | .acqRel => none

/-- Baseline AArch64 store profile. -/
def baselineStore : Order -> Option StoreInstruction
  | .relaxed => some .str
  | .release | .seqCst => some .stlr
  | .acquire | .acqRel => none

/-- Baseline fences. -/
def baselineFence : Order -> Option FenceInstruction
  | .acquire => some .dmbIshld
  | .release | .acqRel | .seqCst => some .dmbIsh
  | .relaxed => none

/-- The current base ARMv8 evidence gate checks relaxed and acquire-release/SC
    RMW families explicitly. -/
def baselineRMW : Order -> ExclusivePair
  | .relaxed => .ldxrStxr
  | .acquire => .ldaxrStxr
  | .release => .ldxrStlxr
  | .acqRel | .seqCst => .ldaxrStlxr

/-- LSE profile: LDADD/CAS suffix classes encode the same four local strengths. -/
def lseRMW : Order -> LSEInstruction
  | .relaxed => .relaxed
  | .acquire => .acquire
  | .release => .release
  | .acqRel | .seqCst => .acqRel

theorem baseline_loads_satisfy_local_order (o : Order)
    (required : LocalOrdering) (instruction : LoadInstruction)
    (hRequired : requiredLoad o = some required)
    (hInstruction : baselineLoad o = some instruction) :
    satisfies (loadProvided instruction) required = true := by
  cases o <;> simp_all [requiredLoad, baselineLoad, loadProvided, satisfies,
    none, acquireRCsc]

theorem baseline_stores_satisfy_local_order (o : Order)
    (required : LocalOrdering) (instruction : StoreInstruction)
    (hRequired : requiredStore o = some required)
    (hInstruction : baselineStore o = some instruction) :
    satisfies (storeProvided instruction) required = true := by
  cases o <;> simp_all [requiredStore, baselineStore, storeProvided, satisfies,
    none, releaseOnly]

theorem baseline_fences_satisfy_local_order (o : Order)
    (required : LocalOrdering) (instruction : FenceInstruction)
    (hRequired : requiredFence o = some required)
    (hInstruction : baselineFence o = some instruction) :
    satisfies (fenceProvided instruction) required = true := by
  cases o <;> simp_all [requiredFence, baselineFence, fenceProvided, satisfies,
    acquireRCsc, releaseOnly, acquireReleaseRCsc]

theorem baseline_rmw_satisfies_local_order (o : Order) :
    satisfies (exclusiveProvided (baselineRMW o)) (requiredRMW o) = true := by
  cases o <;> rfl

theorem lse_rmw_satisfies_local_order (o : Order) :
    satisfies (lseProvided (lseRMW o)) (requiredRMW o) = true := by
  cases o <;> rfl

/-- RCpc LDAPR has acquire semantics but is intentionally insufficient for the
    Oak AArch64 OS profile's acquire requirement. -/
theorem ldapr_does_not_satisfy_oak_acquire :
    satisfies (loadProvided .ldapr) acquireRCsc = false := rfl

theorem ldar_satisfies_oak_acquire :
    satisfies (loadProvided .ldar) acquireRCsc = true := rfl

/-- Seq-cst's global total-order/read-visibility obligations are not discharged
    by this local instruction mapping. This theorem records only the local load
    component; Oak.SequentialConsistency remains a separate proof obligation. -/
theorem seqCst_load_uses_rcsc_acquire : baselineLoad .seqCst = some .ldar := rfl

theorem seqCst_store_uses_release : baselineStore .seqCst = some .stlr := rfl

theorem seqCst_fence_uses_full_dmb : baselineFence .seqCst = some .dmbIsh := rfl

end Oak.AArch64Memory
