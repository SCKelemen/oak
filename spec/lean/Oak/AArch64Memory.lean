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

def unordered : LocalOrdering := ⟨false, false, false⟩
def acquireRCsc : LocalOrdering := ⟨true, false, true⟩
def releaseOnly : LocalOrdering := ⟨false, true, false⟩
def acquireReleaseRCsc : LocalOrdering := ⟨true, true, true⟩

/-- Required local ordering for a legal Oak load. Sequential consistency has
    additional global constraints in Oak.SequentialConsistency; locally its load
    requires RCsc acquire. -/
def requiredLoad : Order -> Option LocalOrdering
  | .relaxed => some unordered
  | .acquire => some acquireRCsc
  | .seqCst => some acquireRCsc
  | .release | .acqRel => Option.none

/-- Required local ordering for a legal Oak store. -/
def requiredStore : Order -> Option LocalOrdering
  | .relaxed => some unordered
  | .release => some releaseOnly
  | .seqCst => some releaseOnly
  | .acquire | .acqRel => Option.none

/-- Required local ordering for RMW. RCsc acquire is required whenever the RMW
    has acquire semantics. -/
def requiredRMW : Order -> LocalOrdering
  | .relaxed => unordered
  | .acquire => acquireRCsc
  | .release => releaseOnly
  | .acqRel | .seqCst => acquireReleaseRCsc

/-- Required local ordering for fences. -/
def requiredFence : Order -> Option LocalOrdering
  | .acquire => some acquireRCsc
  | .release => some releaseOnly
  | .acqRel | .seqCst => some acquireReleaseRCsc
  | .relaxed => Option.none

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
  | .ldr => unordered
  | .ldar => acquireRCsc
  | .ldapr => ⟨true, false, false⟩

inductive StoreInstruction where
  | str
  | stlr
  deriving DecidableEq, Repr

def storeProvided : StoreInstruction -> LocalOrdering
  | .str => unordered
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
  | .ldxrStxr => unordered
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
  | .relaxed => unordered
  | .acquire => acquireRCsc
  | .release => releaseOnly
  | .acqRel => acquireReleaseRCsc

/-- Baseline AArch64 load profile used by Oak's backend evidence gate. -/
def baselineLoad : Order -> Option LoadInstruction
  | .relaxed => some .ldr
  | .acquire | .seqCst => some .ldar
  | .release | .acqRel => Option.none

/-- Baseline AArch64 store profile. -/
def baselineStore : Order -> Option StoreInstruction
  | .relaxed => some .str
  | .release | .seqCst => some .stlr
  | .acquire | .acqRel => Option.none

/-- Baseline fences. -/
def baselineFence : Order -> Option FenceInstruction
  | .acquire => some .dmbIshld
  | .release | .acqRel | .seqCst => some .dmbIsh
  | .relaxed => Option.none

/-- The base ARMv8 profile for all RMW order strengths. -/
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

/-- A total checker for the load profile. Illegal load orders are accepted only
    when both the requirement and machine mapping are absent. -/
def baselineLoadProfileValid (o : Order) : Bool :=
  match requiredLoad o, baselineLoad o with
  | some required, some instruction => satisfies (loadProvided instruction) required
  | Option.none, Option.none => true
  | _, _ => false

/-- A total checker for the store profile. -/
def baselineStoreProfileValid (o : Order) : Bool :=
  match requiredStore o, baselineStore o with
  | some required, some instruction => satisfies (storeProvided instruction) required
  | Option.none, Option.none => true
  | _, _ => false

/-- A total checker for the fence profile. -/
def baselineFenceProfileValid (o : Order) : Bool :=
  match requiredFence o, baselineFence o with
  | some required, some instruction => satisfies (fenceProvided instruction) required
  | Option.none, Option.none => true
  | _, _ => false

theorem baseline_load_profile_valid (o : Order) :
    baselineLoadProfileValid o = true := by
  cases o <;> rfl

theorem baseline_store_profile_valid (o : Order) :
    baselineStoreProfileValid o = true := by
  cases o <;> rfl

theorem baseline_fence_profile_valid (o : Order) :
    baselineFenceProfileValid o = true := by
  cases o <;> rfl

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
    by this local instruction mapping. These record only local components;
    Oak.SequentialConsistency remains the separate global proof obligation. -/
theorem seqCst_load_uses_rcsc_acquire : baselineLoad .seqCst = some .ldar := rfl

theorem seqCst_store_uses_release : baselineStore .seqCst = some .stlr := rfl

theorem seqCst_fence_uses_full_dmb : baselineFence .seqCst = some .dmbIsh := rfl

end Oak.AArch64Memory
