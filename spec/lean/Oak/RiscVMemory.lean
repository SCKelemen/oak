import Oak.MemoryOrder
import Oak.AArch64Memory

/-!
# RISC-V (RV64) local memory-order model (docs/spec/69-riscv-memory-refinement.md)

The RISC-V counterpart of `Oak.AArch64Memory`: the local ordering
capabilities Oak requires of each atomic operation, the instruction
classes RVWMO offers (fences, `.aq`/`.rl`/`.aqrl` annotations on AMOs and
LR/SC), and two mappings — the C11 mapping the ISA recommends and clang
emits, and Oak's RISC-V OS-profile mapping.

The finding the model records: under RVWMO an `.aq` annotation alone, or
the `ld; fence r,rw` sequence, is RCpc — a release store and a later
acquire load to another address may reorder — the analogue of AArch64's
`LDAPR`. Oak's OS profile requires RCsc acquire, so its RISC-V mapping
takes the seq_cst load sequence (`fence rw,rw; ld; fence r,rw`) for
acquire loads and `.aqrl` (`lr.aqrl`) for acquire read-modify-writes; the
C backend selects these through `OAK_ORDER_LOAD_ACQUIRE` and
`OAK_ORDER_RMW_ACQUIRE` under `__riscv`.
-/

namespace Oak.RiscVMemory

open Oak.MemoryOrder
open Oak.AArch64Memory (LocalOrdering unordered acquireRCsc releaseOnly acquireReleaseRCsc
  requiredLoad requiredStore requiredRMW requiredFence satisfies)

/-- RCpc acquire: orders the access before later accesses, but not after a
    preceding release store to another address. -/
def acquireRCpc : LocalOrdering := ⟨true, false, false⟩
def acquireReleaseRCpc : LocalOrdering := ⟨true, true, false⟩

/-- The fences of RVWMO the mappings use. `fence.tso` orders reads before
    everything and everything before writes. -/
inductive Fence where
  | rRW   -- fence r, rw
  | rwW   -- fence rw, w
  | tso   -- fence.tso
  | rwRW  -- fence rw, rw
  deriving DecidableEq, Repr

def fenceProvided : Fence → LocalOrdering
  | .rRW => acquireRCsc
  | .rwW => releaseOnly
  | .tso => acquireReleaseRCsc
  | .rwRW => acquireReleaseRCsc

/-- A load or store with the fences around it. -/
structure Access where
  before : Option Fence
  after : Option Fence
  deriving DecidableEq, Repr

/-- What an access sequence provides: the fence after a load gives acquire;
    the fence before a store gives release; RCsc acquire needs a full fence
    *before* the load as well, which is what orders it after a preceding
    release store (the seq_cst load sequence). -/
def loadProvided : Access → LocalOrdering
  | ⟨none, none⟩ => unordered
  | ⟨none, some .rRW⟩ => acquireRCpc
  | ⟨some .rwRW, some .rRW⟩ => acquireRCsc
  | ⟨_, some f⟩ => ⟨(fenceProvided f).acquire, false, false⟩
  | ⟨_, none⟩ => unordered

def storeProvided : Access → LocalOrdering
  | ⟨none, none⟩ => unordered
  | ⟨some .rwW, none⟩ => releaseOnly
  | ⟨some .rwW, some .rwRW⟩ => releaseOnly
  | ⟨some f, _⟩ => ⟨false, (fenceProvided f).release, false⟩
  | ⟨none, _⟩ => unordered

/-- Annotations on AMOs and LR/SC. `.aq` and `.rl` alone are RCpc; both
    together are RCsc (the ISA's rule). -/
inductive Annotation where
  | none | aq | rl | aqrl
  deriving DecidableEq, Repr

def amoProvided : Annotation → LocalOrdering
  | .none => unordered
  | .aq => acquireRCpc
  | .rl => releaseOnly
  | .aqrl => acquireReleaseRCsc

/-- An LR/SC pair: the LR's annotation gives the acquire side, the SC's the
    release side; RCsc acquire needs `lr.aqrl`. -/
structure LrSc where
  lr : Annotation
  sc : Annotation
  deriving DecidableEq, Repr

def lrScProvided (p : LrSc) : LocalOrdering :=
  ⟨p.lr = .aq ∨ p.lr = .aqrl, p.sc = .rl ∨ p.sc = .aqrl, p.lr = .aqrl⟩

/-! ## The C11 mapping (ISA Table A.6, as clang emits it) -/

def c11Load : Order → Option Access
  | .relaxed => some ⟨none, none⟩
  | .acquire => some ⟨none, some .rRW⟩
  | .seqCst => some ⟨some .rwRW, some .rRW⟩
  | .release | .acqRel => none

def c11Store : Order → Option Access
  | .relaxed => some ⟨none, none⟩
  | .release => some ⟨some .rwW, none⟩
  | .seqCst => some ⟨some .rwW, some .rwRW⟩
  | .acquire | .acqRel => none

def c11Fence : Order → Option Fence
  | .acquire => some .rRW
  | .release => some .rwW
  | .acqRel => some .tso
  | .seqCst => some .rwRW
  | .relaxed => none

def c11AMO : Order → Annotation
  | .relaxed => .none
  | .acquire => .aq
  | .release => .rl
  | .acqRel | .seqCst => .aqrl

def c11LrSc : Order → LrSc
  | .relaxed => ⟨.none, .none⟩
  | .acquire => ⟨.aq, .none⟩
  | .release => ⟨.none, .rl⟩
  | .acqRel => ⟨.aq, .rl⟩
  | .seqCst => ⟨.aqrl, .rl⟩

/-! ## Oak's RISC-V OS-profile mapping: acquire strengthened to RCsc -/

def oakLoad : Order → Option Access
  | .acquire => c11Load .seqCst
  | o => c11Load o

def oakAMO : Order → Annotation
  | .acquire => .aqrl
  | o => c11AMO o

/-- Acquire and acq_rel compare-exchanges take the seq_cst pair
    `lr.aqrl / sc.rl`: the C11 acq_rel pair `lr.aq / sc.rl` is RCpc on its
    acquire side (the model found this; `OAK_ORDER_CAS_ACQUIRE` and
    `OAK_ORDER_CAS_ACQ_REL` select seq_cst under `__riscv`). -/
def oakLrSc : Order → LrSc
  | .acquire | .acqRel => c11LrSc .seqCst
  | o => c11LrSc o

def oakStore := c11Store
def oakFence := c11Fence

/-- The C11 acquire load is RCpc: it does not meet Oak's acquire
    requirement — the `LDAPR` finding, on RISC-V. -/
theorem c11_acquire_load_is_rcpc :
    satisfies (loadProvided ⟨none, some .rRW⟩) acquireRCsc = false := rfl

theorem c11_acquire_amo_is_rcpc :
    satisfies (amoProvided .aq) acquireRCsc = false := rfl

theorem c11_acquire_lrsc_is_rcpc :
    satisfies (lrScProvided ⟨.aq, .none⟩) acquireRCsc = false := by decide

/-- Oak's mapping meets every requirement. -/
def oakLoadProfileValid (o : Order) : Bool :=
  match requiredLoad o, oakLoad o with
  | some required, some access => satisfies (loadProvided access) required
  | Option.none, Option.none => true
  | _, _ => false

def oakStoreProfileValid (o : Order) : Bool :=
  match requiredStore o, oakStore o with
  | some required, some access => satisfies (storeProvided access) required
  | Option.none, Option.none => true
  | _, _ => false

def oakFenceProfileValid (o : Order) : Bool :=
  match requiredFence o, oakFence o with
  | some required, some fence => satisfies (fenceProvided fence) required
  | Option.none, Option.none => true
  | _, _ => false

theorem oak_load_profile_valid (o : Order) : oakLoadProfileValid o = true := by
  cases o <;> rfl

theorem oak_store_profile_valid (o : Order) : oakStoreProfileValid o = true := by
  cases o <;> rfl

theorem oak_fence_profile_valid (o : Order) : oakFenceProfileValid o = true := by
  cases o <;> rfl

theorem oak_amo_satisfies_local_order (o : Order) :
    satisfies (amoProvided (oakAMO o)) (requiredRMW o) = true := by
  cases o <;> rfl

theorem oak_lrsc_satisfies_local_order (o : Order) :
    satisfies (lrScProvided (oakLrSc o)) (requiredRMW o) = true := by
  cases o <;> decide

/-- Where the C11 mapping falls short is exactly the acquire orders: every
    other order's C11 mapping already meets Oak's requirement, so the
    strengthening is the smallest change. For AMOs only `acquire`; for
    LR/SC pairs `acq_rel` too, whose C11 pair `lr.aq / sc.rl` is RCpc on
    the acquire side. -/
theorem c11_amo_valid_except_acquire (o : Order) (h : o ≠ .acquire) :
    satisfies (amoProvided (c11AMO o)) (requiredRMW o) = true := by
  cases o <;> first | rfl | exact absurd rfl h

theorem c11_acqrel_lrsc_is_rcpc :
    satisfies (lrScProvided (c11LrSc .acqRel)) (requiredRMW .acqRel) = false := by decide

theorem c11_lrsc_valid_except_acquires (o : Order) (h : o ≠ .acquire) (h' : o ≠ .acqRel) :
    satisfies (lrScProvided (c11LrSc o)) (requiredRMW o) = true := by
  cases o <;> first | decide | exact absurd rfl h | exact absurd rfl h'

theorem c11_load_valid_except_acquire (o : Order) (h : o ≠ .acquire) :
    (match requiredLoad o, c11Load o with
      | some required, some access => satisfies (loadProvided access) required
      | Option.none, Option.none => true
      | _, _ => false) = true := by
  cases o <;> first | rfl | exact absurd rfl h

/-- The strengthened spellings are what the C backend selects under
    `__riscv`: seq_cst for acquire loads, acq_rel for acquire RMWs. -/
theorem oak_acquire_load_is_seqCst_sequence : oakLoad .acquire = some ⟨some .rwRW, some .rRW⟩ := rfl
theorem oak_acquire_amo_is_aqrl : oakAMO .acquire = .aqrl := rfl
theorem oak_acquire_lrsc_is_seqCst_pair : oakLrSc .acquire = ⟨.aqrl, .rl⟩ := rfl
theorem oak_acqrel_lrsc_is_seqCst_pair : oakLrSc .acqRel = ⟨.aqrl, .rl⟩ := rfl
theorem oak_seqCst_amo_is_aqrl : oakAMO .seqCst = .aqrl := rfl
theorem oak_seqCst_fence_is_full : oakFence .seqCst = some .rwRW := rfl

/-- The seq_cst store has two Appendix A spellings: `fence rw,w; sd` (the
    original Table A.6, what clang 18 emits) and `fence rw,w; sd; fence
    rw,rw` (later LLVM, the spelling `c11Store` records). The model judges
    both `releaseOnly`: the trailing full fence adds no local ordering the
    store needs, because sequential consistency among seq_cst accesses is
    carried by the full fence *before* every seq_cst load. Either spelling
    is therefore admitted by the refinement test
    (`codegen/riscv64_memory_refinement_test.go`). -/
theorem c11_store_seqCst_trailing_fence_optional :
    storeProvided ⟨some .rwW, none⟩ = storeProvided ⟨some .rwW, some .rwRW⟩ := rfl

end Oak.RiscVMemory
