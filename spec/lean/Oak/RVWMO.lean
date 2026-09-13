import Oak.RiscVMemory

/-! # RVWMO, instantiated for Oak's mapping (`69-riscv-memory-refinement.md` §4, `67-memory-ordering.md` §11)

`Oak.RiscVMemory` proves the local capabilities of each instruction class.
This module states the rules of the RISC-V weak memory model (RVWMO, ISA
volume I appendix A) that Oak's mapping leans on — as an axiomatic
structure over memory events — and proves the two litmus results the
mapping relies on: message passing through a release store and an RCsc
acquire load publishes the payload, and two harts that each store then
`fence rw,rw` then load cannot both read the initial values (store
buffering). The rules are RVWMO's: preserved program order is contained in
the global memory order (axiom "Load Value" and "Progress" aside), the
FENCE rule (PPO rule 4) orders every predecessor-set operation before
every successor-set operation across the fence, and the load-value axiom
makes a load read the latest store before it in the global memory order —
so a load from another hart's store is globally after that store. -/

namespace Oak.RVWMO

/-- What a memory operation does: load or store, at a location. -/
inductive Op where
  | load (loc : Nat)
  | store (loc : Nat)
  deriving DecidableEq, Repr

def Op.isLoad : Op → Bool
  | .load _ => true
  | .store _ => false

def Op.isStore : Op → Bool
  | .store _ => true
  | .load _ => false

/-- Which operations a FENCE's predecessor and successor sets cover
    (`fence pred, succ`): reads, writes, or both. -/
structure FenceSet where
  reads : Bool
  writes : Bool
  deriving DecidableEq, Repr

def FenceSet.covers (s : FenceSet) : Op → Bool
  | .load _ => s.reads
  | .store _ => s.writes

/-- The fences Oak's mapping emits, as their sets. -/
def fenceRwW : FenceSet × FenceSet := (⟨true, true⟩, ⟨false, true⟩)   -- fence rw, w  (before a release store)
def fenceRwRW : FenceSet × FenceSet := (⟨true, true⟩, ⟨true, true⟩)  -- fence rw, rw (before an RCsc acquire load)
def fenceRRW : FenceSet × FenceSet := (⟨true, false⟩, ⟨true, true⟩)  -- fence r, rw  (after an acquire load)

/-- An execution's structure: memory events with a hart and a program
    position, the fences between them, a reads-from relation, and the
    global memory order. The fields after `gmo` are RVWMO's rules. -/
structure Execution (Event : Type) where
  hart : Event → Nat
  po : Event → Event → Prop         -- program order within one hart
  op : Event → Op
  /-- `fenceBetween pred succ a b`: a fence with those sets lies between
      `a` and `b` in program order (`a <po fence <po b`). -/
  fenceBetween : FenceSet → FenceSet → Event → Event → Prop
  readsFrom : Event → Event → Prop  -- store, load
  gmo : Event → Event → Prop        -- the global memory order
  gmo_irrefl : ∀ a, ¬ gmo a a
  gmo_trans : ∀ a b c, gmo a b → gmo b c → gmo a c
  /-- PPO rule 4: the FENCE orders what its predecessor set covers before
      what its successor set covers, and PPO is contained in gmo. -/
  fence_rule : ∀ pred succ a b, fenceBetween pred succ a b → pred.covers (op a) = true → succ.covers (op b) = true → gmo a b
  /-- The load-value axiom's consequence for a load of another hart's
      store: the store is globally before the load. -/
  reads_from_gmo : ∀ s l, readsFrom s l → hart s ≠ hart l → gmo s l
  /-- The load-value axiom for a load that reads the initial value: every
      store to its location is globally after it. -/
  reads_initial : Event → Prop
  initial_before_stores : ∀ l s, reads_initial l → (∃ loc, op l = .load loc ∧ op s = .store loc) → gmo l s

variable {Event : Type} (x : Execution Event)

/-- Message passing under Oak's mapping: the producer writes the payload,
    `fence rw,w`, stores the flag; the consumer `fence rw,rw`, loads the
    flag (reading that store), `fence r,rw`, loads the payload. The payload
    write is globally before the payload read — so the read cannot return
    a value older than the write. -/
theorem message_passing (payloadW flagW flagR payloadR : Event)
    (hharts : x.hart payloadW ≠ x.hart flagR)
    (hwrite : x.op payloadW = .store 0) (hflagW : x.op flagW = .store 1)
    (hflagR : x.op flagR = .load 1) (hread : x.op payloadR = .load 0)
    (hrelease : x.fenceBetween fenceRwW.1 fenceRwW.2 payloadW flagW)
    (hacquire : x.fenceBetween fenceRRW.1 fenceRRW.2 flagR payloadR)
    (hrf : x.readsFrom flagW flagR)
    (hsameHart : x.hart payloadW = x.hart flagW) :
    x.gmo payloadW payloadR := by
  have h1 : x.gmo payloadW flagW := x.fence_rule _ _ _ _ hrelease (by simp [fenceRwW, FenceSet.covers, hwrite]) (by simp [fenceRwW, FenceSet.covers, hflagW])
  have h2 : x.gmo flagW flagR := x.reads_from_gmo _ _ hrf (by rw [← hsameHart]; exact hharts)
  have h3 : x.gmo flagR payloadR := x.fence_rule _ _ _ _ hacquire (by simp [fenceRRW, FenceSet.covers, hflagR]) (by simp [fenceRRW, FenceSet.covers, hread])
  exact x.gmo_trans _ _ _ h1 (x.gmo_trans _ _ _ h2 h3)

/-- Store buffering under the RCsc acquire's leading `fence rw,rw`: hart 0
    stores x then loads y, hart 1 stores y then loads x, each with the
    full fence between; both loads cannot read the initial values. -/
theorem store_buffering (wx ry wy rx : Event)
    (hwx : x.op wx = .store 0) (hry : x.op ry = .load 1)
    (hwy : x.op wy = .store 1) (hrx : x.op rx = .load 0)
    (hfence0 : x.fenceBetween fenceRwRW.1 fenceRwRW.2 wx ry)
    (hfence1 : x.fenceBetween fenceRwRW.1 fenceRwRW.2 wy rx)
    (hinit_y : x.reads_initial ry) (hinit_x : x.reads_initial rx) : False := by
  have h1 : x.gmo wx ry := x.fence_rule _ _ _ _ hfence0 (by simp [fenceRwRW, FenceSet.covers, hwx]) (by simp [fenceRwRW, FenceSet.covers, hry])
  have h2 : x.gmo ry wy := x.initial_before_stores _ _ hinit_y ⟨1, hry, hwy⟩
  have h3 : x.gmo wy rx := x.fence_rule _ _ _ _ hfence1 (by simp [fenceRwRW, FenceSet.covers, hwy]) (by simp [fenceRwRW, FenceSet.covers, hrx])
  have h4 : x.gmo rx wx := x.initial_before_stores _ _ hinit_x ⟨0, hrx, hwx⟩
  exact x.gmo_irrefl wx (x.gmo_trans _ _ _ h1 (x.gmo_trans _ _ _ h2 (x.gmo_trans _ _ _ h3 h4)))

/-- The C11 acquire load (`ld; fence r,rw`, no leading fence) has no fence
    between a preceding store and the load, so the store-buffering
    argument has nothing to order `wx` before `ry`: this is the RCpc gap
    `Oak.RiscVMemory.c11_acquire_load_is_rcpc` names, and why the OS
    profile takes the seq_cst load sequence. The fences Oak emits are the
    sets used above. -/
theorem release_store_fence : Oak.RiscVMemory.oakStore .release = some ⟨some .rwW, none⟩ := rfl

theorem acquire_load_fences : Oak.RiscVMemory.oakLoad .acquire = some ⟨some .rwRW, some .rRW⟩ := rfl

end Oak.RVWMO
