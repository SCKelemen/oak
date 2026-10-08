import OakSailBridge.BitwiseExecution

/-! Concrete little-endian effects of the unchanged sequential Sail byte
primitives. These lemmas neither assume memory success nor replace the external
memory implementation. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section

namespace OakSailBridge.BitwiseDecoded
open LeanRV64D Sail Sail.ConcurrencyInterfaceV1

def setByte (s : State) (addr : Nat) (value : BitVec 8) : State :=
  { s with mem := s.mem.insert addr value }

/-- The primitive writes increasing natural addresses, with the least
significant byte at the lowest address. -/
def store64 (s : State) (addr : Nat) (value : BitVec 64) : State :=
  setByte (setByte (setByte (setByte (setByte (setByte (setByte (setByte
    s addr (value.extractLsb' 0 8))
    (addr + 1) (value.extractLsb' 8 8))
    (addr + 2) (value.extractLsb' 16 8))
    (addr + 3) (value.extractLsb' 24 8))
    (addr + 4) (value.extractLsb' 32 8))
    (addr + 5) (value.extractLsb' 40 8))
    (addr + 6) (value.extractLsb' 48 8))
    (addr + 7) (value.extractLsb' 56 8)

theorem writeByte_run (s : State) (addr : Nat) (value : BitVec 8) :
    (PreSail.writeByte addr value : SailM PUnit).run s =
      .ok () (setByte s addr value) := by rfl

theorem writeBytes8_run (s : State) (addr : Nat) (value : BitVec 64) :
    (PreSail.writeBytes (n := 8) addr value : SailM Bool).run s =
      .ok true (store64 s addr value) := by
  rfl

theorem readByte_run (s : State) (addr : Nat) (value : BitVec 8)
    (h : s.mem.get? addr = some value) :
    (PreSail.readByte addr : SailM (BitVec 8)).run s = .ok value s := by
  simp only [PreSail.readByte, EStateM.run, Bind.bind, MonadState.get, getThe,
    MonadStateOf.get, EStateM.bind, EStateM.get, ← Std.ExtHashMap.get?_eq_getElem?,
    h, Pure.pure, EStateM.pure]

theorem lookup_store64_byte (s : State) (addr : Nat) (value : BitVec 64)
    (i : Fin 8) :
    (store64 s addr value).mem.get? (addr + i.val) =
      some (value.extractLsb' (8 * i.val) 8) := by
  have hi := i.isLt
  have cases : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨
      i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 := by omega
  rcases cases with h|h|h|h|h|h|h|h <;>
    simp only [store64, setByte, h, Std.ExtHashMap.get?_eq_getElem?,
      Std.ExtHashMap.getElem?_insert] <;> simp

theorem lookup_store64_other (s : State) (addr query : Nat) (value : BitVec 64)
    (h : query < addr ∨ addr + 8 ≤ query) :
    (store64 s addr value).mem.get? query = s.mem.get? query := by
  have hne : ∀ i : Fin 8, addr + i.val ≠ query := by intro i; omega
  have h0 : addr ≠ query := hne ⟨0, by decide⟩
  simp [store64, setByte, Std.ExtHashMap.getElem?_insert,
    h0, hne ⟨1, by decide⟩, hne ⟨2, by decide⟩,
    hne ⟨3, by decide⟩, hne ⟨4, by decide⟩, hne ⟨5, by decide⟩,
    hne ⟨6, by decide⟩, hne ⟨7, by decide⟩]

@[simp] theorem store64_regs (s : State) (addr : Nat) (value : BitVec 64) :
    (store64 s addr value).regs = s.regs := rfl

@[simp] theorem store64_choiceState (s : State) (addr : Nat) (value : BitVec 64) :
    (store64 s addr value).choiceState = s.choiceState := rfl

@[simp] theorem store64_cycleCount (s : State) (addr : Nat) (value : BitVec 64) :
    (store64 s addr value).cycleCount = s.cycleCount := rfl

@[simp] theorem store64_sailOutput (s : State) (addr : Nat) (value : BitVec 64) :
    (store64 s addr value).sailOutput = s.sailOutput := rfl

theorem store64_setRegister (s : State) (addr : Nat) (value : BitVec 64)
    (r : Register) (v : RegisterType r) :
    store64 (setRegister s r v) addr value =
      setRegister (store64 s addr value) r v := rfl

theorem store64_preserves_disjoint_bytes (s : State) (addr other : Nat)
    (value previous : BitVec 64)
    (hsep : other + 8 ≤ addr ∨ addr + 8 ≤ other)
    (hbytes : ∀ i : Fin 8, s.mem.get? (other + i.val) =
      some (previous.extractLsb' (8 * i.val) 8)) :
    ∀ i : Fin 8, (store64 s addr value).mem.get? (other + i.val) =
      some (previous.extractLsb' (8 * i.val) 8) := by
  intro i
  rw [lookup_store64_other s addr (other + i.val) value (by have hi := i.isLt; omega)]
  exact hbytes i

theorem readBytes8_shape (addr : Nat) :
    (PreSail.readBytes 8 addr : SailM (BitVec 64 × Option Bool)) = (do
      let b0 ← PreSail.readByte addr
      let b1 ← PreSail.readByte (addr + 1)
      let b2 ← PreSail.readByte (addr + 2)
      let b3 ← PreSail.readByte (addr + 3)
      let b4 ← PreSail.readByte (addr + 4)
      let b5 ← PreSail.readByte (addr + 5)
      let b6 ← PreSail.readByte (addr + 6)
      let b7 ← PreSail.readByte (addr + 7)
      pure (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0, none)) := by
  simp [PreSail.readBytes, bind_assoc, Nat.add_assoc]

theorem reassemble64 (value : BitVec 64) :
    (value.extractLsb' 56 8 ++ value.extractLsb' 48 8 ++
      value.extractLsb' 40 8 ++ value.extractLsb' 32 8 ++
      value.extractLsb' 24 8 ++ value.extractLsb' 16 8 ++
      value.extractLsb' 8 8 ++ value.extractLsb' 0 8 : BitVec 64) = (value : BitVec 64) := by
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 56 = 48 + 8 from rfl)]
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 48 = 40 + 8 from rfl)]
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 40 = 32 + 8 from rfl)]
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 32 = 24 + 8 from rfl)]
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 24 = 16 + 8 from rfl)]
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 16 = 8 + 8 from rfl)]
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 8 = 0 + 8 from rfl)]
  exact _root_.BitVec.extractLsb'_eq_self

theorem readBytes8_run (s : State) (addr : Nat) (value : BitVec 64)
    (h : ∀ i : Fin 8, s.mem.get? (addr + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (PreSail.readBytes 8 addr : SailM (BitVec 64 × Option Bool)).run s =
      .ok (value, none) s := by
  rw [readBytes8_shape]
  rw [bind_run_ok _ _ (readByte_run s addr _ (h ⟨0, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 1) _ (h ⟨1, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 2) _ (h ⟨2, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 3) _ (h ⟨3, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 4) _ (h ⟨4, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 5) _ (h ⟨5, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 6) _ (h ⟨6, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 7) _ (h ⟨7, by decide⟩))]
  change EStateM.Result.ok (_, none) s = _
  exact congrArg (fun v : BitVec 64 =>
    (EStateM.Result.ok (v, none) s : EStateM.Result (Sail.Error exception) State
      (BitVec 64 × Option Bool))) (reassemble64 value)

theorem readBytes8_store64 (s : State) (addr : Nat) (value : BitVec 64) :
    (PreSail.readBytes 8 addr : SailM (BitVec 64 × Option Bool)).run
      (store64 s addr value) = .ok (value, none) (store64 s addr value) := by
  exact readBytes8_run _ _ _ (lookup_store64_byte s addr value)

/-- A complete run of the actual primitive write followed by its matching
read succeeds for every initial memory, including an empty one. -/
theorem writeBytes8_readBytes8 (s : State) (addr : Nat) (value : BitVec 64) :
    ((do
      let _ ← PreSail.writeBytes (n := 8) addr value
      PreSail.readBytes 8 addr) : SailM (BitVec 64 × Option Bool)).run s =
      .ok (value, none) (store64 s addr value) := by
  rw [bind_run_ok _ _ (writeBytes8_run s addr value)]
  exact readBytes8_store64 s addr value

theorem readBytes8_store64_disjoint (s : State) (addr other : Nat)
    (value previous : BitVec 64) (hsep : other + 8 ≤ addr ∨ addr + 8 ≤ other) :
    (PreSail.readBytes 8 other : SailM (BitVec 64 × Option Bool)).run
      (store64 (store64 s other previous) addr value) =
      .ok (previous, none) (store64 (store64 s other previous) addr value) := by
  apply readBytes8_run
  exact store64_preserves_disjoint_bytes _ _ _ _ _ hsep
    (lookup_store64_byte s other previous)

end OakSailBridge.BitwiseDecoded
