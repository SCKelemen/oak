import OakSailBridge.FramedMemoryExecution
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

theorem readBytes4_shape (addr : Nat) :
    (PreSail.readBytes 4 addr : SailM (BitVec 32 × Option Bool)) = (do
      let b0 ← PreSail.readByte addr
      let b1 ← PreSail.readByte (addr + 1)
      let b2 ← PreSail.readByte (addr + 2)
      let b3 ← PreSail.readByte (addr + 3)
      pure (b3 ++ b2 ++ b1 ++ b0, none)) := by
  simp [PreSail.readBytes, bind_assoc, Nat.add_assoc]

theorem reassemble32 (value : BitVec 32) :
    (value.extractLsb' 24 8 ++ value.extractLsb' 16 8 ++
      value.extractLsb' 8 8 ++ value.extractLsb' 0 8 : BitVec 32) = (value : BitVec 32) := by
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 24 = 16 + 8 from rfl)]
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 16 = 8 + 8 from rfl)]
  rw [_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (show 8 = 0 + 8 from rfl)]
  exact _root_.BitVec.extractLsb'_eq_self

theorem readBytes4_run (s : State) (addr : Nat) (value : BitVec 32)
    (h : ∀ i : Fin 4, s.mem.get? (addr + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (PreSail.readBytes 4 addr : SailM (BitVec 32 × Option Bool)).run s =
      .ok (value, none) s := by
  rw [readBytes4_shape]
  rw [bind_run_ok _ _ (readByte_run s addr _ (h ⟨0, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 1) _ (h ⟨1, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 2) _ (h ⟨2, by decide⟩))]
  rw [bind_run_ok _ _ (readByte_run s (addr + 3) _ (h ⟨3, by decide⟩))]
  change EStateM.Result.ok (_, none) s = _
  exact congrArg (fun v : BitVec 32 =>
    (EStateM.Result.ok (v, none) s : EStateM.Result (Sail.Error exception) State
      (BitVec 32 × Option Bool))) (reassemble32 value)

theorem read_ram4_run (s : State) (addr : BitVec 64) (value : BitVec 32)
    (h : ∀ i : Fin 4, s.mem.get? (addr.toNat + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (Functions.read_ram .Read_plain (.Physaddr addr) 4 false).run s =
      .ok (value, ()) s := by
  have hs : Functions.read_ram .Read_plain (.Physaddr addr) 4 false = (do
      let (value, _) ← (PreSail.readBytes 4 addr.toNat : SailM (BitVec 32 × Option Bool))
      pure (value, ())) := by
    simp only [Functions.read_ram, pure_bind, PreSail.sail_mem_read, bind_assoc]
    try rfl
  rw [hs, bind_run_ok _ _ (readBytes4_run s addr.toNat value h)]
  rfl

/-- Actual four-byte instruction permission and alignment predicates. -/
def ExecutableRegion (regions : List PMA_Region) (addr : BitVec 64)
    (region : PMA_Region) : Prop :=
  matching_pma_region regions (.Physaddr addr) 4 = some region ∧
  region.attributes.executable = true ∧ is_aligned_paddr (.Physaddr addr) 4 = true

def LowCodeRAM (addr : BitVec 64) : Prop := addr.toNat + 4 ≤ 0x02000000

theorem pmp_code4_range (addr : BitVec 64) :
    pmpMatchAddr (.Physaddr addr) 4 0x1f 0xffffffffffffffff 0 = pure pmpAddrMatch.PMP_Match := by
  simp [pmpMatchAddr, pmpRangeMatch, pmpAddrMatchType_encdec_backwards,
    _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb, Sail.BitVec.toNatInt,
    Sail.BitVec.addInt]
  try simp only [show (Vector.replicate 64 (31#8))[(0 : Nat)] = (31#8) from rfl]
  have h := addr.isLt
  have h0 : ¬ ((addr.toNat : Int) + 4 ≤ 0 ∨ 73786976294838206464 ≤ addr.toNat) := by omega
  have h1 : (addr.toNat : Int) + 4 ≤ 73786976294838206464 := by omega
  simp [h0, h1]

theorem pmp_fetch4_run (s : State) (addr : BitVec 64)
    (hc : s.regs.get? Register.pmpcfg_n = some openPMPConfig)
    (ha : s.regs.get? Register.pmpaddr_n = some openPMPAddress) :
    (pmpCheck (.Physaddr addr) 4 (.InstructionFetch ()) .Machine).run s = .ok none s := by
  unfold pmpCheck
  simp only [sys_pmp_count]
  simp only [ForIn.forIn, instForInOfForIn', ForIn'.forIn', IntRange.forIn']
  rw [IntRange.forIn'.loop]
  simp [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hc, ha, Membership.mem, IntRange.instMemIntRange,
    ExceptT.pure, pmpReadAddrReg, sys_pmp_grain, openPMPConfig, openPMPAddress,
    _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb, pmp_code4_range, to_bits,
    pmpCheckRWX, _get_Pmpcfg_ent_X, SailME.throw, PreSail.PreSailME.throw,
    MonadExceptOf.throw, Sail.BitVec.access, zeros, get_slice_int]
  try simp only [show (Vector.replicate 64 (31#8))[(0 : Int)] = (31#8) from rfl]
  try simp only [show (Vector.replicate 64 (31#8))[(0 : Nat)] = (31#8) from rfl]
  have h := addr.isLt
  have h0 : ¬ ((addr.toNat : Int) + 4 ≤ 0 ∨ 73786976294838206464 ≤ addr.toNat) := by omega
  have h1 : (addr.toNat : Int) + 4 ≤ 73786976294838206464 := by omega
  simp [pmpMatchAddr, pmpRangeMatch, pmpAddrMatchType_encdec_backwards,
    _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb, Sail.BitVec.toNatInt,
    Sail.BitVec.addInt, h0, h1, Pure.pure, EStateM.pure,
    EStateM.map, EStateM.bind, ExceptT.bindCont]
  try rfl



theorem pma_fetch4_run (s : State) (addr : BitVec 64) (regions : List PMA_Region)
    (region : PMA_Region) (hr : s.regs.get? Register.pma_regions = some regions)
    (h : ExecutableRegion regions addr region) :
    (pmaCheck (.Physaddr addr) 4 (.InstructionFetch ()) .PBMT_PMA false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
  unfold pmaCheck
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, liftM, monadLift,
    MonadLift.monadLift, Bind.bind, Functor.map, EStateM.bind, EStateM.map, EStateM.run,
    PreSail.readReg, MonadState.get, getThe, MonadStateOf.get, EStateM.get,
    Pure.pure, EStateM.pure, hr, h.1]
  simp [override_PMA, h.2.1, mag_pma_check, h.2.2, is_mag_applicable_access,
    LeanRV64D.assert, PreSail.assert, Functions.not, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure]
  simp only [ExceptT.pure, ExceptT.mk, ExceptT.bindCont, Bind.bind, EStateM.bind, EStateM.map,
    Pure.pure, EStateM.pure, h.2.1]
  rfl

theorem code_mmio_read_false (s : State) (addr : BitVec 64) (h : LowCodeRAM addr)
    (ht : s.regs.get? Register.htif_tohost_base = some none) :
    (within_mmio_readable (.Physaddr addr) 4).run s = .ok false s := by
  have hc : within_clint (.Physaddr addr) 4 = (pure false : SailM Bool) := by
    change pure (decide (33554432 ≤ (addr.toNat : Int)) &&
      decide ((addr.toNat : Int) + 4 ≤ 34340864)) = pure false
    have hh : ¬ (33554432 : Int) ≤ addr.toNat := by unfold LowCodeRAM at h; omega
    simp [hh]
  have hs : within_sig (.Physaddr addr) 4 = (pure false : SailM Bool) := by
    change pure (decide (201326592 ≤ (addr.toNat : Int)) &&
      decide ((addr.toNat : Int) + 4 ≤ 201326624)) = pure false
    have hh : ¬ (201326592 : Int) ≤ addr.toNat := by unfold LowCodeRAM at h; omega
    simp [hh]
  simp only [within_mmio_readable, get_config_rvfi, hc, hs, pure_bind]
  unfold within_htif_readable within_htif_writable
  simp only [Bool.false_eq_true, if_false, bind_assoc]
  rw [bind_run_ok _ _ (read_register s Register.htif_tohost_base none ht)]
  rfl

theorem pma_priority_fetch4 (s : State) (addr : BitVec 64) (regions : List PMA_Region)
    (region : PMA_Region) (hr : s.regs.get? Register.pma_regions = some regions)
    (h : ExecutableRegion regions addr region) :
    (check_pma_with_pmp_priority (.InstructionFetch ()) .PBMT_PMA .Machine
      (.Physaddr addr) 4 false).run s =
      .ok (.Ok { splittable := .CannotSplit, granule_size_exp := 0 }) s := by
  unfold check_pma_with_pmp_priority
  rw [bind_run_ok _ _ (pma_fetch4_run s addr regions region hr h)]
  rfl

theorem aligned_code_split (addr : BitVec 64) :
    split_misaligned (.Physaddr addr) 4 0 .CannotSplit = pure (1, 4) := by rfl

private theorem addInt_zero {width : Nat} (addr : BitVec width) :
    Sail.BitVec.addInt addr 0 = addr := by simp [Sail.BitVec.addInt]

theorem checked_fetch4_run (s : State) (addr : BitVec 64) (value : BitVec 32)
    (regions : List PMA_Region) (region : PMA_Region)
    (hr : s.regs.get? Register.pma_regions = some regions)
    (hregion : ExecutableRegion regions addr region) (hlow : LowCodeRAM addr)
    (ht : s.regs.get? Register.htif_tohost_base = some none)
    (hc : s.regs.get? Register.pmpcfg_n = some openPMPConfig)
    (ha : s.regs.get? Register.pmpaddr_n = some openPMPAddress)
    (hbytes : ∀ i : Fin 4, s.mem.get? (addr.toNat + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (checked_mem_read (.InstructionFetch ()) .PBMT_PMA .Machine (.Physaddr addr) 4
      false false false false).run s = .ok (.Ok (value, ())) s := by
  have hperm := pma_priority_fetch4 s addr regions region hr hregion
  have hpmp := pmp_fetch4_run s addr hc ha
  have hmmio := code_mmio_read_false s addr hlow ht
  have hread := read_ram4_run s addr value hbytes
  unfold checked_mem_read
  simp only [SailME.run, PreSail.PreSailME.run, ExceptT.run, ExceptT.bind,
    ExceptT.map, ExceptT.lift, ExceptT.mk, ExceptT.bindCont, ExceptT.pure,
    liftM, monadLift, MonadLift.monadLift, Bind.bind, Functor.map,
    EStateM.bind, EStateM.map, EStateM.run, Pure.pure, EStateM.pure] at hperm hpmp hmmio hread ⊢
  rw [hperm]
  simp only [aligned_code_split, EStateM.pure]
  simp only [read_kind_of_flags, misaligned_order, sys_misaligned_order_decreasing,
    untilFuelM, untilFuelM.go, LeanRV64D.assert, PreSail.assert,
    ExceptT.pure, ExceptT.mk, ExceptT.bindCont, ExceptT.bind,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  simp only [Bool.false_eq_true, if_false, Int.reduceToNat, Int.reduceSub]
  simp only [untilFuelM.go, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  simp [bits_of_physaddr, addInt_zero, Sail.BitVec.extractLsb,
    hpmp, hmmio, hread, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  try simp only [hpmp, hmmio, hread, ExceptT.bindCont, ExceptT.pure, ExceptT.mk,
    Bind.bind, EStateM.bind, EStateM.map, Pure.pure, EStateM.pure]
  try simp [Sail.BitVec.updateSubrange, Sail.BitVec.updateSubrange', zeros]
  try rfl

theorem mem_fetch4_run (s : State) (addr : BitVec 64) (value : BitVec 32)
    (regions : List PMA_Region) (region : PMA_Region) (hc : MemoryConfig s regions)
    (hr : ExecutableRegion regions addr region) (hl : LowCodeRAM addr)
    (hb : ∀ i : Fin 4, s.mem.get? (addr.toNat + i.val) =
      some (value.extractLsb' (8 * i.val) 8)) :
    (mem_read (.InstructionFetch ()) .PBMT_PMA (.Physaddr addr) 4
      false false false).run s = .ok (.Ok value) s := by
  unfold mem_read
  rw [bind_run_ok _ _ (read_register s Register.mstatus 0 hc.status)]
  rw [bind_run_ok _ _ (read_register s Register.cur_privilege .Machine hc.privilege)]
  rw [machine_effective]
  simp only [pure_bind]
  unfold mem_read_priv mem_read_priv_meta
  simp only [bind_assoc]
  rw [bind_run_ok _ _ (checked_fetch4_run s addr value regions region hc.regions hr hl
    hc.htif hc.pmpcfg hc.pmpaddr hb)]
  rfl

theorem readBytes4_missing_first (s : State) (addr : Nat)
    (h : s.mem.get? addr = none) :
    (PreSail.readBytes 4 addr : SailM (BitVec 32 × Option Bool)).run s =
      .error (.OutOfMemoryRange addr) s := by
  rw [readBytes4_shape]
  simp only [PreSail.readByte, EStateM.run, Bind.bind, MonadState.get, getThe,
    MonadStateOf.get, EStateM.bind, EStateM.get, ← Std.ExtHashMap.get?_eq_getElem?,
    h, Pure.pure, EStateM.pure]
  rfl

example (regions : List PMA_Region) (addr : BitVec 64) (region : PMA_Region)
    (h : region.attributes.executable = false) : ¬ ExecutableRegion regions addr region := by
  intro hr
  have hx := hr.2.1
  rw [h] at hx
  contradiction

end OakSailBridge.BitwiseDecoded
