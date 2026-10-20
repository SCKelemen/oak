import OakSailBridge.FramedRegisters
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBridge.BitwiseDecoded
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1

def openPMPConfig : Vector (BitVec 8) 64 := Vector.replicate 64 0x1f
def openPMPAddress : Vector (BitVec 64) 64 := Vector.replicate 64 0xffffffffffffffff

theorem pmp_first_read (s : State)
    (hc : s.regs.get? Register.pmpcfg_n = some openPMPConfig)
    (ha : s.regs.get? Register.pmpaddr_n = some openPMPAddress) :
    (pmpReadAddrReg 0).run s = .ok (0xffffffffffffffff#64) s := by
  simp [pmpReadAddrReg, EStateM.run, Bind.bind, EStateM.bind, PreSail.readReg,
    MonadState.get, getThe, MonadStateOf.get, EStateM.get, Pure.pure, EStateM.pure,
    hc, ha, openPMPConfig, openPMPAddress]
  rfl

theorem pmp_all_range (addr : BitVec 64) :
    pmpMatchAddr (.Physaddr addr) 8 0x1f 0xffffffffffffffff 0 = pure pmpAddrMatch.PMP_Match := by
  simp [pmpMatchAddr, pmpRangeMatch, pmpAddrMatchType_encdec_backwards,
    _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb, Sail.BitVec.toNatInt,
    Sail.BitVec.addInt]
  have h := addr.isLt
  have h0 : ¬ ((addr.toNat : Int) + 8 ≤ 0 ∨ 73786976294838206464 ≤ addr.toNat) := by omega
  have h1 : (addr.toNat : Int) + 8 ≤ 73786976294838206464 := by omega
  simp [h0, h1]

theorem pmp_load_run (s : State) (addr : BitVec 64)
    (hc : s.regs.get? Register.pmpcfg_n = some openPMPConfig)
    (ha : s.regs.get? Register.pmpaddr_n = some openPMPAddress) :
    (pmpCheck (.Physaddr addr) 8 (.Load .Data) .Machine).run s = .ok none s := by
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
    _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb, pmp_all_range, to_bits,
    pmpCheckRWX, _get_Pmpcfg_ent_R, SailME.throw, PreSail.PreSailME.throw,
    MonadExceptOf.throw, Sail.BitVec.access, zeros, get_slice_int]
  simp only [show (Vector.replicate 64 (31#8))[(0 : Int)] = (31#8) from rfl]
  have h := addr.isLt
  have h0 : ¬ ((addr.toNat : Int) + 8 ≤ 0 ∨ 73786976294838206464 ≤ addr.toNat) := by omega
  have h1 : (addr.toNat : Int) + 8 ≤ 73786976294838206464 := by omega
  simp [pmpMatchAddr, pmpRangeMatch, pmpAddrMatchType_encdec_backwards,
    _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb, Sail.BitVec.toNatInt,
    Sail.BitVec.addInt, h0, h1, Pure.pure, EStateM.pure,
    EStateM.map, EStateM.bind, ExceptT.bindCont]

/-- The first concrete NAPOT entry permits an eight-byte store.
The real PMP loop exits on that entry, without assuming its result. -/
theorem pmp_store_run (s : State) (addr : BitVec 64)
    (hc : s.regs.get? Register.pmpcfg_n = some openPMPConfig)
    (ha : s.regs.get? Register.pmpaddr_n = some openPMPAddress) :
    (pmpCheck (.Physaddr addr) 8 (.Store .Data) .Machine).run s = .ok none s := by
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
    _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb, pmp_all_range, to_bits,
    pmpCheckRWX, _get_Pmpcfg_ent_W, SailME.throw, PreSail.PreSailME.throw,
    MonadExceptOf.throw, Sail.BitVec.access, zeros, get_slice_int]
  simp only [show (Vector.replicate 64 (31#8))[(0 : Int)] = (31#8) from rfl]
  have h := addr.isLt
  have h0 : ¬ ((addr.toNat : Int) + 8 ≤ 0 ∨ 73786976294838206464 ≤ addr.toNat) := by omega
  have h1 : (addr.toNat : Int) + 8 ≤ 73786976294838206464 := by omega
  simp [pmpMatchAddr, pmpRangeMatch, pmpAddrMatchType_encdec_backwards,
    _get_Pmpcfg_ent_A, Sail.BitVec.extractLsb, Sail.BitVec.toNatInt,
    Sail.BitVec.addInt, h0, h1, Pure.pure, EStateM.pure,
    EStateM.map, EStateM.bind, ExceptT.bindCont]

end OakSailBridge.BitwiseDecoded
