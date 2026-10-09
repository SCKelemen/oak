import ReturnMode
namespace Oak.SailBridge.ReturnELMode
open ReturnExecution ReturnExecution.Functions Sail PreSail
set_option linter.unusedSimpArgs false
abbrev State := ReturnConfig.State
/-- Default-compatible EL configuration, with explicit AArch64 controls.
No callback-success premise appears here. -/
structure Ready (s : State) where
 cfg : ReturnMode.Config s {}
 highest : s.regs.get? Register.__highest_el_aarch32 = some false
 scrValue : BitVec 32
 scr : s.regs.get? Register.SCR_EL3 = some scrValue
 scrRW : BitVec.join1 [BitVec.access scrValue 10] = 1#1
 hcrValue : BitVec 64
 hcr : s.regs.get? Register.HCR_EL2 = some hcrValue
 hcrRW : BitVec.join1 [BitVec.access hcrValue 31] = 1#1

private theorem undefined_bits_eq (width : Nat) :
 (PreSail.undefined_bitvector width : SailM (BitVec width)) = pure (0 : BitVec width) := by
 funext state
 have hc : state.choiceState = () := Subsingleton.elim (α := Unit) _ _
 change EStateM.Result.ok (0 : BitVec width) {state with choiceState := ()} = .ok _ state
 rw [← hc]
private theorem undefined_bool_eq :
 (PreSail.undefined_bool () : SailM Bool) = pure false := by
 funext state
 have hc : state.choiceState = () := Subsingleton.elim (α := Unit) _ _
 change EStateM.Result.ok false {state with choiceState := ()} = .ok _ state
 rw [← hc]

theorem haveEL3_run (s : State) (h : Ready s) : HaveEL EL3 s = .ok true s := by
 simp [HaveEL, EL0,EL1,EL2,EL3,readReg,h.cfg.el3,EStateM.run,
 Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,EStateM.get,getThe]

theorem haveEL2_run (s : State) (h : Ready s) : HaveEL EL2 s = .ok true s := by
 simp [HaveEL, EL0,EL1,EL2,EL3,readReg,h.cfg.el2,EStateM.run,
 Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,EStateM.get,getThe]

theorem scr_run (b : Boundaries) (s : State) (h : Ready s) :
 (aget_SCR_GEN b ()).run s = .ok h.scrValue s := by
 simp [aget_SCR_GEN, haveEL3_run s h, HighestELUsingAArch32,readReg,h.highest,h.scr,
 undefined_bits_eq,PreSail.assert,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
 MonadStateOf.get,MonadState.get,EStateM.get,getThe]

theorem secure_run (b : Boundaries) (s : State) (h : Ready s) :
 (IsSecureBelowEL3 b ()).run s = .ok (BitVec.join1 [BitVec.access h.scrValue 0] == 0#1) s := by
 have sr : aget_SCR_GEN b () s = .ok h.scrValue s := scr_run b s h
 simp [IsSecureBelowEL3,haveEL3_run s h,sr,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
 BitVec.access]

theorem haveAArch32EL1_run (s : State) (h : Ready s) :
 HaveAArch32EL EL1 s = .ok true s := by
 have any : HaveAnyAArch32 () s = .ok true s := ReturnMode.haveAny_run s {} h.cfg
 simp [HaveAArch32EL,HaveEL,HighestEL,HighestELUsingAArch32,any,EL0,EL1,EL2,EL3,
 h.cfg.el1,h.cfg.el3,h.highest,readReg,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
 MonadStateOf.get,MonadState.get,EStateM.get,getThe]

theorem host_run (s : State) (v : ReturnConfig.Values) (h : ReturnConfig.Initialized s v) :
 HaveVirtHostExt () s = .ok v.v81 s := by
 simp [HaveVirtHostExt,HasArchVersion,readReg,h.v81,h.v82,h.v83,h.v84,h.v85,
 EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,EStateM.get,getThe]
 cases v.v81 <;> rfl

theorem secureEL2_run (s : State) (v : ReturnConfig.Values) (h : ReturnConfig.Initialized s v) :
 HaveSecureEL2Ext () s = .ok v.v84 s := by
 simp [HaveSecureEL2Ext,HasArchVersion,readReg,h.v81,h.v82,h.v83,h.v84,h.v85,
 EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,EStateM.get,getThe]
 cases v.v84 <;> rfl

theorem stateK_run (s : State) (h : Ready s) (v : ReturnConfig.Values)
 (versions : ReturnConfig.Initialized s v) (secure : Bool) :
 ELStateUsingAArch32K EL1 secure s = .ok (true,false) s := by
 simp only [ELStateUsingAArch32K, undefined_bool_eq, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure]
 rw [haveAArch32EL1_run s h]
 simp [HighestELUsingAArch32,h.highest,
 haveEL3_run s h,haveEL2_run s h,host_run s v versions,secureEL2_run s v versions,
 readReg,h.scr,h.hcr,h.scrRW,h.hcrRW,undefined_bool_eq,
 EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,EStateM.get,getThe]

 all_goals simp [EL0,EL1,EL3,h.scrRW,h.hcrRW,EStateM.pure]

theorem el1_run (b : Boundaries) (s : State) (h : Ready s) (v : ReturnConfig.Values)
 (versions : ReturnConfig.Initialized s v) :
 (ELUsingAArch32 b EL1).run s = .ok false s := by
 have sr : IsSecureBelowEL3 b () s = .ok (BitVec.join1 [BitVec.access h.scrValue 0] == 0#1) s := secure_run b s h
 simp [ELUsingAArch32,ELStateUsingAArch32,sr,stateK_run s h v versions,
 undefined_bool_eq,PreSail.assert,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure]
/-- All remaining callbacks are quantified, including state-changing failures. -/
theorem callbacks_irrelevant (b c : Boundaries) (s : State) (h : Ready s)
 (v : ReturnConfig.Values) (versions : ReturnConfig.Initialized s v) :
 (ELUsingAArch32 b EL1).run s = (ELUsingAArch32 c EL1).run s := by
 rw [el1_run b s h v versions, el1_run c s h v versions]

theorem hostile_callbacks (b : Boundaries) (s after : State) (h : Ready s)
 (v : ReturnConfig.Values) (versions : ReturnConfig.Initialized s v)
 (err : Sail.Error ReturnExecution.exception) :
 (ELUsingAArch32 {b with
   get_SCR := (fun _ _ => .error err after)
   __IMPDEF_boolean := (fun _ _ => .error err after)} EL1).run s = .ok false s :=
 el1_run _ s h v versions

def withValues (s : State) : State :=
 {s with regs := ((((((s.regs.insert .CFG_ID_AA64PFR0_EL1_EL0 2).insert
 .CFG_ID_AA64PFR0_EL1_EL1 2).insert .CFG_ID_AA64PFR0_EL1_EL2 2).insert
 .CFG_ID_AA64PFR0_EL1_EL3 2).insert .__highest_el_aarch32 false).insert
 .SCR_EL3 1024).insert .HCR_EL2 2147483648}

def withValues_ready (s : State) : Ready (withValues s) := by
 refine ⟨?_,?_,1024,?_,by decide,2147483648,?_,by decide⟩
 · constructor <;> simp [withValues,Std.ExtDHashMap.get?_insert]
 all_goals simp [withValues,Std.ExtDHashMap.get?_insert]

theorem withValues_preserves_versions (s : State) (v : ReturnConfig.Values)
 (h : ReturnConfig.Initialized s v) : ReturnConfig.Initialized (withValues s) v := by
 rcases h with ⟨h1,h2,h3,h4,h5⟩
 constructor <;> simp_all [withValues,Std.ExtDHashMap.get?_insert]

theorem withValues_preserves_mode (s : State) (ps : ProcState) (v : ReturnMode.Values)
 (h : ReturnMode.Ready s ps v) : ReturnMode.Ready (withValues s) ps {} := by
 rcases h with ⟨cfg,hi,hp,hn⟩
 constructor
 · constructor <;> simp [withValues,Std.ExtDHashMap.get?_insert]
 all_goals simp_all [withValues,Std.ExtDHashMap.get?_insert]

theorem withValues_frame (s : State) :
 (withValues s).regs.get? Register.PSTATE = s.regs.get? Register.PSTATE ∧
 (withValues s).regs.get? Register._R = s.regs.get? Register._R ∧
 (withValues s).regs.get? Register.TCR_EL1 = s.regs.get? Register.TCR_EL1 ∧
 (withValues s).mem = s.mem ∧ (withValues s).tags = s.tags := by
 simp [withValues,Std.ExtDHashMap.get?_insert]

def initialized (s : State) : State := withValues (ReturnConfig.withValues s {})

theorem initialized_run (b : Boundaries) (s : State) :
 (ELUsingAArch32 b EL1).run (initialized s) = .ok false (initialized s) :=
 el1_run b _ (withValues_ready _) {} (withValues_preserves_versions _ _ (ReturnConfig.withValues_valid s {}))

theorem scr_other_branch (b : Boundaries) (s : State)
 (el3 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL3 = some (2 : BitVec 4))
 (highest : s.regs.get? Register.__highest_el_aarch32 = some true) :
 (aget_SCR_GEN b ()).run s = (b.get_SCR ()).run s := by
 simp [aget_SCR_GEN,HaveEL,EL0,EL1,EL2,EL3,HighestELUsingAArch32,el3,highest,
 readReg,undefined_bits_eq,PreSail.assert,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
 MonadStateOf.get,MonadState.get,EStateM.get,getThe]

theorem secure_other_branch (b : Boundaries) (s : State)
 (el3 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL3 = some (0 : BitVec 4))
 (el2 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL2 = some (0 : BitVec 4))
 (highest : s.regs.get? Register.__highest_el_aarch32 = some false)
 (v : ReturnConfig.Values) (versions : ReturnConfig.Initialized s v) :
 (IsSecureBelowEL3 b ()).run s = (b.__IMPDEF_boolean "Secure-only implementation").run s := by
 simp [IsSecureBelowEL3,HaveEL,EL0,EL1,EL2,EL3,HighestELUsingAArch32,el3,el2,highest,
 secureEL2_run s v versions,readReg,EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,
 MonadStateOf.get,MonadState.get,EStateM.get,getThe]

def without (s : State) (r : Register) : State := {s with regs := s.regs.erase r}
def requiredRegisters : List Register := [.CFG_ID_AA64PFR0_EL1_EL0,.CFG_ID_AA64PFR0_EL1_EL1,
 .CFG_ID_AA64PFR0_EL1_EL2,.CFG_ID_AA64PFR0_EL1_EL3,.__highest_el_aarch32,.SCR_EL3,.HCR_EL2,
 .__v81_implemented,.__v82_implemented,.__v83_implemented,.__v84_implemented,.__v85_implemented]

set_option maxHeartbeats 2000000 in
theorem each_missing_read_fails (b : Boundaries) (s : State) (r : Register)
 (required : r ∈ requiredRegisters) :
 (ELUsingAArch32 b EL1).run (without (initialized s) r) =
 .error .Unreachable (without (initialized s) r) := by
 simp only [requiredRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,Bool.false_eq_true,or_false] at required
 rcases required with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
 all_goals simp [ELUsingAArch32,ELStateUsingAArch32,ELStateUsingAArch32K,IsSecureBelowEL3,
 aget_SCR_GEN,HaveAArch32EL,HaveEL,HaveAnyAArch32,HighestEL,HighestELUsingAArch32,
 HaveVirtHostExt,HaveSecureEL2Ext,HasArchVersion,EL0,EL1,EL2,EL3,
 without,initialized,withValues,ReturnConfig.withValues,Std.ExtDHashMap.get?_erase,
 Std.ExtDHashMap.get?_insert,undefined_bool_eq,undefined_bits_eq,readReg,PreSail.assert,
 EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,
 EStateM.get,getThe,throw,throwThe,MonadExceptOf.throw,EStateM.throw]

def controls (s : State) (scr : BitVec 32) (hcr : BitVec 64) : State :=
 {initialized s with regs := ((initialized s).regs.insert .SCR_EL3 scr).insert .HCR_EL2 hcr}

theorem scr_rw_clear_returns_aarch32 (b : Boundaries) (s : State) :
 (ELUsingAArch32 b EL1).run (controls s 0 2147483648) = .ok true (controls s 0 2147483648) := by
 simp [ELUsingAArch32,ELStateUsingAArch32,ELStateUsingAArch32K,IsSecureBelowEL3,
 aget_SCR_GEN,HaveAArch32EL,HaveEL,HaveAnyAArch32,HighestEL,HighestELUsingAArch32,
 HaveVirtHostExt,HaveSecureEL2Ext,HasArchVersion,EL0,EL1,EL2,EL3,
 controls,initialized,withValues,ReturnConfig.withValues,Std.ExtDHashMap.get?_insert,
 undefined_bool_eq,undefined_bits_eq,readReg,PreSail.assert,
 EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,
 EStateM.get,getThe]
 decide +kernel

theorem nonsecure_hcr_rw_clear_returns_aarch32 (b : Boundaries) (s : State) :
 (ELUsingAArch32 b EL1).run (controls s 1025 0) = .ok true (controls s 1025 0) := by
 simp [ELUsingAArch32,ELStateUsingAArch32,ELStateUsingAArch32K,IsSecureBelowEL3,
 aget_SCR_GEN,HaveAArch32EL,HaveEL,HaveAnyAArch32,HighestEL,HighestELUsingAArch32,
 HaveVirtHostExt,HaveSecureEL2Ext,HasArchVersion,EL0,EL1,EL2,EL3,
 controls,initialized,withValues,ReturnConfig.withValues,Std.ExtDHashMap.get?_insert,
 undefined_bool_eq,undefined_bits_eq,readReg,PreSail.assert,
 EStateM.run,Bind.bind,Pure.pure,EStateM.bind,EStateM.pure,MonadStateOf.get,MonadState.get,
 EStateM.get,getThe]
 decide +kernel

end Oak.SailBridge.ReturnELMode
