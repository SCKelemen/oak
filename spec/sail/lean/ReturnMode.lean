import ReturnConfig
namespace Oak.SailBridge.ReturnMode
open ReturnExecution ReturnExecution.Functions Sail PreSail
set_option linter.unusedSimpArgs false
abbrev State := ReturnConfig.State
structure Values where
 el0 : BitVec 4 := 2
 el1 : BitVec 4 := 2
 el2 : BitVec 4 := 2
 el3 : BitVec 4 := 2
structure Config (s : State) (v : Values) : Prop where
 el0 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL0 = some v.el0
 el1 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL1 = some v.el1
 el2 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL2 = some v.el2
 el3 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL3 = some v.el3
structure Ready (s : State) (ps : ProcState) (v : Values) extends Config s v : Prop where
 highest : s.regs.get? Register.__highest_el_aarch32 = some false
 pstate : s.regs.get? Register.PSTATE = some ps
 nrw : ps.nRW = 0

def supports (v : Values) : Bool := v.el0 == 2 || v.el1 == 2 || v.el2 == 2 || v.el3 == 2

theorem haveAny_run (s : State) (v : Values) (h : Config s v) :
 (HaveAnyAArch32 ()).run s = .ok (supports v) s := by
 simp [HaveAnyAArch32, supports, readReg, h.el0, h.el1, h.el2, h.el3,
 EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe]

theorem using_run (s : State) (ps : ProcState) (v : Values) (h : Ready s ps v) :
 (UsingAArch32 ()).run s = .ok false s := by
 have any : HaveAnyAArch32 () s = .ok (supports v) s := haveAny_run s v h.toConfig
 cases hs : supports v <;>
 simp [UsingAArch32, HighestELUsingAArch32, any, hs, h.highest, h.pstate, h.nrw,
 readReg, PreSail.assert, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe]

def withValues (s : State) (ps : ProcState) (v : Values) : State :=
 {s with regs := (((((s.regs.insert .CFG_ID_AA64PFR0_EL1_EL0 v.el0).insert .CFG_ID_AA64PFR0_EL1_EL1 v.el1).insert .CFG_ID_AA64PFR0_EL1_EL2 v.el2).insert .CFG_ID_AA64PFR0_EL1_EL3 v.el3).insert .__highest_el_aarch32 false).insert .PSTATE {ps with nRW := 0}}

theorem withValues_ready (s : State) (ps : ProcState) (v : Values) :
 Ready (withValues s ps v) {ps with nRW := 0} v := by
 constructor
 · constructor <;> simp [withValues, Std.ExtDHashMap.get?_insert]
 all_goals simp [withValues, Std.ExtDHashMap.get?_insert]

theorem withValues_runs (s : State) (ps : ProcState) (v : Values) :
 (UsingAArch32 ()).run (withValues s ps v) = .ok false (withValues s ps v) :=
 using_run _ _ _ (withValues_ready s ps v)
/-- The constructive mode witness does not disturb operand/return inputs or memory. -/
theorem withValues_frame (s : State) (ps : ProcState) (v : Values) :
 (withValues s ps v).regs.get? Register._R = s.regs.get? Register._R ∧
 (withValues s ps v).regs.get? Register.TCR_EL1 = s.regs.get? Register.TCR_EL1 ∧
 (withValues s ps v).mem = s.mem ∧ (withValues s ps v).tags = s.tags := by
 simp [withValues, Std.ExtDHashMap.get?_insert]

theorem withValues_preserves_versions (s : State) (ps : ProcState) (v : Values)
 (versions : ReturnConfig.Values) (h : ReturnConfig.Initialized s versions) :
 ReturnConfig.Initialized (withValues s ps v) versions := by
 rcases h with ⟨h1,h2,h3,h4,h5⟩
 constructor <;> simp_all [withValues, Std.ExtDHashMap.get?_insert]

theorem missing_pstate (s : State) (missing : s.regs.get? Register.PSTATE = none) :
 (UsingAArch32 ()).run s = .error .Unreachable s := by
 simp [UsingAArch32, readReg, missing, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe, throw, throwThe,
 MonadExceptOf.throw, EStateM.throw]

theorem missing_el0 (s : State) (ps : ProcState)
 (pstate : s.regs.get? Register.PSTATE = some ps)
 (missing : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL0 = none) :
 (UsingAArch32 ()).run s = .error .Unreachable s := by
 simp [UsingAArch32, HaveAnyAArch32, readReg, pstate, missing, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe, throw, throwThe,
 MonadExceptOf.throw, EStateM.throw]

theorem missing_el1 (s : State) (ps : ProcState)
 (pstate : s.regs.get? Register.PSTATE = some ps)
 (v0 : BitVec 4) (h0 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL0 = some v0)
 (missing : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL1 = none) :
 (UsingAArch32 ()).run s = .error .Unreachable s := by
 simp [UsingAArch32, HaveAnyAArch32, readReg, pstate, missing, h0, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe, throw, throwThe,
 MonadExceptOf.throw, EStateM.throw]

theorem missing_el2 (s : State) (ps : ProcState)
 (pstate : s.regs.get? Register.PSTATE = some ps)
 (v0 : BitVec 4) (h0 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL0 = some v0)
 (v1 : BitVec 4) (h1 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL1 = some v1)
 (missing : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL2 = none) :
 (UsingAArch32 ()).run s = .error .Unreachable s := by
 simp [UsingAArch32, HaveAnyAArch32, readReg, pstate, missing, h0, h1, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe, throw, throwThe,
 MonadExceptOf.throw, EStateM.throw]

theorem missing_el3 (s : State) (ps : ProcState)
 (pstate : s.regs.get? Register.PSTATE = some ps)
 (v0 : BitVec 4) (h0 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL0 = some v0)
 (v1 : BitVec 4) (h1 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL1 = some v1)
 (v2 : BitVec 4) (h2 : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL2 = some v2)
 (missing : s.regs.get? Register.CFG_ID_AA64PFR0_EL1_EL3 = none) :
 (UsingAArch32 ()).run s = .error .Unreachable s := by
 simp [UsingAArch32, HaveAnyAArch32, readReg, pstate, missing, h0, h1, h2, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe, throw, throwThe,
 MonadExceptOf.throw, EStateM.throw]

theorem missing_highest (s : State) (ps : ProcState) (v : Values) (h : Config s v)
 (pstate : s.regs.get? Register.PSTATE = some ps) (nrw : ps.nRW = 0)
 (highest : s.regs.get? Register.__highest_el_aarch32 = none) :
 (UsingAArch32 ()).run s = .error .Unreachable s := by
 have any : HaveAnyAArch32 () s = .ok (supports v) s := haveAny_run s v h
 cases hs : supports v <;>
 simp [UsingAArch32, HighestELUsingAArch32, any, hs, readReg, pstate, nrw,
 highest, PreSail.assert, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe, throw, throwThe,
 MonadExceptOf.throw, EStateM.throw]

theorem inconsistent_highest (s : State) (ps : ProcState) (v : Values) (h : Config s v)
 (pstate : s.regs.get? Register.PSTATE = some ps) (nrw : ps.nRW = 0)
 (highest : s.regs.get? Register.__highest_el_aarch32 = some true) :
 (UsingAArch32 ()).run s = .error (.Assertion "return.sail:272.22-272.23") s := by
 have any : HaveAnyAArch32 () s = .ok (supports v) s := haveAny_run s v h
 cases hs : supports v <;>
 simp [UsingAArch32, HighestELUsingAArch32, any, hs, readReg, pstate, nrw,
 highest, PreSail.assert, EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe, throw, throwThe,
 MonadExceptOf.throw, EStateM.throw]

theorem inconsistent_unsupported (s : State) (ps : ProcState) (v : Values) (h : Config s v)
 (pstate : s.regs.get? Register.PSTATE = some ps) (nrw : ps.nRW = 1)
 (unsupported : supports v = false) :
 (UsingAArch32 ()).run s = .error (.Assertion "return.sail:269.25-269.26") s := by
 have any : HaveAnyAArch32 () s = .ok (supports v) s := haveAny_run s v h
 simp [UsingAArch32, any, unsupported, readReg, pstate, nrw, PreSail.assert,
 EStateM.run, Bind.bind, Pure.pure, EStateM.bind, EStateM.pure,
 MonadStateOf.get, MonadState.get, EStateM.get, getThe, throw, throwThe,
 MonadExceptOf.throw, EStateM.throw]

end Oak.SailBridge.ReturnMode
