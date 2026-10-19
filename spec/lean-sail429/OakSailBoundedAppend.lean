import OakSailEntryChecks

/-! Composition of the actual bounded platform callback iterator. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
noncomputable section
namespace OakSailBoundedAppend
open LeanRV64D LeanRV64D.Functions Sail Sail.ConcurrencyInterfaceV1
open OakSailBridge.BitwiseDecoded OakSailPlatformCallback

private theorem bind_ok_inv {α β : Type} (action : SailM α) (next : α → SailM β)
    (s u : State) (b : β)
    (h : (action >>= next).run s = .ok b u) :
    ∃ a t, action.run s = .ok a t ∧ (next a).run t = .ok b u := by
  simp only [EStateM.run, Bind.bind, EStateM.bind] at h ⊢
  split at h
  · exact ⟨_, _, ‹_›, h⟩
  · contradiction

/-- A callback which returns `done` has not changed either state or cursor,
and its state records that the platform has stopped. -/
theorem callback_done (s t : State) (before after : Nat × Nat)
    (h : (platformCallback () before).run s = .ok (.done after) t) :
    after = before ∧ t = s ∧ t.regs.get? Register.htif_done = some true := by
  rcases before with ⟨phase,step⟩
  unfold platformCallback at h
  cases hd : s.regs.get? Register.htif_done with
  | none =>
      obtain ⟨_, _, hread, _⟩ := bind_ok_inv _ _ _ _ _ h
      simp [PreSail.readReg, EStateM.run, Bind.bind, EStateM.bind,
        MonadState.get, getThe, MonadStateOf.get, EStateM.get,
        Pure.pure, EStateM.pure, hd] at hread
      change EStateM.Result.error Sail.Error.Unreachable s = _ at hread
      contradiction
  | some b =>
      rw [bind_run_ok _ _ (read_register s Register.htif_done b hd)] at h
      cases b with
      | true =>
          simp [Functions.not] at h
          obtain ⟨rfl,rfl⟩ := h
          exact ⟨rfl,rfl,hd⟩
      | false =>
          simp only [Functions.not, Bool.not_false, if_true] at h
          obtain ⟨stepped, s₁, _, h⟩ := bind_ok_inv _ _ _ _ _ h
          cases stepped with
          | false =>
              simp only [Bool.false_eq_true, if_false, pure_bind] at h
              obtain ⟨done, s₂, _, h⟩ := bind_ok_inv _ _ _ _ _ h
              cases done <;> simp only [Functions.not, Bool.not_false, Bool.not_true,
                Bool.false_eq_true, if_false, if_true, pure_bind] at h
              · split at h
                · obtain ⟨_, _, _, h⟩ := bind_ok_inv _ _ _ _ _ h
                  simp [EStateM.run, Pure.pure, EStateM.pure] at h
                · simp [EStateM.run, Pure.pure, EStateM.pure] at h
              · simp [EStateM.run, Pure.pure, EStateM.pure] at h
          | true =>
              simp only [if_true] at h
              obtain ⟨_, s₂, _, h⟩ := bind_ok_inv _ _ _ _ _ h
              simp only [pure_bind] at h
              obtain ⟨done, s₃, _, h⟩ := bind_ok_inv _ _ _ _ _ h
              cases done <;> simp only [Functions.not, Bool.not_false, Bool.not_true,
                Bool.false_eq_true, if_false, if_true, pure_bind] at h
              · split at h
                · obtain ⟨_, _, _, h⟩ := bind_ok_inv _ _ _ _ _ h
                  simp [EStateM.run, Pure.pure, EStateM.pure] at h
                · simp [EStateM.run, Pure.pure, EStateM.pure] at h
              · simp [EStateM.run, Pure.pure, EStateM.pure] at h

/-- Once the platform has stopped, every bounded run is a pure identity. -/
theorem bounded_stopped (count : Nat) (s : State) (cursor : Nat × Nat)
    (hd : s.regs.get? Register.htif_done = some true) :
    (boundedPlatform count cursor).run s = .ok cursor s := by
  cases count with
  | zero => rfl
  | succ count =>
      rcases cursor with ⟨phase,step⟩
      simp only [boundedPlatform]
      rw [bind_run_ok _ _ (stopped_callback s phase step hd)]
      rfl

/-- Append a successful bounded run to a successful prefix. This remains
valid when the prefix stopped early, since the stop branch is absorbing. -/
theorem bounded_append (n m : Nat) (s t u : State)
    (start middle finish : Nat × Nat)
    (hprefix : (boundedPlatform n start).run s = .ok middle t)
    (hrest : (boundedPlatform m middle).run t = .ok finish u) :
    (boundedPlatform (n+m) start).run s = .ok finish u := by
  induction n generalizing s start with
  | zero =>
      change EStateM.Result.ok start s = .ok middle t at hprefix
      cases hprefix
      simpa only [Nat.zero_add] using hrest
  | succ n ih =>
      rw [Nat.succ_add]
      simp only [boundedPlatform] at hprefix ⊢
      obtain ⟨result, nextState, hcallback, hnext⟩ := bind_ok_inv _ _ _ _ _ hprefix
      rw [bind_run_ok _ _ hcallback]
      cases result with
      | done stopped =>
          have hd := callback_done s nextState start stopped hcallback
          change EStateM.Result.ok stopped nextState = .ok middle t at hnext
          cases hnext
          have hs := bounded_stopped m t middle hd.2.2
          rw [hs] at hrest
          exact hrest
      | yield next =>
          exact ih nextState next hnext

end OakSailBoundedAppend
