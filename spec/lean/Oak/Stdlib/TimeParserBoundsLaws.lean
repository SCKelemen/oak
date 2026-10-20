import Oak.Stdlib.TimeComponentLaws
/-! # ISO component parser accumulator invariant
These kernel proofs follow the actual extracted loop. They require no input
validity assumption: every returning execution preserves all three bounds,
including grammar failures and overflow paths. Digit and fraction text semantics
are deliberately separate from this accumulator invariant.
-/
namespace Oak.Stdlib.Time
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- State tuple returned by the extracted ISO main loop. -/
abbrev ISOComponentState := UInt32 × UInt64 × UInt64 × UInt64 × Bool × Bool × Bool × Bool × UInt32 × Bool × Bool

/-- Independent calendar and elapsed-time accumulator limits. -/
def iso_component_bounds (s : ISOComponentState) (c t : UInt64) : Prop := s.2.1 ≤ c ∧ s.2.2.1 ≤ c ∧ s.2.2.2.1 ≤ t

/-- Every returned main-loop state preserves the calendar and time magnitude
bounds. Unit selection supplies a positive factor; accepted updates use the
exact checked arithmetic contract. This holds for arbitrary extraction fuel. -/
theorem parse_iso_components_loop_bounds (src : Array UInt8) (fixed : Bool) (n : UInt32) (c t : UInt64) (fuel : Nat) :
  ∀ (at_ : UInt32) (m d ns : UInt64) (it ts a w : Bool) (r : UInt32) (v o : Bool) (out : ISOComponentState),
  m ≤ c → d ≤ c → ns ≤ t →
  parse_iso_components.loop1 src fixed n at_ m d ns c t it ts a w r v o fuel = some out → iso_component_bounds out c t := by
  induction fuel with
  | zero => intros; contradiction
  | succ fuel ih =>
    intro at_ m d ns it ts a w r v o out hm hd hn h
    unfold parse_iso_components.loop1 at h
    split at h
    · simp only [bind, Option.bind_eq_some_iff] at h
      rcases h with ⟨step, hs, he⟩
      have hb : iso_component_bounds step c t := by
        split at hs
        · simp only [pure, Option.some.injEq] at hs
          subst step
          exact ⟨hm, hd, hn⟩
        · simp only [Option.bind_eq_some_iff] at hs
          rcases hs with ⟨⟨pos, ov, value⟩, hp, hs⟩
          rcases hs with ⟨⟨p, valid, fractional, fraction⟩, _, body, hb, hs⟩
          simp only [pure, Option.some.injEq] at hs
          subst step
          simp only [pure, Prod.eta, Option.bind_fun_some] at hb
          split at hb
          · simp only [Option.some.injEq] at hb
            subst body
            exact ⟨hm, hd, hn⟩
          · split at hb
            · simp only [Option.bind_eq_some_iff] at hb
              rcases hb with ⟨⟨seen, wk, rank, factor, bucket⟩, hu, hb⟩
              have huinfo : 0 < factor ∧ (bucket = 0 ∨ bucket = 1 ∨ bucket = 2) := by
                split at hu
                all_goals split at hu
                all_goals try split at hu
                all_goals try split at hu
                all_goals try split at hu
                all_goals simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq] at hu
                all_goals rcases hu with ⟨_, _, _, rfl, rfl⟩ <;> decide
              rcases hb with ⟨updated, hupt, hb⟩
              simp only [Option.some.injEq] at hb
              subst body
              split at hupt
              · simp only [Option.bind_eq_some_iff] at hupt
                rcases hupt with ⟨over, hg, triple, ht, hupt⟩
                simp only [Option.some.injEq] at hupt
                subst updated
                cases over with
                | false =>
                  rcases huinfo.2 with hbucket | hbucket | hbucket
                  all_goals simp [hbucket] at hg ht
                  all_goals subst triple
                  · exact ⟨(iso_component_accept_exact m value factor fraction c fuel hm huinfo.1 hg).2, hd, hn⟩
                  · exact ⟨hm, (iso_component_accept_exact d value factor fraction c fuel hd huinfo.1 hg).2, hn⟩
                  · exact ⟨hm, hd, (iso_component_accept_exact ns value factor fraction t fuel hn huinfo.1 hg).2⟩
                | true =>
                  simp only [Bool.not_true, Bool.false_eq_true, ite_false, Option.some.injEq] at ht
                  subst triple
                  exact ⟨hm, hd, hn⟩
              · simp only [Option.some.injEq] at hupt
                subst updated
                exact ⟨hm, hd, hn⟩
            · simp only [Option.some.injEq] at hb
              subst body
              exact ⟨hm, hd, hn⟩
      exact ih step.1 step.2.1 step.2.2.1 step.2.2.2.1 step.2.2.2.2.1
        step.2.2.2.2.2.1 step.2.2.2.2.2.2.1 step.2.2.2.2.2.2.2.1
        step.2.2.2.2.2.2.2.2.1 step.2.2.2.2.2.2.2.2.2.1 step.2.2.2.2.2.2.2.2.2.2 out hb.1 hb.2.1 hb.2.2 he
    · simp only [pure, Option.some.injEq] at h
      subst out
      exact ⟨hm, hd, hn⟩
end Oak.Stdlib.Time
