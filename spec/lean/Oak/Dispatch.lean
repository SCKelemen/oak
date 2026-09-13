/-!
# Processor-feature dispatch

`docs/spec/93-simd.md` §6: a function's `dispatch { f₁: r₁, f₂: r₂ }`
clause names realizations selected once, at startup, by the features the
processor has. Selection is a function of the available features and the
clause; it yields the body when no slot applies, and never anything but
the body or a listed realization. The claim that a realization equals the
body is the author's, checked differentially; `dispatch_sound` says that
claim is the only thing left to check.
-/

namespace Oak.Dispatch

variable {Feature R : Type}

/-- The first slot whose feature is available, else the body. -/
def select (available : Feature → Bool) : List (Feature × R) → R → R
  | [], body => body
  | (f, r) :: rest, body => if available f then r else select available rest body

/-- No available feature: the body runs. -/
theorem select_none (available : Feature → Bool) (body : R) :
    ∀ slots : List (Feature × R), (∀ s ∈ slots, available s.1 = false) →
      select available slots body = body := by
  intro slots
  induction slots with
  | nil => intro _; rfl
  | cons s rest ih =>
    intro h
    simp only [select]
    rw [h s (List.mem_cons_self ..)]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ih (fun t ht => h t (List.mem_cons_of_mem _ ht))

/-- The selection is the body or a listed realization, nothing else. -/
theorem select_mem (available : Feature → Bool) (body : R) :
    ∀ slots : List (Feature × R),
      select available slots body = body ∨ ∃ s ∈ slots, select available slots body = s.2 := by
  intro slots
  induction slots with
  | nil => exact Or.inl rfl
  | cons s rest ih =>
    simp only [select]
    by_cases h : available s.1 = true
    · rw [if_pos h]
      exact Or.inr ⟨s, List.mem_cons_self .., rfl⟩
    · rw [if_neg h]
      rcases ih with hb | ⟨t, ht, hts⟩
      · exact Or.inl hb
      · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, hts⟩

/-- The selection is deterministic: it is a function. Two processors with
    the same available features select the same realization. -/
theorem select_deterministic (a b : Feature → Bool) (slots : List (Feature × R)) (body : R)
    (h : ∀ f, a f = b f) : select a slots body = select b slots body := by
  have : a = b := funext h
  rw [this]

/-- **Soundness of the claim.** When every listed realization denotes the
    body's function, so does the dispatched function, on every processor. -/
theorem dispatch_sound {D : Type} (denote : R → D) (available : Feature → Bool)
    (slots : List (Feature × R)) (body : R)
    (hclaim : ∀ s ∈ slots, denote s.2 = denote body) :
    denote (select available slots body) = denote body := by
  rcases select_mem available body slots with hb | ⟨s, hs, hsel⟩
  · rw [hb]
  · rw [hsel]; exact hclaim s hs

/-- The static rule: a feature the baseline guarantees is available on
    every processor the binary runs on, so a clause whose first slot is
    such a feature always selects that realization. -/
theorem select_static (available : Feature → Bool) (f : Feature) (r : R)
    (rest : List (Feature × R)) (body : R) (h : available f = true) :
    select available ((f, r) :: rest) body = r := by
  simp [select, h]

end Oak.Dispatch
