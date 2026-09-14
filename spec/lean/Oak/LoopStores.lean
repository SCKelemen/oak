/-!
# Oak.LoopStores — stores in data-dependent loops through the coupling

The assembler-unit verifier (docs/spec/94-assembler.md §8, thirtieth
increment; `asm/loops.go` verifyLoops) proves a counting loop that stores
one element per iteration not by summarizing its memory but by coupling:
the two sides' loop states are related by the affine coupling `R` the
recognizer finds, the continue conditions agree under `R`, one iteration
preserves `R`, and — the increment's obligation — the store each iteration
makes (its element, its value, its guard) is the same on both sides under
`R`. This module is the semantic content of that argument: two loops so
coupled, run for the same number of steps from the same memory, leave the
same memory (`run_mem_eq`), whatever the states themselves are. The
verifier discharges each obligation at the bit level under the body
premise; the theorem is why those obligations suffice.

A body that reads a span it stores to reads the memory at the start of
the iteration, which the verifier names by one fresh memory symbol on both
sides (`v@loop1`, `spanMemoryName`): the write of an iteration is a
function of the state and of that memory, and the obligation compares the
two sides' writes over the same memory. `run_mem_eq` threads the memory
through the iterations, so equal writes over equal memories keep the
memories equal. A span a loop stores to is closed to reads afterwards
(the final memory is the loop's); the memories before and after the loops
are straight-line logs, compared at a fresh index as `asm/effects.go`
does.
-/

namespace Oak.LoopStores

/-- A memory over indices `ι` holding values `α`. -/
abbrev Mem (ι α : Type) := ι → α

/-- One store: an element, a value, and whether it happens. -/
structure Write (ι α : Type) where
  index : ι
  value : α
  guard : Bool

/-- Applying a store to a memory. -/
def Mem.apply {ι α : Type} [DecidableEq ι] (m : Mem ι α) (w : Write ι α) : Mem ι α :=
  fun j => if w.guard ∧ j = w.index then w.value else m j

/-- A loop over states `σ`: its continue condition, one iteration's
    successor state, and the store one iteration makes — a function of the
    state and of the memory at the start of the iteration (the body's
    reads of the span it stores to). -/
structure Loop (σ ι α : Type) where
  cond : σ → Bool
  step : σ → σ
  write : σ → Mem ι α → Write ι α

/-- Running the loop for at most `fuel` iterations: the state and memory
    it leaves. -/
def run {σ ι α : Type} [DecidableEq ι] (L : Loop σ ι α) : Nat → σ → Mem ι α → σ × Mem ι α
  | 0, s, m => (s, m)
  | n + 1, s, m => if L.cond s = true then run L n (L.step s) (m.apply (L.write s m)) else (s, m)

/-- The coupling the verifier establishes between the Oak loop `L₁` and
    the asm loop `L₂`: under `R` the conditions agree, an iteration
    preserves `R`, and the iteration's stores are equal. -/
structure Coupled {σ₁ σ₂ ι α : Type} (L₁ : Loop σ₁ ι α) (L₂ : Loop σ₂ ι α) (R : σ₁ → σ₂ → Prop) : Prop where
  cond : ∀ s₁ s₂, R s₁ s₂ → L₁.cond s₁ = L₂.cond s₂
  step : ∀ s₁ s₂, R s₁ s₂ → L₁.cond s₁ = true → R (L₁.step s₁) (L₂.step s₂)
  write : ∀ s₁ s₂ m, R s₁ s₂ → L₁.cond s₁ = true → L₁.write s₁ m = L₂.write s₂ m

/-- Coupled loops run from coupled states over one memory leave the same
    memory and coupled states, for every fuel. -/
theorem run_mem_eq {σ₁ σ₂ ι α : Type} [DecidableEq ι] {L₁ : Loop σ₁ ι α} {L₂ : Loop σ₂ ι α}
    {R : σ₁ → σ₂ → Prop} (h : Coupled L₁ L₂ R) :
    ∀ (n : Nat) (s₁ : σ₁) (s₂ : σ₂) (m : Mem ι α), R s₁ s₂ →
      (run L₁ n s₁ m).2 = (run L₂ n s₂ m).2 ∧ R (run L₁ n s₁ m).1 (run L₂ n s₂ m).1 := by
  intro n
  induction n with
  | zero => intro s₁ s₂ m hR; exact ⟨rfl, hR⟩
  | succ n ih =>
    intro s₁ s₂ m hR
    have hc := h.cond s₁ s₂ hR
    by_cases h1 : L₁.cond s₁ = true
    · have h2 : L₂.cond s₂ = true := by rw [← hc]; exact h1
      simp only [run, h1, h2, ↓reduceIte]
      rw [h.write s₁ s₂ m hR h1]
      exact ih _ _ _ (h.step s₁ s₂ hR h1)
    · have h1' : L₁.cond s₁ = false := by simpa using h1
      have h2 : L₂.cond s₂ = false := by rw [← hc]; exact h1'
      simp only [run, h1', h2, Bool.false_eq_true, ↓reduceIte]
      simpa using hR

/-- The memories agree element by element: the final memory of a span is
    the loop's, so the verifier closes the span to later reads and compares
    nothing more. -/
theorem run_mem_eq_at {σ₁ σ₂ ι α : Type} [DecidableEq ι] {L₁ : Loop σ₁ ι α} {L₂ : Loop σ₂ ι α}
    {R : σ₁ → σ₂ → Prop} (h : Coupled L₁ L₂ R) (n : Nat) (s₁ : σ₁) (s₂ : σ₂) (m : Mem ι α)
    (hR : R s₁ s₂) (j : ι) : (run L₁ n s₁ m).2 j = (run L₂ n s₂ m).2 j := by
  rw [(run_mem_eq h n s₁ s₂ m hR).1]

end Oak.LoopStores
