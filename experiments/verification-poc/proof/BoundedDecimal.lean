import Std.Tactic

/-! Arithmetic refinement for the bounded decimal core used by rup_token.
    These are proofs about this executable model, not about Oak compiler output. -/
set_option autoImplicit false
namespace OakVerification.Decimal

def limit : Nat := 2147483647
def modulus : Nat := 4294967296

def step (n d : Nat) : Option Nat :=
  if d < 10 then
    if n > 214748364 || (n = 214748364 ∧ d > 7) then none
    else some (n * 10 + d)
  else none

def specStep (n d : Nat) : Option Nat :=
  if d < 10 then
    if n * 10 + d ≤ limit then some (n * 10 + d) else none
  else none

theorem step_refines (n d : Nat) : step n d = specStep n d := by
  unfold step specStep limit
  by_cases hd : d < 10
  · simp only [if_pos hd]
    by_cases hg : n > 214748364 ∨ (n = 214748364 ∧ d > 7)
    · have hb : ¬ n * 10 + d ≤ 2147483647 := by omega
      simp [hg, hb]
    · have hb : n * 10 + d ≤ 2147483647 := by omega
      simp [hg, hb]
  · simp [hd]

theorem step_bounds {n d r : Nat} (h : step n d = some r) :
    d < 10 ∧ r = n * 10 + d ∧ r ≤ limit := by
  rw [step_refines] at h
  unfold specStep at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst r
      exact ⟨by assumption, rfl, by assumption⟩
    · simp at h
  · simp at h

-- The multiplication and addition are both representable before a u32 store.
theorem step_no_wrap {n d r : Nat} (h : step n d = some r) :
    n * 10 < modulus ∧ n * 10 + d < modulus ∧
      (n * 10 + d) % modulus = r := by
  obtain ⟨_, hr, hb⟩ := step_bounds h
  have hsum : n * 10 + d < modulus := by unfold limit at hb; unfold modulus; omega
  refine ⟨by omega, hsum, ?_⟩
  rw [Nat.mod_eq_of_lt hsum]
  exact hr.symm

def value (n : Nat) : List (Fin 10) → Nat
  | [] => n
  | d :: ds => value (n * 10 + d.val) ds

theorem value_ge (n : Nat) (ds : List (Fin 10)) : n ≤ value n ds := by
  induction ds generalizing n with
  | nil => simp [value]
  | cons d ds ih =>
    simp only [value]
    have h := ih (n * 10 + d.val)
    omega

def run (n : Nat) : List (Fin 10) → Option Nat
  | [] => if n ≤ limit then some n else none
  | d :: ds => (step n d.val).bind (fun next => run next ds)

-- Early overflow rejection is equivalent to computing with unbounded naturals
-- and checking only the final mathematical value (including leading zeroes).
theorem run_refines (n : Nat) (ds : List (Fin 10)) :
    run n ds = if value n ds ≤ limit then some (value n ds) else none := by
  induction ds generalizing n with
  | nil => rfl
  | cons d ds ih =>
    simp only [run, value, step_refines, specStep, if_pos d.isLt]
    by_cases hb : n * 10 + d.val ≤ limit
    · simp only [if_pos hb]
      exact ih (n * 10 + d.val)
    · have hv := value_ge (n * 10 + d.val) ds
      have he : ¬ value (n * 10 + d.val) ds ≤ limit := by omega
      simp [hb, he]

def decodeDigit (b : Nat) : Option (Fin 10) :=
  if h : 48 ≤ b ∧ b ≤ 57 then some ⟨b - 48, by omega⟩ else none

theorem decodeDigit_refines (b : Nat) :
    (decodeDigit b).map Fin.val =
      if 48 ≤ b ∧ b ≤ 57 then some (b - 48) else none := by
  unfold decodeDigit
  split <;> simp_all

def unsignedWith (worker : List (Fin 10) → Option Nat) (bytes : List Nat) : Option Nat :=
  if bytes.isEmpty then none else (bytes.mapM decodeDigit).bind worker

def parseUnsigned : List Nat → Option Nat := unsignedWith (run 0)
def specUnsigned : List Nat → Option Nat :=
  unsignedWith (fun ds => if value 0 ds ≤ limit then some (value 0 ds) else none)

theorem parseUnsigned_refines : parseUnsigned = specUnsigned := by
  have h : run 0 = fun ds => if value 0 ds ≤ limit then some (value 0 ds) else none :=
    funext (run_refines 0)
  unfold parseUnsigned specUnsigned
  rw [h]

structure Signed where
  negative : Bool
  magnitude : Nat
  deriving BEq, Repr

def signedWith (parser : List Nat → Option Nat) : List Nat → Option Signed
  | 43 :: rest => (parser rest).map (fun n => ⟨false, n⟩)
  | 45 :: rest => (parser rest).map (fun n => ⟨true, n⟩)
  | bytes => (parser bytes).map (fun n => ⟨false, n⟩)

def parseSigned := signedWith parseUnsigned
def specSigned := signedWith specUnsigned

theorem parseSigned_refines : parseSigned = specSigned := by
  unfold parseSigned specSigned
  rw [parseUnsigned_refines]

-- The same subtraction-based range guard is used throughout the Oak decoder.
def rangeSafe (start count size : Nat) : Prop := start ≤ size ∧ count ≤ size - start

theorem rangeSafe_refines (start count size : Nat) :
    rangeSafe start count size ↔ start + count ≤ size := by
  unfold rangeSafe
  omega

theorem range_index {start count size offset : Nat}
    (h : rangeSafe start count size) (hi : offset < count) : start + offset < size := by
  rw [rangeSafe_refines] at h
  omega

theorem append_bounds {used capacity : Nat} (h : used < capacity) :
    used < capacity ∧ used + 1 ≤ capacity := by omega

theorem append_no_wrap {used capacity : Nat}
    (h : used < capacity) (hc : capacity < modulus) :
    (used + 1) % modulus = used + 1 := by
  apply Nat.mod_eq_of_lt
  omega

theorem cursor_progress {pos size : Nat} (h : pos < size) (hs : size ≤ 65536) :
    pos < pos + 1 ∧ pos + 1 ≤ size ∧ (pos + 1) % modulus = pos + 1 := by
  refine ⟨by omega, by omega, ?_⟩
  apply Nat.mod_eq_of_lt
  unfold modulus
  omega

#print axioms step_refines
#print axioms step_no_wrap
#print axioms run_refines
#print axioms decodeDigit_refines
#print axioms parseUnsigned_refines
#print axioms parseSigned_refines
#print axioms rangeSafe_refines
#print axioms range_index
#print axioms append_bounds
#print axioms append_no_wrap
#print axioms cursor_progress
end OakVerification.Decimal
