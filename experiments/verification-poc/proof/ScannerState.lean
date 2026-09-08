import BoundedDecimal

/-! A byte-list model of rup_token. Refinement of compiled Oak is tested separately. -/
set_option autoImplicit false
namespace OakVerification.Scanner
open OakVerification.Decimal

def space (b : Nat) : Bool := b == 32 || b == 9 || b == 13 || b == 11 || b == 12
def wordByte (b : Nat) : Bool := b != 10 && !space b

def countWhile (p : Nat → Bool) : List Nat → Nat
  | [] => 0
  | b :: bs => if p b then 1 + countWhile p bs else 0

theorem countWhile_bounds (p : Nat → Bool) (bs : List Nat) :
    countWhile p bs ≤ bs.length := by
  induction bs with
  | nil => simp [countWhile]
  | cons b bs ih => simp only [countWhile, List.length_cons]; split <;> omega

-- The implementation uses the pre-multiplication threshold guard.
def advance (n b : Nat) : Option Nat :=
  (decodeDigit b).bind (fun d => step n d.val)

-- The relation below instead uses an unbounded arithmetic specification.
def specAdvance (n b : Nat) : Option Nat :=
  if 48 ≤ b ∧ b ≤ 57 then
    if n * 10 + (b - 48) ≤ limit then some (n * 10 + (b - 48)) else none
  else none

theorem advance_refines (n b : Nat) : advance n b = specAdvance n b := by
  unfold advance decodeDigit specAdvance
  split
  · rename_i hb
    simp only [Option.bind, step_refines, specStep]
    have hd : b - 48 < 10 := by omega
    simp [hd]
  · simp_all

structure Digits where
  used : Nat
  magnitude : Nat
  valid : Bool
  deriving BEq, Repr

def walk (n : Nat) : List Nat → Digits
  | [] => ⟨0, n, true⟩
  | b :: bs => match advance n b with
    | none => ⟨1, n, false⟩
    | some next => let r := walk next bs; ⟨1 + r.used, r.magnitude, r.valid⟩

-- Independent relational specification: consume exactly a bounded numeric
-- prefix; on failure consume the offending byte and retain the previous value.
inductive Trace : Nat → List Nat → Digits → Prop
  | done (n : Nat) : Trace n [] ⟨0, n, true⟩
  | reject (n b : Nat) (bs : List Nat) (h : specAdvance n b = none) :
      Trace n (b :: bs) ⟨1, n, false⟩
  | digit (n b next : Nat) (bs : List Nat) (r : Digits)
      (h : specAdvance n b = some next) (tail : Trace next bs r) :
      Trace n (b :: bs) ⟨1 + r.used, r.magnitude, r.valid⟩

theorem walk_trace (n : Nat) (bs : List Nat) : Trace n bs (walk n bs) := by
  induction bs generalizing n with
  | nil => exact Trace.done n
  | cons b bs ih =>
    simp only [walk]
    cases h : advance n b with
    | none => exact Trace.reject n b bs (by rwa [advance_refines] at h)
    | some next =>
      exact Trace.digit n b next bs (walk next bs)
        (by rwa [advance_refines] at h) (ih next)

theorem trace_bounds {n : Nat} {bs : List Nat} {r : Digits}
    (h : Trace n bs r) (hn : n ≤ limit) :
    r.used ≤ bs.length ∧ r.magnitude ≤ limit ∧
      (r.valid = true → r.used = bs.length) := by
  induction h with
  | done n => simp_all
  | reject n b bs h => simp_all
  | digit n b next bs r h tail ih =>
    have hb : next ≤ limit := by
      unfold specAdvance at h
      split at h
      · split at h
        · simp only [Option.some.injEq] at h; subst next; assumption
        · simp at h
      · simp at h
    obtain ⟨hu, hm, hv⟩ := ih hb
    simp only [List.length_cons]
    exact ⟨by omega, hm, by intro hh; have := hv hh; omega⟩

theorem walk_bounds (n : Nat) (bs : List Nat) (hn : n ≤ limit) :
    (walk n bs).used ≤ bs.length ∧ (walk n bs).magnitude ≤ limit ∧
      ((walk n bs).valid = true → (walk n bs).used = bs.length) :=
  trace_bounds (walk_trace n bs) hn

-- Sign-only words reject without scanning a digit. The digit cursor is local:
-- the outer scanner has already found the end of the entire word.
def numeric (bs : List Nat) : Nat × Nat :=
  let (tag, ds) := match bs with
    | 43 :: rest => (1, rest)
    | 45 :: rest => (2, rest)
    | rest => (1, rest)
  if ds.isEmpty then (0, 0) else
    let r := walk 0 ds
    (r.magnitude, if r.valid then tag else 0)

structure Token where
  kind : Nat
  next : Nat
  start : Nat
  stop : Nat
  magnitude : Nat
  sign : Nat
  deriving BEq, Repr

def scanTail (pos : Nat) (tail : List Nat) : Token :=
  let skipped := countWhile space tail
  let start := pos + skipped
  match tail.drop skipped with
  | [] => ⟨0, start, start, start, 0, 1⟩
  | b :: bs =>
    if b = 10 then ⟨1, start + 1, start, start + 1, 0, 1⟩ else
      let size := 1 + countWhile wordByte bs
      let number := numeric ((b :: bs).take size)
      ⟨2, start + size, start, start + size, number.1, number.2⟩

def scan (bytes : List Nat) (pos : Nat) : Token := scanTail pos (bytes.drop pos)

-- A representation invariant for the externally visible cursor and token range.
def InRange (pos size : Nat) (t : Token) : Prop :=
  pos ≤ t.start ∧ t.start ≤ t.next ∧ t.next ≤ size ∧ t.stop = t.next ∧
    (t.kind ≠ 0 → pos < t.next)

theorem scanTail_range (pos : Nat) (tail : List Nat) :
    InRange pos (pos + tail.length) (scanTail pos tail) := by
  have hc := countWhile_bounds space tail
  have hl : (tail.drop (countWhile space tail)).length + countWhile space tail = tail.length := by
    rw [List.length_drop]; omega
  unfold scanTail InRange
  generalize hr : tail.drop (countWhile space tail) = rest at *
  cases rest with
  | nil => simp_all
  | cons b bs =>
    have hw := countWhile_bounds wordByte bs
    simp only [List.length_cons] at hl
    by_cases hb : b = 10
    · simp only [hr, if_pos hb]; omega
    · simp only [hr, if_neg hb]; omega

theorem scan_range (bytes : List Nat) (pos : Nat) (hp : pos ≤ bytes.length) :
    InRange pos bytes.length (scan bytes pos) := by
  have h := scanTail_range pos (bytes.drop pos)
  have he : pos + (bytes.drop pos).length = bytes.length := by rw [List.length_drop]; omega
  rw [he] at h
  exact h

theorem scan_no_wrap (bytes : List Nat) (pos : Nat)
    (hp : pos ≤ bytes.length) (hs : bytes.length ≤ 65536) :
    (scan bytes pos).next % modulus = (scan bytes pos).next := by
  obtain ⟨_, _, hn, _, _⟩ := scan_range bytes pos hp
  apply Nat.mod_eq_of_lt
  unfold modulus
  omega

#print axioms countWhile_bounds
#print axioms advance_refines
#print axioms walk_trace
#print axioms trace_bounds
#print axioms walk_bounds
#print axioms scanTail_range
#print axioms scan_range
#print axioms scan_no_wrap
end OakVerification.Scanner
