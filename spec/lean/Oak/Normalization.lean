namespace Oak.Normalization

/-! # Unicode normalization forms (UAX #15)

Model for `stdlib/normalize.oak`. The Unicode Character Database enters as
an abstract `UCD` — a combining class for every scalar, the full canonical
decomposition of the scalars that have one, and the primary composite of a
pair — so the theorems hold for any data with the shape the standard
guarantees, and the Go law test (`compiler/e2e_stdlib_normalize_laws_test.go`)
checks the compiled Oak against the same definitions instantiated with the
Unicode 17.0.0 extract.

Three definitions are stated, two are proved about:

* `order` is **canonical ordering** (UAX #15 §3.11, D109): each maximal run
  of non-starters is put in non-decreasing order of combining class by a
  stable insertion. `normalize_settle` in the library is this insertion
  applied to one run. Proved: `order` permutes its input
  (`order_perm`), leaves every starter in place and never carries a mark
  across one, yields adjacent-sorted runs (`order_sorted`), keeps the
  relative order of marks with equal class (`order_stable`, stated as the
  filter by class), and is idempotent (`order_idem`).
* `nfd` is canonical decomposition followed by ordering. Proved: `nfd` is
  idempotent (`nfd_idem`) for any UCD whose decompositions are **closed** —
  no scalar in a decomposition itself decomposes — which is what "full
  decomposition" means and what `extract_normalize.py` computes.
* `compose` is canonical composition (D117): each character not blocked from
  the last starter that forms a primary composite with it is absorbed. It is
  defined here so the law test states the same procedure; the composition
  laws (NFC idempotent, `nfd (nfc x) = nfd x`) are **not proved** in this
  file and are recorded as remaining work in STATUS.md — they need the
  primary-composite inverse property of the data, which the conformance
  file exercises but this model does not yet assume. -/

/-- The Unicode data normalization reads. -/
structure UCD where
  /-- Canonical_Combining_Class; 0 is a starter. -/
  ccc : Nat → Nat
  /-- The full canonical decomposition of a scalar that has one. -/
  decomp : Nat → Option (List Nat)
  /-- The primary composite of a pair, when the pair composes. -/
  compose : Nat → Nat → Option Nat

variable (u : UCD)

/-! ## Canonical ordering -/

/-- Insert a non-starter `c` into the run at the head of `xs`: it moves past
    the marks of strictly lower class and stops at a starter or at a mark of
    equal or higher class, so equal classes keep their order. -/
def insertMark (c : Nat) : List Nat → List Nat
  | [] => [c]
  | x :: xs => if u.ccc x ≠ 0 ∧ u.ccc x < u.ccc c then x :: insertMark c xs else c :: x :: xs

/-- Canonical ordering of a whole text: starters stay, marks are inserted. -/
def order : List Nat → List Nat
  | [] => []
  | x :: xs => if u.ccc x = 0 then x :: order xs else insertMark u x (order xs)

/-- Adjacent marks are in non-decreasing class order. -/
def RunSorted : List Nat → Prop
  | a :: b :: rest => (u.ccc a ≠ 0 → u.ccc b ≠ 0 → u.ccc a ≤ u.ccc b) ∧ RunSorted (b :: rest)
  | _ => True

theorem insertMark_perm (c : Nat) : ∀ xs : List Nat, (insertMark u c xs).Perm (c :: xs)
  | [] => List.Perm.refl _
  | x :: xs => by
    unfold insertMark
    split
    · exact ((insertMark_perm c xs).cons x).trans (List.Perm.swap c x xs)
    · exact List.Perm.refl _

theorem order_perm : ∀ l : List Nat, (order u l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => by
    unfold order
    split
    · exact (order_perm xs).cons x
    · exact (insertMark_perm u x (order u xs)).trans ((order_perm xs).cons x)

theorem order_length (l : List Nat) : (order u l).length = l.length :=
  (order_perm u l).length_eq

/-- The head of `insertMark c xs` is `c` or the head of `xs`. -/
theorem insertMark_head (c : Nat) : ∀ xs : List Nat,
    (insertMark u c xs).head? = some c ∨ (insertMark u c xs).head? = xs.head?
  | [] => Or.inl rfl
  | x :: xs => by
    unfold insertMark
    split
    · exact Or.inr rfl
    · exact Or.inl rfl

/-- Inserting a mark into a sorted list keeps it sorted. -/
theorem insertMark_sorted (c : Nat) (hc : u.ccc c ≠ 0) :
    ∀ xs : List Nat, RunSorted u xs → RunSorted u (insertMark u c xs)
  | [], _ => trivial
  | [x], _ => by
    unfold insertMark
    split
    · rename_i h
      exact ⟨fun _ _ => Nat.le_of_lt h.2, trivial⟩
    · rename_i h
      refine ⟨fun _ hx => ?_, trivial⟩
      have : ¬ (u.ccc x < u.ccc c) := fun lt => h ⟨hx, lt⟩
      omega
  | x :: y :: rest, hs => by
    unfold insertMark
    split
    · rename_i h
      have tail := insertMark_sorted c hc (y :: rest) hs.2
      -- the inserted list starts with `c` or with `y`
      rcases insertMark_head u c (y :: rest) with hh | hh
      · match hins : insertMark u c (y :: rest), hh with
        | c' :: rest', hh =>
          simp at hh
          subst hh
          rw [hins] at tail
          exact ⟨fun _ _ => Nat.le_of_lt h.2, tail⟩
      · match hins : insertMark u c (y :: rest), hh with
        | y' :: rest', hh =>
          simp at hh
          subst hh
          rw [hins] at tail
          exact ⟨hs.1, tail⟩
    · rename_i h
      refine ⟨fun _ hx => ?_, hs⟩
      have : ¬ (u.ccc x < u.ccc c) := fun lt => h ⟨hx, lt⟩
      omega

theorem order_sorted : ∀ l : List Nat, RunSorted u (order u l)
  | [] => trivial
  | x :: xs => by
    unfold order
    split
    · rename_i h0
      have tail := order_sorted xs
      match order u xs, tail with
      | [], _ => trivial
      | y :: rest, tail => exact ⟨fun hx _ => absurd h0 hx, tail⟩
    · rename_i h0
      exact insertMark_sorted u x h0 _ (order_sorted xs)

/-- Stability: the marks of one class appear in the same order before and
    after ordering (the filter by class is unchanged). -/
theorem insertMark_filter (c : Nat) (k : Nat) (hk : k ≠ 0) :
    ∀ xs : List Nat, (insertMark u c xs).filter (fun x => u.ccc x == k) =
      (c :: xs).filter (fun x => u.ccc x == k)
  | [] => rfl
  | x :: xs => by
    unfold insertMark
    split
    · rename_i h
      have ih := insertMark_filter c k hk xs
      by_cases hx : u.ccc x = k
      · -- x has class k, so c's class is above k and c is not in the filter
        have hc : u.ccc c ≠ k := by omega
        simp [hx, hc] at ih ⊢
        exact ih
      · simp [List.filter_cons, hx] at ih ⊢
        exact ih
    · rfl

theorem order_filter (k : Nat) (hk : k ≠ 0) :
    ∀ l : List Nat, (order u l).filter (fun x => u.ccc x == k) = l.filter (fun x => u.ccc x == k)
  | [] => rfl
  | x :: xs => by
    unfold order
    split
    · rename_i h0
      have hx : u.ccc x ≠ k := by omega
      simp [hx]
      exact order_filter k hk xs
    · rw [insertMark_filter u x k hk]
      simp [List.filter_cons]
      split <;> simp_all [order_filter k hk xs]

theorem order_stable (k : Nat) (hk : k ≠ 0) (l : List Nat) :
    (order u l).filter (fun x => u.ccc x == k) = l.filter (fun x => u.ccc x == k) :=
  order_filter u k hk l

/-- A sorted run absorbs an insertion at its head: the mark stops at once. -/
theorem insertMark_of_sorted (c : Nat) (xs : List Nat) (h : RunSorted u (c :: xs)) (hc : u.ccc c ≠ 0) :
    insertMark u c xs = c :: xs := by
  cases xs with
  | nil => rfl
  | cons x rest =>
    unfold insertMark
    have hle : u.ccc x ≠ 0 → u.ccc c ≤ u.ccc x := fun hx => h.1 hc hx
    split
    · rename_i hlt
      exact absurd hlt.2 (Nat.not_lt.mpr (hle hlt.1))
    · rfl

theorem RunSorted.tail {a : Nat} {rest : List Nat} (h : RunSorted u (a :: rest)) : RunSorted u rest := by
  cases rest with
  | nil => trivial
  | cons b more => exact h.2

theorem order_of_sorted : ∀ l : List Nat, RunSorted u l → order u l = l
  | [], _ => rfl
  | x :: xs, h => by
    unfold order
    have ih := order_of_sorted xs (RunSorted.tail u h)
    split
    · rw [ih]
    · rename_i h0
      rw [ih]
      exact insertMark_of_sorted u x xs h h0

theorem order_idem (l : List Nat) : order u (order u l) = order u l :=
  order_of_sorted u _ (order_sorted u l)

/-! ## Canonical decomposition -/

/-- The full decomposition of one scalar: the data's, or the scalar itself. -/
def decompose (c : Nat) : List Nat := (u.decomp c).getD [c]

def decomposeAll (l : List Nat) : List Nat := l.flatMap (decompose u)

/-- Canonical decomposition in canonical order. -/
def nfd (l : List Nat) : List Nat := order u (decomposeAll u l)

/-- The data is closed: nothing inside a decomposition decomposes further.
    This is what "full decomposition" means (UAX #15 D68) and what the
    extractor computes by recursion. -/
def UCD.Closed : Prop :=
  ∀ c d, u.decomp c = some d → ∀ x ∈ d, u.decomp x = none

theorem decompose_of_none {c : Nat} (h : u.decomp c = none) : decompose u c = [c] := by
  simp [decompose, h]

/-- Every scalar a decomposition produces is itself undecomposable. -/
theorem decomposeAll_none (hc : UCD.Closed u) :
    ∀ l : List Nat, ∀ x ∈ decomposeAll u l, u.decomp x = none
  | [], x, hx => by simp [decomposeAll] at hx
  | c :: rest, x, hx => by
    simp only [decomposeAll, List.flatMap_cons, List.mem_append] at hx
    rcases hx with hx | hx
    · unfold decompose at hx
      cases hd : u.decomp c with
      | none =>
        rw [hd] at hx
        simp at hx
        subst hx
        exact hd
      | some d =>
        rw [hd] at hx
        exact hc c d hd x hx
    · exact decomposeAll_none hc rest x hx

theorem decomposeAll_id_of_none : ∀ l : List Nat, (∀ x ∈ l, u.decomp x = none) → decomposeAll u l = l
  | [], _ => rfl
  | c :: rest, h => by
    simp only [decomposeAll, List.flatMap_cons]
    rw [decompose_of_none u (h c (List.mem_cons_self ..))]
    simp only [List.singleton_append, List.cons.injEq, true_and]
    exact decomposeAll_id_of_none rest (fun x hx => h x (List.mem_cons_of_mem c hx))

/-- NFD is idempotent for closed data: re-decomposing changes nothing, and
    ordering is idempotent. -/
theorem nfd_idem (hc : UCD.Closed u) (l : List Nat) : nfd u (nfd u l) = nfd u l := by
  unfold nfd
  have hnone : ∀ x ∈ order u (decomposeAll u l), u.decomp x = none := fun x hx =>
    decomposeAll_none u hc l x ((order_perm u _).mem_iff.mp hx)
  rw [decomposeAll_id_of_none u _ hnone, order_idem]

/-! ## Canonical composition (defined, not yet proved about) -/

/-- One step of D117 over an ordered, decomposed text. The accumulator is the
    output so far, the index of the last starter kept in it (when there is
    one), and the class of the last character kept after that starter
    (`none` when nothing intervenes). A character is blocked from the
    starter when a kept character between them has a class that is not
    lower; an unblocked character that forms a primary composite with the
    starter replaces it. -/
def composeStep (acc : List Nat × Option Nat × Option Nat) (c : Nat) : List Nat × Option Nat × Option Nat :=
  let out := acc.1
  let starter := acc.2.1
  let last := acc.2.2
  let cc := u.ccc c
  let unblocked := match last with
    | none => true
    | some k => decide (k < cc)
  let keep : List Nat × Option Nat × Option Nat :=
    (out ++ [c], if cc = 0 then some out.length else starter, if cc = 0 then none else some cc)
  match starter with
  | some i =>
    if unblocked then
      match out[i]? with
      | some s =>
        match u.compose s c with
        | some p => (out.set i p, some i, last)
        | none => keep
      | none => keep
    else keep
  | none => keep

/-- Canonical composition of an ordered, decomposed text (D117). -/
def compose (l : List Nat) : List Nat := (l.foldl (composeStep u) ([], none, none)).1

def nfc (l : List Nat) : List Nat := compose u (nfd u l)

end Oak.Normalization
