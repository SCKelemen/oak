namespace Oak.Normalization

/-! # Unicode normalization forms (UAX #15)

Model for `stdlib/normalize.oak`. The Unicode Character Database enters as
an abstract `UCD` — a combining class for every scalar, the full canonical
decomposition of the scalars that have one, and the primary composite of a
pair — so the theorems hold for any data with the shape the standard
guarantees, and the Go law test (`compiler/e2e_stdlib_normalize_laws_test.go`)
checks the compiled Oak against the same definitions instantiated with the
Unicode 17.0.0 extract.

Three definitions are stated and proved about:

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
  the last starter that forms a primary composite with it is absorbed.
  Proved, for closed data whose primary composites undo their composition
  (`UCD.Inverse`, the property the composition table has by construction):
  decomposing a composed text is canonically equivalent to the text it came
  from (`nfd_compose`), so NFC loses nothing NFD sees (`nfd_nfc`:
  `nfd (nfc x) = nfd x`) and NFC is idempotent (`nfc_idem`). The proof is
  below, after the composer's invariant. -/

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

/-! ## Canonical composition (the definition; its laws follow below) -/

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

/-! ## Canonical composition: the laws

The composition laws rest on one property of the data beyond closure: a
primary composite undoes the composition it came from. `UCD.Inverse` states
it through the full decomposition, so it covers a starter that is itself a
composite of an earlier step (`a + ´ + ¨`): if `compose s c = some p` and `c`
is undecomposable, then `decompose p = decompose s ++ [c]`. This is the
"primary composite" half of UAX #15's definition of the composition table
(D115, D116), with exclusions already applied by whoever built `compose`.

The argument: decomposing `compose l` returns every absorbed character to
the run it came from, immediately after its starter's own decomposition,
ahead of the kept marks it was not blocked by. Those kept marks all have a
class strictly below its own (that is what "unblocked" means), so the
result differs from `l` only by adjacent swaps of two non-starters with
different classes — reorderings canonical ordering cannot distinguish
(`order_moves`), because a stable insertion of two keys that differ commutes
(`insertMark_comm`). Hence `nfd (compose l) = order l` for every ordered,
undecomposable `l` (`nfd_compose`), and `nfd (nfc x) = nfd x` and
`nfc (nfc x) = nfc x` follow. -/

/-- A primary composite undoes its composition (through full decomposition). -/
def UCD.Inverse : Prop :=
  ∀ s c p, u.compose s c = some p → u.decomp c = none → decompose u p = decompose u s ++ [c]

/-- The reorderings canonical ordering cannot tell apart: adjacent swaps of two
    non-starters whose classes differ, and their compositions. -/
inductive Moves : List Nat → List Nat → Prop
  | refl (l : List Nat) : Moves l l
  | swap (xs ys : List Nat) (a b : Nat) (ha : u.ccc a ≠ 0) (hb : u.ccc b ≠ 0) (hab : u.ccc a ≠ u.ccc b) :
      Moves (xs ++ a :: b :: ys) (xs ++ b :: a :: ys)
  | trans {l m n : List Nat} : Moves l m → Moves m n → Moves l n

theorem Moves.append_left {l l' : List Nat} (m : List Nat) (h : Moves u l l') : Moves u (m ++ l) (m ++ l') := by
  induction h with
  | refl l => exact Moves.refl _
  | swap xs ys a b ha hb hab =>
    rw [← List.append_assoc, ← List.append_assoc]
    exact Moves.swap (m ++ xs) ys a b ha hb hab
  | trans _ _ ih1 ih2 => exact Moves.trans ih1 ih2

theorem Moves.append_right {l l' : List Nat} (m : List Nat) (h : Moves u l l') : Moves u (l ++ m) (l' ++ m) := by
  induction h with
  | refl l => exact Moves.refl _
  | swap xs ys a b ha hb hab =>
    simp only [List.append_assoc, List.cons_append]
    exact Moves.swap xs (ys ++ m) a b ha hb hab
  | trans _ _ ih1 ih2 => exact Moves.trans ih1 ih2

/-- A mark moves to the front of a run of marks whose classes all differ from its own. -/
theorem Moves.move_left (c : Nat) (hc : u.ccc c ≠ 0) :
    ∀ K : List Nat, (∀ k ∈ K, u.ccc k ≠ 0 ∧ u.ccc k ≠ u.ccc c) → Moves u (K ++ [c]) (c :: K)
  | [], _ => Moves.refl _
  | k :: K, h => by
    have hk := h k List.mem_cons_self
    have ih := Moves.move_left c hc K (fun x hx => h x (List.mem_cons_of_mem k hx))
    have step1 : Moves u ([k] ++ (K ++ [c])) ([k] ++ c :: K) := Moves.append_left u [k] ih
    have step2 : Moves u ([] ++ k :: c :: K) ([] ++ c :: k :: K) := Moves.swap [] K k c hk.1 hc hk.2
    simp only [List.singleton_append, List.nil_append] at step1 step2
    exact Moves.trans (by simpa using step1) step2

/-! ### Canonical ordering is blind to `Moves` -/

/-- One character placed onto an ordered tail. -/
def step (x : Nat) (acc : List Nat) : List Nat := if u.ccc x = 0 then x :: acc else insertMark u x acc

theorem order_cons (x : Nat) (xs : List Nat) : order u (x :: xs) = step u x (order u xs) := by
  simp only [order, step]

theorem order_append (xs ys : List Nat) : order u (xs ++ ys) = xs.foldr (step u) (order u ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [List.cons_append, order_cons, ih]; rfl

/-- A stable insertion of two keys that differ commutes, whatever the list. -/
theorem insertMark_comm (a b : Nat) (ha : u.ccc a ≠ 0) (hb : u.ccc b ≠ 0) (hab : u.ccc a ≠ u.ccc b) :
    ∀ L : List Nat, insertMark u a (insertMark u b L) = insertMark u b (insertMark u a L)
  | [] => by
    simp only [insertMark]
    by_cases h1 : u.ccc b < u.ccc a
    · rw [if_pos ⟨hb, h1⟩, if_neg (fun h => by omega)]
    · rw [if_neg (fun h => h1 h.2), if_pos ⟨ha, by omega⟩]
  | x :: xs => by
    have ih := insertMark_comm a b ha hb hab xs
    by_cases hxa : u.ccc x ≠ 0 ∧ u.ccc x < u.ccc a <;> by_cases hxb : u.ccc x ≠ 0 ∧ u.ccc x < u.ccc b
    · -- x passes both marks
      have e1 : insertMark u b (x :: xs) = x :: insertMark u b xs := by simp [insertMark, hxb]
      have e2 : insertMark u a (x :: xs) = x :: insertMark u a xs := by simp [insertMark, hxa]
      rw [e1, e2]
      simp only [insertMark, if_pos hxa, if_pos hxb, ih]
    · -- x passes a but not b: b ≤ x < a, so b stops before x and a passes both
      have hlt : u.ccc b < u.ccc a := by omega
      have e1 : insertMark u b (x :: xs) = b :: x :: xs := by simp [insertMark, hxb]
      have e2 : insertMark u a (x :: xs) = x :: insertMark u a xs := by simp [insertMark, hxa]
      rw [e1, e2]
      simp only [insertMark, if_pos hxa, if_pos (show u.ccc b ≠ 0 ∧ u.ccc b < u.ccc a from ⟨hb, hlt⟩),
        if_neg (show ¬ (u.ccc x ≠ 0 ∧ u.ccc x < u.ccc b) from hxb)]
    · -- x passes b but not a: a ≤ x < b
      have hlt : u.ccc a < u.ccc b := by omega
      have e1 : insertMark u b (x :: xs) = x :: insertMark u b xs := by simp [insertMark, hxb]
      have e2 : insertMark u a (x :: xs) = a :: x :: xs := by simp [insertMark, hxa]
      rw [e1, e2]
      simp only [insertMark, if_pos hxb, if_pos (show u.ccc a ≠ 0 ∧ u.ccc a < u.ccc b from ⟨ha, hlt⟩),
        if_neg (show ¬ (u.ccc x ≠ 0 ∧ u.ccc x < u.ccc a) from hxa)]
    · -- x stops both marks; they land in class order in front of it
      have e1 : insertMark u b (x :: xs) = b :: x :: xs := by simp [insertMark, hxb]
      have e2 : insertMark u a (x :: xs) = a :: x :: xs := by simp [insertMark, hxa]
      rw [e1, e2]
      by_cases hlt : u.ccc b < u.ccc a
      · simp only [insertMark, if_pos (show u.ccc b ≠ 0 ∧ u.ccc b < u.ccc a from ⟨hb, hlt⟩),
          if_neg (show ¬ (u.ccc a ≠ 0 ∧ u.ccc a < u.ccc b) from fun h => by omega),
          if_neg (show ¬ (u.ccc x ≠ 0 ∧ u.ccc x < u.ccc a) from hxa)]
      · have hlt' : u.ccc a < u.ccc b := by omega
        simp only [insertMark, if_neg (show ¬ (u.ccc b ≠ 0 ∧ u.ccc b < u.ccc a) from fun h => hlt h.2),
          if_pos (show u.ccc a ≠ 0 ∧ u.ccc a < u.ccc b from ⟨ha, hlt'⟩),
          if_neg (show ¬ (u.ccc x ≠ 0 ∧ u.ccc x < u.ccc b) from hxb)]

theorem order_swap (xs ys : List Nat) (a b : Nat) (ha : u.ccc a ≠ 0) (hb : u.ccc b ≠ 0)
    (hab : u.ccc a ≠ u.ccc b) : order u (xs ++ a :: b :: ys) = order u (xs ++ b :: a :: ys) := by
  rw [order_append, order_append, order_cons, order_cons, order_cons, order_cons]
  simp only [step, if_neg ha, if_neg hb]
  rw [insertMark_comm u a b ha hb hab]

theorem order_moves {l l' : List Nat} (h : Moves u l l') : order u l = order u l' := by
  induction h with
  | refl l => rfl
  | swap xs ys a b ha hb hab => exact order_swap u xs ys a b ha hb hab
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ### Decomposition distributes over the composer's edits -/

theorem decomposeAll_append (l m : List Nat) :
    decomposeAll u (l ++ m) = decomposeAll u l ++ decomposeAll u m := by
  simp [decomposeAll, List.flatMap_append]

theorem decomposeAll_cons (c : Nat) (l : List Nat) :
    decomposeAll u (c :: l) = decompose u c ++ decomposeAll u l := by
  simp [decomposeAll]

/-- `out` around its `i`-th element, decomposed. -/
theorem decomposeAll_split (out : List Nat) (i : Nat) (h : i < out.length) :
    decomposeAll u out = decomposeAll u (out.take i) ++ decompose u out[i] ++ decomposeAll u (out.drop (i + 1)) := by
  have h1 : out.take i ++ out[i] :: out.drop (i + 1) = out := by
    rw [List.getElem_cons_drop h, List.take_append_drop]
  rw [List.append_assoc, ← decomposeAll_cons, ← decomposeAll_append, h1]

theorem decomposeAll_set (out : List Nat) (i : Nat) (p : Nat) (h : i < out.length) :
    decomposeAll u (out.set i p) = decomposeAll u (out.take i) ++ decompose u p ++ decomposeAll u (out.drop (i + 1)) := by
  rw [List.set_eq_take_append_cons_drop, if_pos h, decomposeAll_append, decomposeAll_cons, List.append_assoc]

/-! ### The composer's invariant -/

/-- What holds of the composition state after the prefix `done`: decomposing
    the output moves back to `done`, and — when a starter has been kept at
    index `i` — everything after it is an undecomposable non-starter whose
    class is bounded by the recorded class of the last kept character, and
    nothing follows it at all when no class is recorded. -/
def ComposeInv (done : List Nat) (st : List Nat × Option Nat × Option Nat) : Prop :=
  Moves u done (decomposeAll u st.1) ∧
  ∀ i, st.2.1 = some i →
    i < st.1.length ∧
    (∀ j x, i < j → st.1[j]? = some x →
      u.ccc x ≠ 0 ∧ u.decomp x = none ∧ ∀ m, st.2.2 = some m → u.ccc x ≤ m) ∧
    (st.2.2 = none → st.1.length = i + 1)

/-- The state a kept character produces. -/
theorem keep_inv (done out : List Nat) (si last : Option Nat) (c : Nat)
    (hinv : ComposeInv u done (out, si, last)) (hc : u.decomp c = none)
    (hlast : ∀ m, last = some m → u.ccc c ≠ 0 → m ≤ u.ccc c) :
    ComposeInv u (done ++ [c])
      (out ++ [c], if u.ccc c = 0 then some out.length else si, if u.ccc c = 0 then none else some (u.ccc c)) := by
  simp only [ComposeInv] at hinv ⊢
  obtain ⟨hmoves, hidx⟩ := hinv
  refine ⟨?_, ?_⟩
  · rw [decomposeAll_append, decomposeAll_cons, decompose_of_none u hc]
    simpa [decomposeAll] using Moves.append_right u [c] hmoves
  · intro i hi
    by_cases h0 : u.ccc c = 0
    · rw [if_pos h0] at hi
      cases hi
      refine ⟨by simp, ?_, fun _ => by simp⟩
      intro j x hj hx
      have : (out ++ [c])[j]? = none := by
        rw [List.getElem?_eq_none_iff]; simp; omega
      rw [this] at hx; cases hx
    · rw [if_neg h0] at hi
      rw [if_neg h0]
      obtain ⟨hlen, hafter, hnone⟩ := hidx i hi
      refine ⟨by simp; omega, ?_, fun h => by cases h⟩
      intro j x hj hx
      by_cases hjl : j < out.length
      · rw [List.getElem?_append_left hjl] at hx
        obtain ⟨hcx, hdx, hbx⟩ := hafter j x hj hx
        refine ⟨hcx, hdx, fun m hm => ?_⟩
        cases hm
        cases hl : last with
        | none => have := hnone hl; omega
        | some m => exact Nat.le_trans (hbx m hl) (hlast m hl h0)
      · rw [List.getElem?_append_right (by omega)] at hx
        have hj' : j - out.length = 0 := by
          have : j - out.length < [c].length := (List.getElem?_eq_some_iff.mp hx).1
          simp at this; omega
        rw [hj'] at hx
        simp at hx
        subst hx
        exact ⟨h0, hc, fun m hm => by cases hm; exact Nat.le_refl _⟩

/-- Every character after the kept starter, as a list: the kept marks. -/
theorem drop_facts (out : List Nat) (i : Nat) (P : Nat → Prop)
    (h : ∀ j x, i < j → out[j]? = some x → P x) : ∀ x ∈ out.drop (i + 1), P x := by
  intro x hx
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hx
  rw [List.getElem?_drop] at hj
  exact h (i + 1 + j) x (by omega) hj

/-- The blocking test of D115 as a proposition on the recorded class: nothing
    kept since the starter, or the last kept class below the candidate's. -/
def Unblocked (last : Option Nat) (cc : Nat) : Prop :=
  match last with
  | none => True
  | some k => k < cc

/-- The state an absorbed character produces. -/
theorem absorb_inv (hinv : UCD.Inverse u) (done out : List Nat) (i : Nat) (last : Option Nat) (c s p : Nat)
    (hcomp : ComposeInv u done (out, some i, last)) (hc : u.decomp c = none)
    (hs : out[i]? = some s) (hp : u.compose s c = some p)
    (hunblocked : Unblocked last (u.ccc c)) :
    ComposeInv u (done ++ [c]) (out.set i p, some i, last) := by
  simp only [ComposeInv] at hcomp ⊢
  obtain ⟨hmoves, hidx⟩ := hcomp
  obtain ⟨hlen, hafter, hnone⟩ := hidx i rfl
  have hsi : out[i] = s := (List.getElem?_eq_some_iff.mp hs).2
  refine ⟨?_, ?_⟩
  · -- decomposing the edited output: the absorbed mark returns behind its starter
    rw [decomposeAll_set u out i p hlen, hinv s c p hp hc]
    have hK : decomposeAll u (out.drop (i + 1)) = out.drop (i + 1) :=
      decomposeAll_id_of_none u _ (drop_facts out i (fun x => u.decomp x = none)
        (fun j x hj hx => (hafter j x hj hx).2.1))
    rw [hK]
    have hsplit := decomposeAll_split u out i hlen
    rw [hsi, hK] at hsplit
    rw [hsplit] at hmoves
    have h1 : Moves u (done ++ [c])
        (decomposeAll u (out.take i) ++ decompose u s ++ out.drop (i + 1) ++ [c]) :=
      Moves.append_right u [c] hmoves
    have h2 : Moves u (out.drop (i + 1) ++ [c]) (c :: out.drop (i + 1)) := by
      cases last with
      | none =>
        have hlen1 : out.length = i + 1 := hnone rfl
        have : out.drop (i + 1) = [] := by
          rw [List.drop_eq_nil_iff]; omega
        rw [this]; exact Moves.refl _
      | some k =>
        have hk : k < u.ccc c := hunblocked
        apply Moves.move_left u c (by omega)
        intro x hx
        obtain ⟨hcx, -, hbx⟩ := drop_facts out i
          (fun x => u.ccc x ≠ 0 ∧ u.decomp x = none ∧ ∀ m, some k = some m → u.ccc x ≤ m) hafter x hx
        have := hbx k rfl
        exact ⟨hcx, by omega⟩
    have h3 := Moves.append_left u (decomposeAll u (out.take i) ++ decompose u s) h2
    simp only [List.append_assoc] at h1 h3 ⊢
    exact Moves.trans h1 h3
  · intro i' hi'
    cases hi'
    refine ⟨by simpa using hlen, ?_, fun h => by simpa using hnone h⟩
    intro j x hj hx
    rw [List.getElem?_set_ne (by omega)] at hx
    exact hafter j x hj hx

/-- One step of the composer preserves the invariant, and the recorded class
    it leaves behind is the new mark's or the old record with the mark above it. -/
theorem composeStep_inv (hinv : UCD.Inverse u) (done : List Nat) (st : List Nat × Option Nat × Option Nat) (c : Nat)
    (hcomp : ComposeInv u done st) (hc : u.decomp c = none)
    (hlast : ∀ m, st.2.2 = some m → u.ccc c ≠ 0 → m ≤ u.ccc c) :
    ComposeInv u (done ++ [c]) (composeStep u st c) ∧
    ∀ m, (composeStep u st c).2.2 = some m →
      (m = u.ccc c ∧ u.ccc c ≠ 0) ∨ (st.2.2 = some m ∧ u.ccc c ≠ 0) := by
  obtain ⟨out, si, last⟩ := st
  have hkeep := keep_inv u done out si last c hcomp hc hlast
  have hkeep_last : ∀ m, (if u.ccc c = 0 then none else some (u.ccc c)) = some m →
      (m = u.ccc c ∧ u.ccc c ≠ 0) ∨ (last = some m ∧ u.ccc c ≠ 0) := by
    intro m hm
    by_cases h0 : u.ccc c = 0
    · rw [if_pos h0] at hm; cases hm
    · rw [if_neg h0] at hm; cases hm; exact Or.inl ⟨rfl, h0⟩
  cases si with
  | none =>
    simp only [composeStep]
    exact ⟨hkeep, hkeep_last⟩
  | some i =>
    cases last with
    | none =>
      simp only [composeStep, ite_true]
      split
      · rename_i s hs
        split
        · rename_i p hp
          refine ⟨absorb_inv u hinv done out i none c s p hcomp hc hs hp trivial, ?_⟩
          intro m hm
          cases hm
        · exact ⟨hkeep, hkeep_last⟩
      · exact ⟨hkeep, hkeep_last⟩
    | some k =>
      simp only [composeStep, decide_eq_true_eq]
      by_cases hk : k < u.ccc c
      · rw [if_pos hk]
        split
        · rename_i s hs
          split
          · rename_i p hp
            refine ⟨absorb_inv u hinv done out i (some k) c s p hcomp hc hs hp hk, ?_⟩
            intro m hm
            cases hm
            exact Or.inr ⟨rfl, by omega⟩
          · exact ⟨hkeep, hkeep_last⟩
        · exact ⟨hkeep, hkeep_last⟩
      · rw [if_neg hk]
        exact ⟨hkeep, hkeep_last⟩

/-- The invariant carried across the whole fold. -/
theorem compose_inv (hinv : UCD.Inverse u) :
    ∀ (rest done : List Nat) (st : List Nat × Option Nat × Option Nat),
      ComposeInv u done st → RunSorted u rest → (∀ x ∈ rest, u.decomp x = none) →
      (∀ m, st.2.2 = some m → ∀ c, rest.head? = some c → u.ccc c ≠ 0 → m ≤ u.ccc c) →
      ComposeInv u (done ++ rest) (rest.foldl (composeStep u) st)
  | [], done, st, h, _, _, _ => by simpa using h
  | c :: rest, done, st, h, hs, hn, hlast => by
    rw [List.foldl_cons]
    have hc : u.decomp c = none := hn c List.mem_cons_self
    obtain ⟨hstep, hstep_last⟩ := composeStep_inv u hinv done st c h hc
      (fun m hm h0 => hlast m hm c rfl h0)
    have ih := compose_inv hinv rest (done ++ [c]) (composeStep u st c) hstep (RunSorted.tail u hs)
      (fun x hx => hn x (List.mem_cons_of_mem c hx)) ?_
    · simpa [List.append_assoc] using ih
    · intro m hm c' hc' hc'0
      rcases hstep_last m hm with ⟨rfl, hc0⟩ | ⟨hm', hc0⟩
      · -- the new mark sits right before c' in the sorted run
        cases rest with
        | nil => cases hc'
        | cons d rest' =>
          simp at hc'; subst hc'
          exact hs.1 hc0 hc'0
      · have h1 := hlast m hm' c rfl hc0
        cases rest with
        | nil => cases hc'
        | cons d rest' =>
          simp at hc'; subst hc'
          exact Nat.le_trans h1 (hs.1 hc0 hc'0)

/-- Decomposing the composition of an ordered, undecomposable text moves back
    to the text itself. -/
theorem compose_moves (hinv : UCD.Inverse u) (l : List Nat) (hs : RunSorted u l)
    (hn : ∀ x ∈ l, u.decomp x = none) : Moves u l (decomposeAll u (compose u l)) := by
  have h := compose_inv u hinv l [] ([], none, none)
    ⟨Moves.refl [], fun i hi => by cases hi⟩ hs hn (fun m hm => by cases hm)
  simpa [compose, decomposeAll] using h.1

theorem nfd_compose (hinv : UCD.Inverse u) (l : List Nat) (hs : RunSorted u l)
    (hn : ∀ x ∈ l, u.decomp x = none) : nfd u (compose u l) = order u l := by
  unfold nfd
  exact (order_moves u (compose_moves u hinv l hs hn)).symm

/-- `nfc` is composition applied to `nfd`, by definition. -/
theorem nfc_of_nfd (l : List Nat) : nfc u l = compose u (nfd u l) := rfl

/-- Decomposing a composed text gives the decomposition of the original:
    NFC loses nothing NFD sees. -/
theorem nfd_nfc (hcl : UCD.Closed u) (hinv : UCD.Inverse u) (l : List Nat) : nfd u (nfc u l) = nfd u l := by
  rw [nfc_of_nfd, nfd_compose u hinv (nfd u l) (order_sorted u _)
    (fun y hy => decomposeAll_none u hcl l y ((order_perm u _).mem_iff.mp hy))]
  exact order_idem u _

/-- NFC is idempotent. -/
theorem nfc_idem (hcl : UCD.Closed u) (hinv : UCD.Inverse u) (l : List Nat) : nfc u (nfc u l) = nfc u l := by
  rw [nfc_of_nfd u (nfc u l), nfd_nfc u hcl hinv]
  rfl

end Oak.Normalization
