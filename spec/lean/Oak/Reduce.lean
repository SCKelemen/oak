/-!
# Oak.Reduce — reductions whose grouping is a language fact

Model of `stdlib/reduce.oak` (docs/spec/55-parallelism.md section 4, the
fourth option): `tree f z xs` combines a list with a binary operation in the
**balanced binary-counter tree**, and `left f z xs` is the sequential left
fold. The tree is defined exactly as the Oak implementation computes it — a
stack of partial results with levels; a new element enters at level 0 and
combines with its neighbour whenever the two topmost partials share a
level; the leftovers combine right to left — so the theorems here are about
the grouping every backend produces, not about an idealized one.

* `tree_four`: four elements give `f (f x0 x1) (f x2 x3)`, the grouping of
  `simd.reduce_add`; `tree_eight` is the perfect tree.
* `tree_nil`, `tree_singleton`: the zero appears only for the empty input.
* `tree_assoc`: under associativity the tree equals the left fold started at
  the first element — the law that makes `laws { associative }`
  (`10-syntax.md` section 14a) the permission to regroup. Without it, the
  grouping named is the grouping computed.
* `chainFold`, `tree_eq_chainFold`: the left fold from the first element
  (`reduce.chain`), and the theorem that licenses lowering a
  `reduce.reduce` under `order bounded` over a function declaring
  `laws { associative }` to it.
* `resolve`, `resolve_default_exact`, `resolve_bounded_needs_claim`,
  `resolve_regroups_only_bounded`, `bounded_sound`: the checker's rule for
  "declaring the order once" (`55-parallelism.md` section 4) — the exact
  tree by default, a named order by name, and the regrouping only under
  `bounded` with the claim, where it is the tree's value.
* `fold`, `tree_map`, `fold_eq_tree_map`: the stateful orders — the
  sequential fold with a state and the tree over lifted elements — and
  the theorem that an associative merge makes them one value.
* `tree_append_pow2`, `coop_eq_tree`, `coop_full`: the cooperative
  threadgroup scheme of `reduce.group_tree` (`56-kernels.md` section 7) —
  pairwise-adjacent combination with doubling stride, partner present —
  computes this same tree for every window length.
-/

namespace Oak.Reduce

variable {α : Type}

/-- One stack entry: a partial result and its level. The stack's head is the
most recent entry. -/
structure Partial (α : Type) where
  value : α
  level : Nat

/-- Combine equal-level neighbours at the top of the stack. -/
def collapse (f : α → α → α) : List (Partial α) → List (Partial α)
  | top :: next :: rest =>
    if top.level = next.level then
      collapse f ({ value := f next.value top.value, level := next.level + 1 } :: rest)
    else top :: next :: rest
  | s => s
termination_by s => s.length

/-- Push one element and collapse. -/
def push (f : α → α → α) (s : List (Partial α)) (x : α) : List (Partial α) :=
  collapse f ({ value := x, level := 0 } :: s)

/-- Combine the leftover stack right to left: the head (latest) is the right
operand of its neighbour, and so on down. -/
def finish (f : α → α → α) : List (Partial α) → Option α
  | [] => none
  | [p] => some p.value
  | top :: next :: rest => finish f ({ value := f next.value top.value, level := next.level } :: rest)
termination_by s => s.length

/-- The balanced binary-counter tree reduction (`reduce.tree`). -/
def tree (f : α → α → α) (z : α) (xs : List α) : α :=
  match finish f (xs.foldl (push f) []) with
  | some v => v
  | none => z

/-- The sequential left fold (`reduce.left`). -/
def left (f : α → α → α) (z : α) (xs : List α) : α := xs.foldl f z

theorem tree_nil (f : α → α → α) (z : α) : tree f z [] = z := by
  simp [tree, finish]

theorem tree_singleton (f : α → α → α) (z x : α) : tree f z [x] = x := by
  simp [tree, push, collapse, finish]

/-- Two elements combine in order. -/
theorem tree_two (f : α → α → α) (z a b : α) : tree f z [a, b] = f a b := by
  simp [tree, push, collapse, finish]

/-- Three elements: the first pair, then the third on the right. -/
theorem tree_three (f : α → α → α) (z a b c : α) : tree f z [a, b, c] = f (f a b) c := by
  simp [tree, push, collapse, finish]

/-- **The `reduce_add` grouping**: four elements give `(x0 ∘ x1) ∘ (x2 ∘ x3)`. -/
theorem tree_four (f : α → α → α) (z a b c d : α) :
    tree f z [a, b, c, d] = f (f a b) (f c d) := by
  simp [tree, push, collapse, finish]

/-- Five elements: the perfect four, then the fifth on the right. -/
theorem tree_five (f : α → α → α) (z a b c d e : α) :
    tree f z [a, b, c, d, e] = f (f (f a b) (f c d)) e := by
  simp [tree, push, collapse, finish]

/-- Eight elements form the perfect tree. -/
theorem tree_eight (f : α → α → α) (z a b c d e g h i : α) :
    tree f z [a, b, c, d, e, g, h, i] = f (f (f a b) (f c d)) (f (f e g) (f h i)) := by
  simp [tree, push, collapse, finish]

/-- Associativity of `f`. -/
def Assoc (f : α → α → α) : Prop := ∀ a b c, f (f a b) c = f a (f b c)

/-- The left fold of a non-empty list from its first element. -/
def chain (f : α → α → α) : List α → Option α
  | [] => none
  | y :: ys => some (ys.foldl f y)

/-- What a stack denotes: its entries oldest first, chained. -/
def denote (f : α → α → α) (s : List (Partial α)) : Option α :=
  chain f (s.reverse.map Partial.value)

theorem chain_append_pair (f : α → α → α) (hf : Assoc f) (l : List α) (a b : α) :
    chain f (l ++ [a, b]) = chain f (l ++ [f a b]) := by
  cases l with
  | nil => simp [chain]
  | cons y ys =>
    simp only [List.cons_append, chain, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hf]

/-- Merging the two newest entries does not change what the stack denotes. -/
theorem denote_merge (f : α → α → α) (hf : Assoc f) (top next : Partial α) (rest : List (Partial α)) (lvl : Nat) :
    denote f ({ value := f next.value top.value, level := lvl } :: rest) = denote f (top :: next :: rest) := by
  unfold denote
  simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.append_assoc,
    List.singleton_append]
  rw [chain_append_pair f hf]

/-- Collapsing preserves the denotation. -/
theorem denote_collapse (f : α → α → α) (hf : Assoc f) (s : List (Partial α)) :
    denote f (collapse f s) = denote f s := by
  induction s using collapse.induct f with
  | case1 top next rest heq ih =>
    rw [collapse, if_pos heq, ih, denote_merge f hf]
  | case2 top next rest hne =>
    rw [collapse, if_neg hne]
  | case3 s h =>
    unfold collapse
    split
    · exact absurd rfl (h _ _ _)
    · rfl

/-- Finishing computes the denotation. -/
theorem finish_eq_denote (f : α → α → α) (hf : Assoc f) (s : List (Partial α)) :
    finish f s = denote f s := by
  induction s using finish.induct f with
  | case1 => simp [finish, denote, chain]
  | case2 p => simp [finish, denote, chain]
  | case3 top next rest ih =>
    rw [finish, ih, denote_merge f hf]

/-- Extending a chain by further elements: fold them onto the value, or
start the chain when there was none. -/
def extend (f : α → α → α) (d : Option α) (xs : List α) : Option α :=
  match d with
  | none => chain f xs
  | some v => some (xs.foldl f v)

theorem extend_nil (f : α → α → α) (d : Option α) : extend f d [] = d := by
  cases d <;> simp [extend, chain]

theorem extend_cons (f : α → α → α) (d : Option α) (x : α) (xs : List α) :
    extend f d (x :: xs) = extend f (extend f d [x]) xs := by
  cases d <;> simp [extend, chain]

theorem chain_append_one (f : α → α → α) (l : List α) (x : α) :
    chain f (l ++ [x]) = extend f (chain f l) [x] := by
  cases l <;> simp [chain, extend]

/-- Pushing an element extends the denoted chain by that element. -/
theorem denote_push (f : α → α → α) (hf : Assoc f) (s : List (Partial α)) (x : α) :
    denote f (push f s x) = extend f (denote f s) [x] := by
  unfold push
  rw [denote_collapse f hf]
  unfold denote
  simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
  exact chain_append_one f _ x

/-- After pushing a list in order, the stack denotes the old chain extended
by the list. -/
theorem denote_foldl_push (f : α → α → α) (hf : Assoc f) (s : List (Partial α)) (xs : List α) :
    denote f (xs.foldl (push f) s) = extend f (denote f s) xs := by
  induction xs generalizing s with
  | nil => simp [extend_nil]
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [ih, denote_push f hf]
    exact (extend_cons f (denote f s) x xs).symm

/-- **Regrouping permission.** Under associativity the tree reduction of a
non-empty list is its left fold from the first element, so any grouping a
backend prefers computes the same value. -/
theorem tree_assoc (f : α → α → α) (hf : Assoc f) (z x : α) (xs : List α) :
    tree f z (x :: xs) = xs.foldl f x := by
  unfold tree
  rw [finish_eq_denote f hf, denote_foldl_push f hf]
  simp [denote, chain, extend]

/-! ## The grouping an associative law licenses

`reduce.chain` is the left fold from the first element, `zero` only for
the empty list: what `tree` computes under associativity (`tree_assoc`),
without the stack of partials. A call of `tree` whose combine declares
`laws { associative }` (docs/spec/10-syntax.md section 14a) is lowered to
`chain` where a block asks (`order bounded`, below); `tree_eq_chainFold` is
the theorem the lowering rests on, and the law is its hypothesis — a false
law makes the two differ, which is what the chapter says a false law
does. -/

/-- The left fold from the first element (`reduce.chain`; `chain` above is
the proof-internal chain of partials). -/
def chainFold (f : α → α → α) (z : α) : List α → α
  | [] => z
  | x :: xs => xs.foldl f x

theorem chainFold_nil (f : α → α → α) (z : α) : chainFold f z [] = z := rfl

theorem chainFold_cons (f : α → α → α) (z x : α) (xs : List α) : chainFold f z (x :: xs) = xs.foldl f x := rfl

/-- Under associativity the tree is the chain fold, on every input. -/
theorem tree_eq_chainFold (f : α → α → α) (hf : Assoc f) (z : α) (xs : List α) :
    tree f z xs = chainFold f z xs := by
  cases xs with
  | nil => exact tree_nil f z
  | cons x xs => rw [tree_assoc f hf, chainFold_cons]

/-! ## Stateful orders: an order is a function

`reduce.fold xs init step` is the sequential order with a state of its own
type, and `reduce.tree_map xs zero lift merge` the binary-counter order
over the lifted elements (docs/spec/55-parallelism.md section 4). Each is
a function a program names; `fold_eq_tree_map` is the theorem that for an
associative merge the two are one value — the online-softmax merge of a
fused attention written once as the step of a fold and once as the merge
of a tree is the same number both ways. -/

/-- The sequential left fold with a state. -/
def fold {β : Type} (step : α → β → α) (init : α) (xs : List β) : α := xs.foldl step init

/-- The binary-counter tree over the lifted elements. -/
def tree_map {β : Type} (lift : β → α) (merge : α → α → α) (z : α) (xs : List β) : α :=
  tree merge z (xs.map lift)

theorem fold_eq_left (f : α → α → α) (z : α) (xs : List α) : fold f z xs = left f z xs := rfl

theorem tree_map_nil {β : Type} (lift : β → α) (merge : α → α → α) (z : α) :
    tree_map lift merge z [] = z := by
  simp [tree_map, tree_nil]

theorem tree_map_id (f : α → α → α) (z : α) (xs : List α) : tree_map id f z xs = tree f z xs := by
  simp [tree_map]

/-- For an associative merge the fold whose step merges the lifted element
equals the tree over the lifted elements, on non-empty input. -/
theorem fold_eq_tree_map {β : Type} (lift : β → α) (merge : α → α → α) (hm : Assoc merge)
    (z : α) (x : β) (xs : List β) :
    fold (fun s y => merge s (lift y)) (lift x) xs = tree_map lift merge z (x :: xs) := by
  unfold fold tree_map
  rw [List.map_cons, tree_assoc merge hm, List.foldl_map]

/-! ## The cooperative scheme computes the same tree

`reduce.group_tree` in a kernel (docs/spec/56-kernels.md section 7) is
computed by a threadgroup: the window's `m` elements sit at positions
`0 .. m-1`; at stride `S = 1, 2, 4, …` every position `i` that is a
multiple of `2S` with a partner `i + S < m` combines with it. The
invariant of that loop — after the strides below `S`, position `i`
(a multiple of `S`) holds the tree of the block of at most `S` elements
starting at `i` — is `coop` below, taken as the definition of the scheme
on blocks; `coop_eq_tree` proves the invariant against the binary-counter
`tree`, and `coop_full` that the value at position 0 after the last stride
is `tree` of the whole window. The essential fact is `tree_append_pow2`:
splitting a list after a power-of-two prefix at least as long as the rest
splits the tree. -/

theorem collapse_ne (f : α → α → α) (top next : Partial α) (rest : List (Partial α))
    (h : top.level ≠ next.level) : collapse f (top :: next :: rest) = top :: next :: rest := by
  rw [collapse, if_neg h]

theorem collapse_eq (f : α → α → α) (top next : Partial α) (rest : List (Partial α))
    (h : top.level = next.level) :
    collapse f (top :: next :: rest) = collapse f ({ value := f next.value top.value, level := next.level + 1 } :: rest) := by
  rw [collapse, if_pos h]

theorem collapse_single (f : α → α → α) (p : Partial α) : collapse f [p] = [p] := by
  unfold collapse; rfl

/-- No collapse when the new top sits below every level of the stack. -/
theorem collapse_below (f : α → α → α) (p : Partial α) (S : List (Partial α))
    (h : ∀ q ∈ S, p.level < q.level) : collapse f (p :: S) = p :: S := by
  cases S with
  | nil => exact collapse_single f p
  | cons q rest => exact collapse_ne f p q rest (Nat.ne_of_lt (h q (by simp)))

theorem collapse_ne_nil (f : α → α → α) (s : List (Partial α)) (h : s ≠ []) : collapse f s ≠ [] := by
  induction s using collapse.induct f with
  | case1 top next rest heq ih => rw [collapse, if_pos heq]; exact ih (List.cons_ne_nil _ _)
  | case2 top next rest hne => rw [collapse, if_neg hne]; exact List.cons_ne_nil _ _
  | case3 s hs =>
    unfold collapse
    split
    · exact absurd rfl (hs _ _ _)
    · exact h

theorem push_ne_nil (f : α → α → α) (S : List (Partial α)) (x : α) : push f S x ≠ [] :=
  collapse_ne_nil f _ (List.cons_ne_nil _ _)

theorem foldl_push_ne_nil (f : α → α → α) (xs : List α) (S : List (Partial α)) (hne : xs ≠ [] ∨ S ≠ []) :
    xs.foldl (push f) S ≠ [] := by
  induction xs generalizing S with
  | nil => simpa using hne
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact ih (push f S x) (Or.inr (push_ne_nil f S x))

/-- `finish` of a nonempty stack is some value. -/
theorem finish_some (f : α → α → α) (s : List (Partial α)) (h : s ≠ []) : ∃ v, finish f s = some v := by
  induction s using finish.induct f with
  | case1 => exact absurd rfl h
  | case2 p => exact ⟨p.value, by simp [finish]⟩
  | case3 top next rest ih => rw [finish]; exact ih (List.cons_ne_nil _ _)

/-- The bottom of the stack is the left operand of everything above it. -/
theorem finish_append_last (f : α → α → α) (q : Partial α) :
    ∀ (P : List (Partial α)) (v : α), finish f P = some v → finish f (P ++ [q]) = some (f q.value v) := by
  intro P
  induction P using finish.induct f with
  | case1 => intro v h; simp [finish] at h
  | case2 p =>
    intro v h
    simp [finish] at h
    subst h
    simp [finish]
  | case3 top next rest ih =>
    intro v h
    rw [finish] at h
    simp only [List.cons_append]
    rw [finish]
    exact ih v h

/-- `tree` of a nonempty list is the value `finish` computes. -/
theorem tree_eq_of_finish (f : α → α → α) (z : α) (xs : List α) (v : α)
    (h : finish f (xs.foldl (push f) []) = some v) : tree f z xs = v := by
  unfold tree; rw [h]

theorem tree_nonempty (f : α → α → α) (z : α) (xs : List α) (h : xs ≠ []) :
    finish f (xs.foldl (push f) []) = some (tree f z xs) := by
  obtain ⟨v, hv⟩ := finish_some f _ (foldl_push_ne_nil f xs [] (Or.inl h))
  rw [hv, tree_eq_of_finish f z xs v hv]

theorem two_pow_succ_split (k : Nat) : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
  rw [Nat.pow_succ, Nat.mul_two]

/-- A list of length 2^(k+1) is two halves of length 2^k. -/
theorem split_halves (a : List α) (k : Nat) (ha : a.length = 2 ^ (k + 1)) :
    ∃ a1 a2 : List α, a = a1 ++ a2 ∧ a1.length = 2 ^ k ∧ a2.length = 2 ^ k := by
  refine ⟨a.take (2 ^ k), a.drop (2 ^ k), (List.take_append_drop _ _).symm, ?_, ?_⟩
  · rw [List.length_take, ha, two_pow_succ_split]; omega
  · rw [List.length_drop, ha, two_pow_succ_split]; omega

/-- Pushing a power-of-two list onto a stack whose levels all reach its
exponent yields its tree at that level, collapsed into the stack. -/
theorem foldl_push_pow2 (f : α → α → α) (z : α) :
    ∀ (k : Nat) (a : List α) (S : List (Partial α)), a.length = 2 ^ k → (∀ p ∈ S, k ≤ p.level) →
      a.foldl (push f) S = collapse f ({ value := tree f z a, level := k } :: S) := by
  intro k
  induction k with
  | zero =>
    intro a S ha _
    cases a with
    | nil => simp at ha
    | cons x rest =>
      cases rest with
      | nil => simp [push, tree_singleton]
      | cons y rest' => simp at ha
  | succ k ih =>
    intro a S ha hS
    obtain ⟨a1, a2, rfl, h1, h2⟩ := split_halves a k ha
    have step : ∀ T : List (Partial α), (∀ p ∈ T, k + 1 ≤ p.level) →
        (a1 ++ a2).foldl (push f) T = collapse f ({ value := f (tree f z a1) (tree f z a2), level := k + 1 } :: T) := by
      intro T hT
      rw [List.foldl_append, ih a1 T h1 (fun p hp => Nat.le_of_succ_le (hT p hp))]
      rw [collapse_below f { value := tree f z a1, level := k } T (fun q hq => hT q hq)]
      rw [ih a2 _ h2 (by
        intro p hp
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact Nat.le_refl _
        · exact Nat.le_of_succ_le (hT p hp))]
      exact collapse_eq f { value := tree f z a2, level := k } { value := tree f z a1, level := k } T rfl
    have hvalue : tree f z (a1 ++ a2) = f (tree f z a1) (tree f z a2) := by
      apply tree_eq_of_finish
      rw [step [] (by simp), collapse_single]
      simp [finish]
    rw [step S hS, hvalue]

/-- A list shorter than 2^k pushed onto a stack whose levels all reach k
never touches the stack, and its own partials stay below k. -/
theorem foldl_push_short (f : α → α → α) (z : α) :
    ∀ (k : Nat) (b : List α) (S : List (Partial α)), b.length < 2 ^ k → (∀ p ∈ S, k ≤ p.level) →
      b.foldl (push f) S = b.foldl (push f) [] ++ S ∧ ∀ p ∈ b.foldl (push f) [], p.level < k := by
  intro k
  induction k with
  | zero =>
    intro b S hb _
    have : b = [] := List.eq_nil_of_length_eq_zero (by simpa using hb)
    subst this
    simp
  | succ k ih =>
    intro b S hb hS
    by_cases hshort : b.length < 2 ^ k
    · obtain ⟨heq, hlev⟩ := ih b S hshort (fun p hp => Nat.le_of_succ_le (hS p hp))
      exact ⟨heq, fun p hp => Nat.lt_succ_of_lt (hlev p hp)⟩
    · -- 2^k ≤ |b| < 2^(k+1): a full power-of-two prefix and a short rest.
      have hge : 2 ^ k ≤ b.length := Nat.le_of_not_lt hshort
      obtain ⟨c, d, rfl, hcl, hdl⟩ : ∃ c d : List α, b = c ++ d ∧ c.length = 2 ^ k ∧ d.length < 2 ^ k := by
        refine ⟨b.take (2 ^ k), b.drop (2 ^ k), (List.take_append_drop _ _).symm, ?_, ?_⟩
        · rw [List.length_take]; omega
        · rw [List.length_drop]; rw [two_pow_succ_split] at hb; omega
      have run : ∀ T : List (Partial α), (∀ p ∈ T, k + 1 ≤ p.level) →
          (c ++ d).foldl (push f) T = d.foldl (push f) [] ++ ({ value := tree f z c, level := k } : Partial α) :: T := by
        intro T hT
        rw [List.foldl_append, foldl_push_pow2 f z k c T hcl (fun p hp => Nat.le_of_succ_le (hT p hp))]
        rw [collapse_below f { value := tree f z c, level := k } T (fun q hq => hT q hq)]
        obtain ⟨heq, _⟩ := ih d ({ value := tree f z c, level := k } :: T) hdl (by
          intro p hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hp
          · exact Nat.le_refl _
          · exact Nat.le_of_succ_le (hT p hp))
        exact heq
      obtain ⟨_, hdlev⟩ := ih d [] hdl (by simp)
      refine ⟨?_, ?_⟩
      · rw [run S hS, run [] (by simp)]
        simp
      · rw [run [] (by simp)]
        intro p hp
        simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with hp | rfl
        · exact Nat.lt_succ_of_lt (hdlev p hp)
        · exact Nat.lt_succ_self k

/-- **The split.** A power-of-two prefix at least as long as the nonempty
rest splits the tree. -/
theorem tree_append_pow2 (f : α → α → α) (z : α) (k : Nat) (a b : List α)
    (ha : a.length = 2 ^ k) (hb0 : b ≠ []) (hb : b.length ≤ 2 ^ k) :
    tree f z (a ++ b) = f (tree f z a) (tree f z b) := by
  apply tree_eq_of_finish
  rw [List.foldl_append, foldl_push_pow2 f z k a [] ha (by simp), collapse_single]
  by_cases hfull : b.length = 2 ^ k
  · rw [foldl_push_pow2 f z k b _ hfull (by simp),
      collapse_eq f { value := tree f z b, level := k } { value := tree f z a, level := k } [] rfl,
      collapse_single]
    simp [finish]
  · have hlt : b.length < 2 ^ k := Nat.lt_of_le_of_ne hb hfull
    obtain ⟨heq, _⟩ := foldl_push_short f z k b [{ value := tree f z a, level := k }] hlt (by simp)
    rw [heq]
    exact finish_append_last f _ _ _ (tree_nonempty f z b hb0)

/-- The block of at most `S` elements at position `i`. -/
def block (xs : List α) (i S : Nat) : List α := (xs.drop i).take S

/-- The cooperative scheme on blocks: after the strides below `2^k`,
position `i` holds the tree of its block; the next stride combines with
the partner block when it is present. -/
def coop (f : α → α → α) (z : α) (xs : List α) : Nat → Nat → α
  | 0, i => tree f z (block xs i 1)
  | k + 1, i => if i + 2 ^ k < xs.length then f (coop f z xs k i) (coop f z xs k (i + 2 ^ k)) else coop f z xs k i

theorem block_split (xs : List α) (i k : Nat) :
    block xs i (2 ^ (k + 1)) = block xs i (2 ^ k) ++ block xs (i + 2 ^ k) (2 ^ k) := by
  unfold block
  rw [two_pow_succ_split, List.take_add, List.drop_drop]

theorem block_length (xs : List α) (i S : Nat) : (block xs i S).length = min S (xs.length - i) := by
  unfold block; rw [List.length_take, List.length_drop]

/-- **The invariant.** -/
theorem coop_eq_tree (f : α → α → α) (z : α) (xs : List α) :
    ∀ (k i : Nat), coop f z xs k i = tree f z (block xs i (2 ^ k)) := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
    simp only [coop]
    split
    · rename_i hpartner
      rw [ih, ih, block_split]
      apply (tree_append_pow2 f z k _ _ _ _ _).symm
      · rw [block_length]; omega
      · apply List.ne_nil_of_length_pos
        rw [block_length]; omega
      · rw [block_length]; exact Nat.min_le_left _ _
    · rename_i hno
      rw [ih, block_split]
      have hempty : block xs (i + 2 ^ k) (2 ^ k) = [] := by
        unfold block
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hno), List.take_nil]
      rw [hempty, List.append_nil]

/-- **The whole window.** After the last stride, position 0 holds `tree` of
the window when the group covers it. -/
theorem coop_full (f : α → α → α) (z : α) (xs : List α) (k : Nat) (h : xs.length ≤ 2 ^ k) :
    coop f z xs k 0 = tree f z xs := by
  rw [coop_eq_tree]
  unfold block
  rw [List.drop_zero, List.take_of_length_le h]

/-! ## Declaring the order once

`typechecker.lowerAssociativeTree` is the transliteration of `resolve`
(docs/spec/55-parallelism.md section 4): a `reduce.reduce` call takes the
order of its innermost `order` block — `tree` or `left` by name — and under
`order bounded` the regrouping to `chain`, which is admitted only when the
combine declares `laws { associative }`. Outside every block the call is
the exact tree. There is no unchecked order. -/

/-- The orders a block may declare. -/
inductive Order where
  | tree
  | left
  | bounded
  deriving DecidableEq, Repr

/-- The named groupings a call resolves to. -/
inductive Named where
  | tree
  | left
  | chain
  deriving DecidableEq, Repr

/-- The checker's rule: the enclosing block's order (none outside every
block) and whether the combine carries the associativity claim give the
grouping computed, or a refusal. -/
def resolve : Option Order → Bool → Option Named
  | none, _ => some .tree
  | some .tree, _ => some .tree
  | some .left, _ => some .left
  | some .bounded, true => some .chain
  | some .bounded, false => none

/-- The exact order is the default: outside every block, the tree, whatever
the combine claims. -/
theorem resolve_default_exact (claim : Bool) : resolve none claim = some .tree := rfl

/-- `bounded` without the claim is refused. -/
theorem resolve_bounded_needs_claim : resolve (some .bounded) false = none := rfl

/-- `bounded` with the claim is the chain. -/
theorem resolve_bounded_claim : resolve (some .bounded) true = some .chain := rfl

/-- Nothing regroups unless a block says `bounded` and the claim is there:
the chain is reached from no other order and under no missing claim. -/
theorem resolve_regroups_only_bounded (o : Option Order) (claim : Bool)
    (h : resolve o claim = some .chain) : o = some .bounded ∧ claim = true := by
  cases o with
  | none => simp [resolve] at h
  | some o => cases o <;> cases claim <;> simp [resolve] at h ⊢

/-- A named order keeps its name: `tree` and `left` resolve to themselves
whatever the combine claims. -/
theorem resolve_named (claim : Bool) :
    resolve (some .tree) claim = some .tree ∧ resolve (some .left) claim = some .left :=
  ⟨rfl, rfl⟩

/-- What a resolved name computes. -/
def compute (f : α → α → α) (z : α) (xs : List α) : Named → α
  | .tree => tree f z xs
  | .left => left f z xs
  | .chain => chainFold f z xs

/-- Soundness of the regrouping: when the claim holds, the chain `bounded`
computes is the exact tree's value on every input, so a true law costs no
bits — and a false law is the only way the two differ. -/
theorem bounded_sound (f : α → α → α) (hf : Assoc f) (z : α) (xs : List α) :
    compute f z xs .chain = compute f z xs .tree :=
  (tree_eq_chainFold f hf z xs).symm

/-! ## The lane rule as an order

`reduce.lanes` (docs/spec/55-parallelism.md section 4; the ml pilot's F2):
`2^k` lane-strided partial accumulators, element `i` folded into lane
`laneOf i run (2^k)` in index order from `z`, then the xor butterfly over
the partials — rounds at offsets `2^k / 2, …, 1`, every lane taking
`f acc[l] acc[l ^ off]` from the values before the round — whose lane 0
is the result. `bfly` is that lane's value by halving: in the round at
offset `half`, lane `l < half` takes `f v[l] v[l + half]`, and the later
rounds never leave the lower half. `lanes_eq_left` is the theorem the
order rests on: under a commutative monoid it is the sequential fold, so
the lane rule is a legal regrouping wherever `laws { associative,
commutative, identity(z) }` hold, and for floating point it is one of the
groupings `Oak.FloatBounds` bounds. -/

/-- The lane element `i` lands in, with runs of `run` consecutive elements
per lane. -/
def laneOf (i run count : Nat) : Nat := (i / run) % count

theorem laneOf_lt (i run count : Nat) (h : 0 < count) : laneOf i run count < count :=
  Nat.mod_lt _ h

/-- Fold `x` into slot `l` of the partials; a slot past the end is left. -/
def into (f : α → α → α) (acc : List α) (l : Nat) (x : α) : List α :=
  match acc[l]? with
  | some a => acc.set l (f a x)
  | none => acc

theorem into_zero (f : α → α → α) (a : α) (rest : List α) (x : α) :
    into f (a :: rest) 0 x = f a x :: rest := by
  simp [into]

theorem into_succ (f : α → α → α) (a : α) (rest : List α) (m : Nat) (x : α) :
    into f (a :: rest) (m + 1) x = a :: into f rest m x := by
  cases h : rest[m]? <;> simp [into, h]

theorem length_into (f : α → α → α) (acc : List α) (l : Nat) (x : α) :
    (into f acc l x).length = acc.length := by
  cases h : acc[l]? <;> simp [into, h]

/-- The partials after folding the elements from index `i`, each into the
slot `slot` names for its index. -/
def accum (f : α → α → α) (slot : Nat → Nat) : List α → Nat → List α → List α
  | acc, _, [] => acc
  | acc, i, x :: xs => accum f slot (into f acc (slot i) x) (i + 1) xs

theorem length_accum (f : α → α → α) (slot : Nat → Nat) :
    ∀ (xs : List α) (acc : List α) (i : Nat), (accum f slot acc i xs).length = acc.length
  | [], acc, i => rfl
  | x :: xs, acc, i => by
    rw [accum, length_accum f slot xs, length_into]

/-- Lane 0 of the butterfly over `2^k` partials. -/
def bfly (f : α → α → α) (z : α) : Nat → List α → α
  | 0, v => v.headD z
  | k + 1, v => bfly f z k (List.zipWith f (v.take (2 ^ k)) (v.drop (2 ^ k)))

/-- `reduce.lanes` over `2^k` lanes. -/
def lanes (f : α → α → α) (z : α) (run k : Nat) (xs : List α) : α :=
  bfly f z k (accum f (fun i => laneOf i run (2 ^ k)) (List.replicate (2 ^ k) z) 0 xs)

theorem bfly_one (f : α → α → α) (z a : α) : bfly f z 0 [a] = a := rfl

/-- Two lanes: lane 0 with lane 1. -/
theorem bfly_two (f : α → α → α) (z a b : α) : bfly f z 1 [a, b] = f a b := rfl

/-- Four lanes: the round at offset 2 pairs 0 with 2 and 1 with 3, the round
at offset 1 combines the two. -/
theorem bfly_four (f : α → α → α) (z a b c d : α) :
    bfly f z 2 [a, b, c, d] = f (f a c) (f b d) := rfl

/-- Eight lanes: offsets 4, 2, 1. -/
theorem bfly_eight (f : α → α → α) (z a b c d e g h i : α) :
    bfly f z 3 [a, b, c, d, e, g, h, i] = f (f (f a e) (f c h)) (f (f b g) (f d i)) := rfl

/-- One lane folds every element in order: `reduce.lanes` at one lane is
`reduce.left`. -/
theorem accum_single (f : α → α → α) (slot : Nat → Nat) (hs : ∀ j, slot j = 0) :
    ∀ (xs : List α) (a : α) (i : Nat), accum f slot [a] i xs = [xs.foldl f a]
  | [], a, i => rfl
  | x :: xs, a, i => by
    rw [accum, hs, into_zero, accum_single f slot hs xs, List.foldl_cons]

theorem lanes_one (f : α → α → α) (z : α) (run : Nat) (xs : List α) :
    lanes f z run 0 xs = left f z xs := by
  unfold lanes left
  rw [Nat.pow_zero, List.replicate_one,
    accum_single f (fun i => laneOf i run 1) (fun j => Nat.mod_one _) xs z 0]
  rfl

/-! ### Under a commutative monoid the lane rule is the sequential fold -/

/-- Commutativity. -/
def Comm (f : α → α → α) : Prop := ∀ a b, f a b = f b a

/-- `z` is a left identity (with `Comm`, a two-sided one). -/
def LeftId (f : α → α → α) (z : α) : Prop := ∀ a, f z a = a

theorem right_id (f : α → α → α) (z : α) (hc : Comm f) (hz : LeftId f z) (a : α) : f a z = a := by
  rw [hc, hz]

section CommMonoid
variable (f : α → α → α) (z : α) (hf : Assoc f) (hc : Comm f) (hz : LeftId f z)
include hf hc hz

theorem foldl_from (l : List α) : ∀ a, l.foldl f a = f a (l.foldl f z) := by
  induction l with
  | nil => intro a; simp [right_id f z hc hz]
  | cons x l ih =>
    intro a
    rw [List.foldl_cons, List.foldl_cons, ih (f a x), ih (f z x), hz, hf]

/-- The fold of a cons: the head combined with the fold of the tail. -/
theorem total_cons (a : α) (l : List α) : (a :: l).foldl f z = f a (l.foldl f z) := by
  rw [List.foldl_cons, hz, foldl_from f z hf hc hz]

theorem total_append (l m : List α) : (l ++ m).foldl f z = f (l.foldl f z) (m.foldl f z) := by
  induction l with
  | nil => rw [List.nil_append, List.foldl_nil, hz]
  | cons x l ih => rw [List.cons_append, total_cons f z hf hc hz, total_cons f z hf hc hz, ih, hf]

theorem total_replicate (n : Nat) : (List.replicate n z).foldl f z = z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, total_cons f z hf hc hz, ih, hz]

omit hz in
/-- The commutative-monoid rearrangement `(a b)(c d) = (a c)(b d)`. -/
theorem exchange (a b c d : α) : f (f a b) (f c d) = f (f a c) (f b d) := by
  rw [hf, ← hf b c d, hc b c, hf c b d, ← hf]

/-- Folding `x` into one slot combines it into the total. -/
theorem total_into (x : α) : ∀ (acc : List α) (l : Nat), l < acc.length →
    (into f acc l x).foldl f z = f (acc.foldl f z) x
  | [], l, h => absurd h (Nat.not_lt_zero l)
  | a :: rest, 0, _ => by
    rw [into_zero, total_cons f z hf hc hz, total_cons f z hf hc hz, hf, hc x, ← hf]
  | a :: rest, m + 1, h => by
    rw [into_succ, total_cons f z hf hc hz, total_into x rest m (Nat.lt_of_succ_lt_succ h),
      total_cons f z hf hc hz, hf]

/-- The partials' total is the fold of the elements so far. -/
theorem total_accum (slot : Nat → Nat) :
    ∀ (xs : List α) (acc : List α) (i : Nat), (∀ j, slot j < acc.length) →
    (accum f slot acc i xs).foldl f z = xs.foldl f (acc.foldl f z)
  | [], acc, i, _ => rfl
  | x :: xs, acc, i, hs => by
    rw [accum, total_accum slot xs _ (i + 1) (fun j => by rw [length_into]; exact hs j),
      total_into f z hf hc hz x acc (slot i) (hs i), List.foldl_cons]

/-- Combining two lists lane by lane totals to the two totals combined. -/
theorem total_zipWith : ∀ (l m : List α), l.length = m.length →
    (List.zipWith f l m).foldl f z = f (l.foldl f z) (m.foldl f z)
  | [], [], _ => by rw [List.zipWith_nil_left, List.foldl_nil, hz]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: m, h => by
    rw [List.zipWith_cons_cons, total_cons f z hf hc hz, total_zipWith l m (by simpa using h),
      total_cons f z hf hc hz, total_cons f z hf hc hz, exchange f hf hc]

/-- The butterfly's lane 0 is the total of the partials. -/
theorem bfly_total : ∀ (k : Nat) (v : List α), v.length = 2 ^ k → bfly f z k v = v.foldl f z
  | 0, v, h => by
    match v, h with
    | [a], _ => simp [bfly, total_cons f z hf hc hz, right_id f z hc hz]
  | k + 1, v, h => by
    have hlen : (List.zipWith f (v.take (2 ^ k)) (v.drop (2 ^ k))).length = 2 ^ k := by
      rw [List.length_zipWith, List.length_take, List.length_drop, h, Nat.pow_succ]
      omega
    have htake : (v.take (2 ^ k)).length = (v.drop (2 ^ k)).length := by
      rw [List.length_take, List.length_drop, h, Nat.pow_succ]
      omega
    rw [bfly, bfly_total k _ hlen, total_zipWith f z hf hc hz _ _ htake,
      ← total_append f z hf hc hz, List.take_append_drop]

/-- **The lane rule is the sequential fold** under a commutative monoid:
whatever the lane count and run, `reduce.lanes` is `reduce.left`. -/
theorem lanes_eq_left (run k : Nat) (xs : List α) : lanes f z run k xs = left f z xs := by
  unfold lanes left
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  rw [bfly_total f z hf hc hz k _ (by rw [length_accum, List.length_replicate]),
    total_accum f z hf hc hz _ xs _ 0
      (fun j => by rw [List.length_replicate]; exact laneOf_lt j run _ hpos),
    total_replicate f z hf hc hz]

end CommMonoid

/-! ## The simdgroup shuffle spells the butterfly

`simd_shuffle_xor(v, off)` (docs/spec/56-kernels.md section 2a) gives lane
`l` the value lane `l ^ off` holds. One round of the butterfly at offset
`half` over `2 * half` lanes therefore pairs lane `l < half` with
`l + half` and lane `l ≥ half` with `l - half`; `shuffleRound` is that
round on the vector of every lane's value, and `shuffleButterfly` the
rounds at descending offsets. `shuffle_butterfly_lane0` is the theorem a
kernel that spells `v = f(v, simd_shuffle_xor(v, off))` for `off = G/2 …
1` relies on: lane 0 ends holding exactly `bfly f z k v`, the lane-rule
butterfly of `reduce.lanes`, so the hand-spelled reduction computes the
bits `group_lanes` computes. The rounds below `half` never pair a lower
lane with an upper one, which is why the lower half after a round is all
lane 0 ever reads again (`shuffleRound_take`). -/

/-- One butterfly round over `2 * half` lanes: lane `l` takes
`f v[l] v[l ^ half]`. -/
def shuffleRound (f : α → α → α) (half : Nat) (v : List α) : List α :=
  List.zipWith f (v.take half) (v.drop half) ++ List.zipWith f (v.drop half) (v.take half)

/-- The rounds at offsets `2^(k-1), …, 1`, every lane updated. -/
def shuffleButterfly (f : α → α → α) : Nat → List α → List α
  | 0, v => v
  | k + 1, v => shuffleButterfly f k (shuffleRound f (2 ^ k) v)

theorem shuffleRound_length (f : α → α → α) (half : Nat) (v : List α) (hlen : v.length = 2 * half) :
    (shuffleRound f half v).length = 2 * half := by
  unfold shuffleRound
  rw [List.length_append, List.length_zipWith, List.length_zipWith, List.length_take, List.length_drop, hlen]
  omega

theorem zipWith_take_right (f : α → α → α) : ∀ (l m : List α) (n : Nat), l.length ≤ n →
    List.zipWith f l (m.take n) = List.zipWith f l m
  | [], _, _, _ => by simp
  | _ :: _, [], _, _ => by simp
  | a :: l, b :: m, n, h => by
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.take_succ_cons, List.zipWith_cons_cons]
      rw [zipWith_take_right f l m n (by simpa using h)]

/-- The lower half after a round is the halving butterfly's next vector,
for any vector long enough for the round. -/
theorem shuffleRound_take (f : α → α → α) (half : Nat) (v : List α) (hlen : 2 * half ≤ v.length) :
    (shuffleRound f half v).take half = List.zipWith f (v.take half) (v.drop half) := by
  unfold shuffleRound
  have h : (List.zipWith f (v.take half) (v.drop half)).length = half := by
    rw [List.length_zipWith, List.length_take, List.length_drop]
    omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-- A round at offset `2^k` pairs each of the lower `2^(k+1)` lanes within
that block, so the lower half of the round of `w` is the round of the
lower half of `w`, as far as lane 0 reads. -/
theorem shuffleRound_lower (f : α → α → α) (k : Nat) (w : List α) (hlen : 2 ^ (k + 2) ≤ w.length) :
    (shuffleRound f (2 ^ k) w).take (2 ^ k) = (shuffleRound f (2 ^ k) (w.take (2 ^ (k + 1)))).take (2 ^ k) := by
  have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hk2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ 2 (k + 1)]; omega
  rw [shuffleRound_take f (2 ^ k) w (by omega),
    shuffleRound_take f (2 ^ k) (w.take (2 ^ (k + 1))) (by rw [List.length_take]; omega),
    List.take_take, List.drop_take, Nat.min_eq_left (by omega)]
  rw [zipWith_take_right f (w.take (2 ^ k)) (w.drop (2 ^ k)) (2 ^ (k + 1) - 2 ^ k)
    (by rw [List.length_take]; omega)]

/-- The rounds that follow a round at `2^k` keep to the lower `2^k` lanes,
so lane 0 of the whole is lane 0 of the lower half's butterfly. -/
theorem shuffle_lower (f : α → α → α) (z : α) :
    ∀ (k : Nat) (w : List α), 2 ^ (k + 1) ≤ w.length →
      (shuffleButterfly f k w).headD z = (shuffleButterfly f k (w.take (2 ^ k))).headD z
  | 0, w, _ => by
    simp only [shuffleButterfly, Nat.pow_zero]
    cases w with
    | nil => rfl
    | cons a _ => rfl
  | k + 1, w, hlen => by
    simp only [shuffleButterfly]
    have hk : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
    have hk2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ 2 (k + 1)]; omega
    have h1 := shuffle_lower f z k (shuffleRound f (2 ^ k) w) (by
      unfold shuffleRound
      rw [List.length_append, List.length_zipWith, List.length_zipWith, List.length_take, List.length_drop]
      omega)
    have h2 := shuffle_lower f z k (shuffleRound f (2 ^ k) (w.take (2 ^ (k + 1)))) (by
      unfold shuffleRound
      rw [List.length_append, List.length_zipWith, List.length_zipWith, List.length_take, List.length_drop, List.length_take]
      omega)
    rw [h1, h2, shuffleRound_lower f k w hlen]

/-- **Lane 0 of the shuffled butterfly is the halving butterfly.** -/
theorem shuffle_butterfly_lane0 (f : α → α → α) (z : α) :
    ∀ (k : Nat) (v : List α), v.length = 2 ^ k → (shuffleButterfly f k v).headD z = bfly f z k v
  | 0, v, _ => rfl
  | k + 1, v, hlen => by
    simp only [shuffleButterfly, bfly]
    have hround : (shuffleRound f (2 ^ k) v).length = 2 ^ (k + 1) := by
      rw [shuffleRound_length f (2 ^ k) v (by rw [hlen, Nat.pow_succ]; omega), Nat.pow_succ]; omega
    rw [shuffle_lower f z k _ (Nat.le_of_eq hround.symm), shuffleRound_take f (2 ^ k) v (by rw [hlen, Nat.pow_succ]; omega)]
    exact shuffle_butterfly_lane0 f z k _ (by
      rw [List.length_zipWith, List.length_take, List.length_drop, hlen, Nat.pow_succ]; omega)

end Oak.Reduce
