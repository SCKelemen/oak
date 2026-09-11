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

end Oak.Reduce
