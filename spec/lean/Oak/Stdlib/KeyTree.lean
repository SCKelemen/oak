namespace Oak.Stdlib.KeyTree

/-! # Key trees: finite maps the kernel can search

A `KTree` is a balanced binary search tree over `Nat` keys written out as a
term by a generator (`stdlib/generate_normalize.py` for the Unicode tables).
`lookup` descends by comparing the key with each node's split, so a query
costs one `Nat` comparison per level — the shape the kernel evaluates
quickly when a theorem is decided over thousands of table entries. `entries`
lists the leaves; `lookup_mem` connects a successful lookup to that list, so
a property decided over `entries` transfers to every key the tree answers. -/

inductive KTree (α : Type) where
  | nil
  | leaf (key : Nat) (val : α)
  | node (split : Nat) (left right : KTree α)

variable {α : Type}

/-- The value stored under `x`, if any. Keys below a node's split live in
    its left subtree, the rest in the right. -/
def lookup : KTree α → Nat → Option α
  | .nil, _ => none
  | .leaf k v, x => if x = k then some v else none
  | .node s l r, x => if x < s then lookup l x else lookup r x

/-- Every leaf, left to right. -/
def entries : KTree α → List (Nat × α)
  | .nil => []
  | .leaf k v => [(k, v)]
  | .node _ l r => entries l ++ entries r

theorem lookup_mem : ∀ (t : KTree α) (x : Nat) (v : α), lookup t x = some v → (x, v) ∈ entries t
  | .nil, _, _, h => by simp [lookup] at h
  | .leaf k w, x, v, h => by
    simp only [lookup] at h
    split at h
    · rename_i hx
      simp only [Option.some.injEq] at h
      subst hx; subst h
      simp [entries]
    · simp at h
  | .node s l r, x, v, h => by
    simp only [lookup] at h
    simp only [entries, List.mem_append]
    split at h
    · exact Or.inl (lookup_mem l x v h)
    · exact Or.inr (lookup_mem r x v h)

/-- A property decided over the entry list holds of every successful lookup. -/
theorem lookup_prop (t : KTree α) (p : Nat → α → Bool)
    (hall : (entries t).all (fun e => p e.1 e.2) = true) (x : Nat) (v : α)
    (h : lookup t x = some v) : p x v = true := by
  have hm := lookup_mem t x v h
  rw [List.all_eq_true] at hall
  exact hall (x, v) hm

end Oak.Stdlib.KeyTree
