import Oak.Modules

/-! # Compiler correspondence for the module system's decision procedures

`Oak.Modules` states the module-system laws over the concrete decision
procedures the compiler runs: `lookup`, `order`, `decode`/`mangle`, and
`select`, each a line-for-line transliteration of the Go functions in
`modules/` (`Lookup`, `Order`, `Demangle`/`Mangle`, `Select`). This module
states the correspondence in refinement form: for each procedure, the
concrete decision agrees exactly with an abstract specification stated
without reference to the procedure.

The correspondence is scoped: it covers the pure decision procedures — which
qualified references resolve, in what order packages compile, how internal
names decode, which version a module gets — not the loader's filesystem
traversal, syntax-tree rewriting, or diagnostics. The Go functions are
maintained as transliterations of the definitions in `Oak.Modules`;
`modules/modules_test.go` exercises the same laws (with a randomized
injectivity witness) against the Go code. -/

namespace Oak.ModulesRefinement

open Oak.Modules

namespace Visibility

open Oak.Modules.Visibility

/-- **Abstract reachability.** A member is reachable through an import exactly
    when the package declares it, marks it exported, and — when the import
    is sealed — the signature lists it. -/
def Reachable (exports : Nat → Option Member) (sig : Option Signature) (name : Nat)
    (m : Member) : Prop :=
  exports name = some m ∧ m.exported = true ∧ (∀ s, sig = some s → name ∈ s.members)

/-- **Resolution correspondence.** The compiler's `lookup` resolves exactly
    the abstractly reachable members, to exactly those members. -/
theorem lookup_iff_reachable (exports : Nat → Option Member) (sig : Option Signature) (name : Nat)
    (m : Member) : lookup exports sig name = .resolved m ↔ Reachable exports sig name m := by
  constructor
  · intro h
    refine ⟨?_, lookup_never_private exports sig name m h, ?_⟩
    · cases sig with
      | none => exact (lookupMember_resolved exports name m h).1
      | some s => exact (lookupMember_resolved exports name m (lookup_sealed_narrows exports s name m h)).1
    · intro s hs
      subst hs
      exact lookup_sealed_subset exports s name m h
  · rintro ⟨hm, he, hs⟩
    cases sig with
    | none => exact lookup_exported_resolves exports name m hm he
    | some s =>
      have hmem := hs s rfl
      simp [lookup, hmem, lookupMember, hm, he]

/-- **Every failure is a non-reachability.** When `lookup` does not resolve,
    no member is reachable: the compiler never rejects a reachable member. -/
theorem lookup_unresolved_iff (exports : Nat → Option Member) (sig : Option Signature) (name : Nat) :
    (∀ m, lookup exports sig name ≠ .resolved m) ↔ (∀ m, ¬ Reachable exports sig name m) := by
  constructor
  · intro h m hr
    exact h m ((lookup_iff_reachable exports sig name m).mpr hr)
  · intro h m hl
    exact h m ((lookup_iff_reachable exports sig name m).mp hl)

end Visibility

namespace Order

open Oak.Modules.Order

/-- **Abstract compile order.** A list is a valid compile order for a closed
    graph when it is a permutation of the packages and every package follows
    its imports. -/
def ValidOrder (g : Graph) (nodes order : List Nat) : Prop :=
  order.Perm nodes ∧ OrderedFrom g [] order

/-- **Order correspondence, soundness.** Whenever the compiler's Kahn
    procedure places every package (no stuck set), its result is a valid
    compile order. -/
theorem order_complete_refines (g : Graph) (nodes : List Nat)
    (h : (order g nodes).2 = []) : ValidOrder g nodes (order g nodes).1 := by
  refine ⟨?_, order_ordered g nodes⟩
  have hperm := order_perm g nodes
  rw [h, List.append_nil] at hperm
  exact hperm

/-- **Order correspondence, failure.** When the compiler reports a stuck set
    in a closed graph, the stuck set is a cycle witness: every stuck package
    imports a stuck package, so no valid order can exist for those packages
    (a valid order would have to place one of them first, with all its
    imports before it). -/
theorem order_stuck_refines (g : Graph) (nodes : List Nat)
    (hclosed : ∀ n ∈ nodes, ∀ d ∈ g.imports n, d ∈ nodes) :
    ∀ n ∈ (order g nodes).2, ∃ d ∈ g.imports n, d ∈ (order g nodes).2 :=
  order_stuck_cycle g nodes hclosed

end Order

namespace Mangle

open Oak.Modules.Mangle

/-- **Naming correspondence.** The compiler's decoder is a left inverse of
    the compiler's mangler on rune sequences, so internal names are in
    bijection with (package path, declaration name) pairs. -/
theorem naming_refines (path name : List Nat) (hp : Runes path) (hn : Runes name) :
    decode (mangle path name) = some (path, name) :=
  decode_mangle path name hp hn

/-- **Reserved-name correspondence.** An identifier accepted by the reserved
    check (`splitDouble = none`, no `__`) is never an internal name. -/
theorem user_identifier_not_internal (ident path name : List Nat) (hp : Runes path)
    (huser : splitDouble ident = none) : ident ≠ mangle path name := by
  intro h
  have := mangle_reserved path name hp
  unfold Reserved at this
  exact this (h ▸ huser)

end Mangle

namespace Versions

open Oak.Modules.Versions

theorem LE_antisymm (a b : Version) (h₁ : Oak.Modules.Versions.LE a b)
    (h₂ : Oak.Modules.Versions.LE b a) : a = b := by
  cases a with
  | mk a1 a2 a3 =>
    cases b with
    | mk b1 b2 b3 =>
      simp only [Oak.Modules.Versions.LE] at h₁ h₂
      simp only [Version.mk.injEq]
      omega

/-- **Abstract minimal version.** The version a module gets is the least
    version at or above every requirement, and it is one of them. -/
def MinimalVersion (reqs : List Version) (s : Version) : Prop :=
  s ∈ reqs ∧ ∀ v ∈ reqs, Oak.Modules.Versions.LE v s

/-- **Selection correspondence.** The compiler's fold selects a version
    exactly when it is the abstract minimal version. -/
theorem select_iff_minimal (reqs : List Version) (s : Version) :
    select reqs = some s ↔ MinimalVersion reqs s := by
  constructor
  · intro h
    exact ⟨select_mem reqs s h, select_satisfies reqs s h⟩
  · rintro ⟨hmem, hbound⟩
    cases reqs with
    | nil => cases hmem
    | cons v rest =>
      have hsel : select (v :: rest) = some (rest.foldl step v) := rfl
      have hsat := select_satisfies (v :: rest) _ hsel
      have hmin := select_minimal (v :: rest) _ s hsel hbound
      have := LE_antisymm _ _ hmin (hsat s hmem)
      rw [hsel, this]

end Versions

end Oak.ModulesRefinement
