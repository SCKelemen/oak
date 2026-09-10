import Oak.Modules

/-!
# Oak.Semver — API change classification and the exact-bump rule

Formal model of `docs/spec/82-package-semver.md` sections 2, 3, and 6:
how the public changes between two API snapshots are classified into a
release level, which version that level requires, and how package levels
combine into a module level. The Go procedures `packageapi.Compare`,
`packageapi.NextVersion`, `packageapi.Enforce`, and
`packageapi.CompareModules` are transliterations of the definitions here and
are tested against the same laws (`packageapi/semver_laws_test.go`).

The laws:

* **Classification is the maximum.** The level of a change set bounds every
  member and is bounded by any bound on the members
  (`classify_ge`, `classify_le_bound`); adding changes never lowers the level
  (`classify_mono`).
* **Per-export rule.** An export is unchanged exactly when its kind, semantic
  type, and ABI are all unchanged; removal or mutation is major, addition is
  minor (`exportChange_none_iff`, `exportChange_cases`).
* **Exact bump.** The required next version is a function of the previous
  version and the level, strictly greater than the previous version
  (`next_gt`), unique (`enforce_unique`), and at or after 1.0.0 the level is
  recoverable from the bump (`next_injective_level`); before 1.0.0 breaking
  and additive changes coincide (`next_pre1_major_eq_minor`).
* **Module level.** A module's level is the maximum over its packages, where a
  removed package is major and an added one minor (`moduleLevel_ge`,
  `moduleLevel_patch_iff`).
-/

namespace Oak.Modules.Semver

open Oak.Modules.Versions (Version)

/-- Release levels (`packageapi.ChangeLevel`), ordered patch < minor < major. -/
inductive Level
  | patch
  | minor
  | major
  deriving DecidableEq, Repr

namespace Level

def toNat : Level → Nat
  | .patch => 0
  | .minor => 1
  | .major => 2

/-- `Report.add` keeps the higher level. -/
def max (a b : Level) : Level := if a.toNat < b.toNat then b else a

def LE (a b : Level) : Prop := a.toNat ≤ b.toNat

theorem LE_refl (a : Level) : LE a a := Nat.le_refl _

theorem LE_trans {a b c : Level} (h₁ : LE a b) (h₂ : LE b c) : LE a c := Nat.le_trans h₁ h₂

theorem LE_antisymm {a b : Level} (h₁ : LE a b) (h₂ : LE b a) : a = b := by
  cases a <;> cases b <;> simp_all [LE, toNat]

theorem patch_le (a : Level) : LE .patch a := by cases a <;> simp [LE, toNat]

theorem le_major (a : Level) : LE a .major := by cases a <;> simp [LE, toNat]

theorem le_patch_iff (a : Level) : LE a .patch ↔ a = .patch := by
  cases a <;> simp [LE, toNat]

theorem max_ge_left (a b : Level) : LE a (max a b) := by
  unfold max LE; split <;> omega

theorem max_ge_right (a b : Level) : LE b (max a b) := by
  unfold max LE; split <;> omega

theorem max_le {a b c : Level} (h₁ : LE a c) (h₂ : LE b c) : LE (max a b) c := by
  unfold max LE at *; split <;> assumption

end Level

/-- Classification of a change set: the fold `Report.add` performs, starting
from patch (`Compare` initializes `Required: Patch`). -/
def classify (changes : List Level) : Level := changes.foldl Level.max .patch

theorem foldl_max_ge_acc (acc : Level) (rest : List Level) :
    Level.LE acc (rest.foldl Level.max acc) := by
  induction rest generalizing acc with
  | nil => exact Level.LE_refl _
  | cons l rest ih =>
    simp only [List.foldl_cons]
    exact Level.LE_trans (Level.max_ge_left acc l) (ih _)

theorem foldl_max_ge_mem (acc : Level) (rest : List Level) (l : Level) (h : l ∈ rest) :
    Level.LE l (rest.foldl Level.max acc) := by
  induction rest generalizing acc with
  | nil => cases h
  | cons m rest ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Level.LE_trans (Level.max_ge_right acc l) (foldl_max_ge_acc _ _)
    · exact ih _ h

theorem foldl_max_le_bound (acc : Level) (rest : List Level) (bound : Level)
    (hacc : Level.LE acc bound) (hrest : ∀ l ∈ rest, Level.LE l bound) :
    Level.LE (rest.foldl Level.max acc) bound := by
  induction rest generalizing acc with
  | nil => exact hacc
  | cons m rest ih =>
    simp only [List.foldl_cons]
    exact ih _ (Level.max_le hacc (hrest m (List.mem_cons_self ..)))
      (fun l hl => hrest l (List.mem_cons_of_mem _ hl))

/-- Every recorded change is at most the classification. -/
theorem classify_ge (changes : List Level) (l : Level) (h : l ∈ changes) :
    Level.LE l (classify changes) :=
  foldl_max_ge_mem _ _ _ h

/-- The classification is the least level above every change. -/
theorem classify_le_bound (changes : List Level) (bound : Level)
    (h : ∀ l ∈ changes, Level.LE l bound) : Level.LE (classify changes) bound :=
  foldl_max_le_bound _ _ _ (Level.patch_le _) h

/-- Adding changes never lowers the classification: a superset of changes
classifies at least as high. -/
theorem classify_mono (a b : List Level) (h : ∀ l ∈ a, l ∈ b) :
    Level.LE (classify a) (classify b) :=
  classify_le_bound a _ (fun l hl => classify_ge b l (h l hl))

/-- A change set classifies as patch exactly when it contains no non-patch
change. -/
theorem classify_patch_iff (changes : List Level) :
    classify changes = .patch ↔ ∀ l ∈ changes, l = .patch := by
  constructor
  · intro h l hl
    have := classify_ge changes l hl
    rw [h] at this
    exact (Level.le_patch_iff l).mp this
  · intro h
    exact (Level.le_patch_iff _).mp (classify_le_bound changes .patch
      (fun l hl => by rw [h l hl]; exact Level.LE_refl _))

/-- One export's checked identity (`packageapi.Export`): kind, canonical
semantic type, canonical ABI, each abstracted to a code. -/
structure Export where
  kind : Nat
  type : Nat
  abi : Nat
  deriving DecidableEq, Repr

/-- The per-export rule of `Compare`: absent → present is an addition (minor),
present → absent a removal (major), any difference in kind, type, or ABI a
breaking change (major), and identity no change at all. -/
def exportChange (old new : Option Export) : Option Level :=
  match old, new with
  | none, none => none
  | some _, none => some .major
  | none, some _ => some .minor
  | some o, some n => if o = n then none else some .major

/-- An export contributes no change exactly when its checked identity is
unchanged. -/
theorem exportChange_none_iff (old new : Option Export) :
    exportChange old new = none ↔ old = new := by
  cases old <;> cases new <;> simp [exportChange]

/-- The only levels an export can contribute, and when. -/
theorem exportChange_cases (old new : Option Export) :
    (exportChange old new = some .minor ↔ old = none ∧ new ≠ none) ∧
    (exportChange old new = some .major ↔ old ≠ none ∧ old ≠ new) := by
  cases old <;> cases new <;> simp [exportChange]

/-- The required next version (`packageapi.NextVersion`): before 1.0.0 both
breaking and additive changes advance the minor component. -/
def next (v : Version) : Level → Version
  | .major => if v.major = 0 then ⟨0, v.minor + 1, 0⟩ else ⟨v.major + 1, 0, 0⟩
  | .minor => ⟨v.major, v.minor + 1, 0⟩
  | .patch => ⟨v.major, v.minor, v.patch + 1⟩

/-- The exact-bump rule (`packageapi.Enforce`): the declared version must be
the required next version. -/
def enforce (previous : Version) (level : Level) (declared : Version) : Prop :=
  declared = next previous level

/-- The next version is strictly greater than the previous. -/
theorem next_gt (v : Version) (l : Level) :
    Versions.LE v (next v l) ∧ next v l ≠ v := by
  obtain ⟨M, m, p⟩ := v
  cases l with
  | patch => simp [next, Versions.LE]
  | minor => simp [next, Versions.LE]
  | major =>
    by_cases h : M = 0
    · subst h; simp [next, Versions.LE]
    · simp [next, Versions.LE, h]

/-- Exactly one declared version satisfies the rule. -/
theorem enforce_unique (previous : Version) (level : Level) (d₁ d₂ : Version)
    (h₁ : enforce previous level d₁) (h₂ : enforce previous level d₂) : d₁ = d₂ := by
  unfold enforce at *; rw [h₁, h₂]

/-- The rule is satisfiable: the required version itself. -/
theorem enforce_next (previous : Version) (level : Level) :
    enforce previous level (next previous level) := rfl

/-- Before 1.0.0 a breaking change and an additive change require the same
version. -/
theorem next_pre1_major_eq_minor (v : Version) (h : v.major = 0) :
    next v .major = next v .minor := by
  simp [next, h]

/-- At or after 1.0.0 the level is recoverable from the bump: distinct levels
require distinct versions. -/
theorem next_injective_level (v : Version) (h : 1 ≤ v.major) (a b : Level)
    (hab : next v a = next v b) : a = b := by
  have hz : v.major ≠ 0 := by omega
  cases a <;> cases b <;> simp [next, hz] at hab <;> first | rfl | omega

/-- A major bump at or after 1.0.0 resets minor and patch; a minor bump
resets patch. -/
theorem next_resets (v : Version) (h : 1 ≤ v.major) :
    (next v .major).minor = 0 ∧ (next v .major).patch = 0 ∧ (next v .minor).patch = 0 := by
  have hz : v.major ≠ 0 := by omega
  simp [next, hz]

/-- One package's state on each side of a module comparison: absent, or
present with its export change set already classified. -/
inductive PackageState
  | absent
  | present (changes : List Level)

/-- The per-package rule of `CompareModules`: added minor, removed major,
otherwise the package's own classification. -/
def packageLevel : PackageState → PackageState → Option Level
  | .absent, .absent => none
  | .present _, .absent => some .major
  | .absent, .present _ => some .minor
  | .present _, .present changes => some (classify changes)

/-- The module level is the classification of the package levels. -/
def moduleLevel (packages : List (PackageState × PackageState)) : Level :=
  classify (packages.filterMap (fun p => packageLevel p.1 p.2))

/-- Every package's level is at most the module's. -/
theorem moduleLevel_ge (packages : List (PackageState × PackageState))
    (p : PackageState × PackageState) (hp : p ∈ packages) (l : Level)
    (hl : packageLevel p.1 p.2 = some l) : Level.LE l (moduleLevel packages) :=
  classify_ge _ _ (List.mem_filterMap.mpr ⟨p, hp, hl⟩)

/-- A module is patch-compatible exactly when no package was added or
removed and every surviving package is patch-compatible. -/
theorem moduleLevel_patch_iff (packages : List (PackageState × PackageState)) :
    moduleLevel packages = .patch ↔
      ∀ p ∈ packages, ∀ l, packageLevel p.1 p.2 = some l → l = .patch := by
  unfold moduleLevel
  rw [classify_patch_iff]
  constructor
  · intro h p hp l hl
    exact h l (List.mem_filterMap.mpr ⟨p, hp, hl⟩)
  · intro h l hl
    obtain ⟨p, hp, hpl⟩ := List.mem_filterMap.mp hl
    exact h p hp l hpl

/-- Removing a package is always a breaking change for the module. -/
theorem moduleLevel_removed (packages : List (PackageState × PackageState))
    (changes : List Level) (h : (.present changes, .absent) ∈ packages) :
    moduleLevel packages = .major :=
  Level.LE_antisymm (Level.le_major _)
    (moduleLevel_ge packages _ h .major rfl)

end Oak.Modules.Semver
