namespace Oak.Modules

/-! # Module system laws

Model for `docs/spec/83-modules.md`: the pure decision procedures of the Oak
module system, kept as transliterations of the Go package `modules/`
(`Escape`/`Unescape`/`Mangle`/`Demangle` in `mangle.go`, `Order` in
`order.go`, `Lookup`/`ProjectionAllowed` in `lookup.go`, `Select` in
`version.go`).

Four law families are proved:

* **Naming** (§7): the internal name of a package-level declaration is
  `escape path ++ "__" ++ escape name`. `escape` is injective (it has a left
  inverse) and never produces two adjacent underscores, so the separator is
  the unique split point and `decode` recovers exactly the package path and
  declaration name. Together with the reserved-sequence rule (user
  identifiers never contain `__`) this is the capture-freedom argument for
  whole-program compilation of many packages into one C translation unit.
* **Compile order** (§5): Kahn's algorithm places every package after all of
  its imports; when it gets stuck, every remaining package imports a
  remaining package — the set contains a cycle.
* **Visibility and sealing** (§6): `alias.name` never resolves to a private
  declaration; a sealed import exposes only signature members; sealing never
  widens what an unsealed import resolves; opaque types are projectable only
  inside their declaring package.
* **Version selection** (§4.2): the selected version of a module is the least
  version satisfying every requirement.

The Go functions are maintained as line-for-line transliterations of the
definitions below; `modules/modules_test.go` exercises the same laws
(including a randomized injectivity witness). Characters are modeled as code
points (`Nat`) exactly as Go iterates runes. -/

namespace Mangle

/-- ASCII letters and digits pass through escaping unchanged. -/
def isAlnum (c : Nat) : Bool :=
  (48 ≤ c && c ≤ 57) || (65 ≤ c && c ≤ 90) || (97 ≤ c && c ≤ 122)

/-- Lowercase hexadecimal digit of a value below 16 (`%06x`). -/
def hexChar (d : Nat) : Nat := if d < 10 then 48 + d else 87 + d

/-- Value of a lowercase hexadecimal digit character. -/
def hexVal (c : Nat) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c - 48)
  else if 97 ≤ c ∧ c ≤ 102 then some (c - 87)
  else none

theorem hexVal_hexChar (d : Nat) (h : d < 16) : hexVal (hexChar d) = some d := by
  unfold hexVal hexChar
  by_cases hd : d < 10
  · rw [if_pos hd, if_pos (by omega)]
    simp only [Option.some.injEq]
    omega
  · rw [if_neg hd, if_neg (by omega), if_pos (by omega)]
    simp only [Option.some.injEq]
    omega

theorem hexChar_ne_underscore (d : Nat) (h : d < 16) : hexChar d ≠ 95 := by
  unfold hexChar
  by_cases hd : d < 10 <;> simp [hd] <;> omega

/-- The six fixed-width hex digits of a code point (`fmt.Fprintf("_x%06x")`). -/
def hex6 (n : Nat) : List Nat :=
  [hexChar (n / 1048576 % 16), hexChar (n / 65536 % 16), hexChar (n / 4096 % 16),
   hexChar (n / 256 % 16), hexChar (n / 16 % 16), hexChar (n % 16)]

/-- Decoding six hex digits. -/
def unhex6 (a b c d e f : Nat) : Option Nat :=
  match hexVal a, hexVal b, hexVal c, hexVal d, hexVal e, hexVal f with
  | some a, some b, some c, some d, some e, some f =>
      some (a * 1048576 + b * 65536 + c * 4096 + d * 256 + e * 16 + f)
  | _, _, _, _, _, _ => none

/-- Code points fit in six hex digits: the largest Unicode scalar is far below
    `16^6`, and Go's `rune` iteration never yields more. -/
def MaxCodePoint : Nat := 16777216

theorem unhex6_hex6 (n : Nat) (h : n < MaxCodePoint) :
    unhex6 (hexChar (n / 1048576 % 16)) (hexChar (n / 65536 % 16)) (hexChar (n / 4096 % 16))
      (hexChar (n / 256 % 16)) (hexChar (n / 16 % 16)) (hexChar (n % 16)) = some n := by
  unfold unhex6
  rw [hexVal_hexChar _ (Nat.mod_lt _ (by decide)), hexVal_hexChar _ (Nat.mod_lt _ (by decide)),
    hexVal_hexChar _ (Nat.mod_lt _ (by decide)), hexVal_hexChar _ (Nat.mod_lt _ (by decide)),
    hexVal_hexChar _ (Nat.mod_lt _ (by decide)), hexVal_hexChar _ (Nat.mod_lt _ (by decide))]
  simp only [Option.some.injEq]
  unfold MaxCodePoint at h
  omega

/-- Transliteration of `modules.Escape` for one code point. `95` is `_`,
    `47` is `/`, `46` is `.`, `45` is `-`; `117 115 100 104 120` spell
    `u s d h x`. -/
def escapeChar (c : Nat) : List Nat :=
  if isAlnum c then [c]
  else if c = 95 then [95, 117]
  else if c = 47 then [95, 115]
  else if c = 46 then [95, 100]
  else if c = 45 then [95, 104]
  else 95 :: 120 :: hex6 c

/-- Transliteration of `modules.Escape`. -/
def escape : List Nat → List Nat
  | [] => []
  | c :: rest => escapeChar c ++ escape rest

/-- Transliteration of `modules.Unescape`. -/
def unescape : List Nat → Option (List Nat)
  | [] => some []
  | c :: rest =>
    if c = 95 then
      match rest with
      | [] => none
      | k :: rest' =>
        if k = 117 then (unescape rest').map (95 :: ·)
        else if k = 115 then (unescape rest').map (47 :: ·)
        else if k = 100 then (unescape rest').map (46 :: ·)
        else if k = 104 then (unescape rest').map (45 :: ·)
        else if k = 120 then
          match rest' with
          | a :: b :: c' :: d :: e :: f :: rest'' =>
            match unhex6 a b c' d e f with
            | some n => (unescape rest'').map (n :: ·)
            | none => none
          | _ => none
        else none
    else if isAlnum c then (unescape rest).map (c :: ·)
    else none

/-- Every source code point is a valid rune. -/
def Runes (s : List Nat) : Prop := ∀ c ∈ s, c < MaxCodePoint

theorem alnum_ne_underscore (c : Nat) (h : isAlnum c = true) : c ≠ 95 := by
  intro hc; subst hc; simp [isAlnum] at h

theorem unescape_escapeChar (c : Nat) (rest : List Nat) (hc : c < MaxCodePoint)
    (ih : unescape (escape rest) = some rest) :
    unescape (escapeChar c ++ escape rest) = some (c :: rest) := by
  by_cases ha : isAlnum c = true
  · have he : escapeChar c = [c] := by simp [escapeChar, ha]
    rw [he, List.singleton_append, unescape.eq_def]
    simp [ha, alnum_ne_underscore c ha, ih]
  · by_cases h95 : c = 95
    · subst h95
      have he : escapeChar 95 = [95, 117] := by simp [escapeChar, ha]
      rw [he, List.cons_append, List.singleton_append, unescape.eq_def]
      simp [ih]
    · by_cases h47 : c = 47
      · subst h47
        have he : escapeChar 47 = [95, 115] := by simp [escapeChar, ha]
        rw [he, List.cons_append, List.singleton_append, unescape.eq_def]
        simp [ih]
      · by_cases h46 : c = 46
        · subst h46
          have he : escapeChar 46 = [95, 100] := by simp [escapeChar, ha]
          rw [he, List.cons_append, List.singleton_append, unescape.eq_def]
          simp [ih]
        · by_cases h45 : c = 45
          · subst h45
            have he : escapeChar 45 = [95, 104] := by simp [escapeChar, ha]
            rw [he, List.cons_append, List.singleton_append, unescape.eq_def]
            simp [ih]
          · have he : escapeChar c = 95 :: 120 :: hex6 c := by
              simp [escapeChar, ha, h95, h47, h46, h45]
            rw [he, hex6]
            simp only [List.cons_append, List.nil_append]
            rw [unescape.eq_def]
            simp [unhex6_hex6 c hc, ih]

/-- **Escaping is invertible**: `unescape` is a left inverse of `escape`
    on rune sequences, so `escape` is injective. -/
theorem unescape_escape (s : List Nat) (hs : Runes s) : unescape (escape s) = some s := by
  induction s with
  | nil => rfl
  | cons c rest ih =>
    have hc : c < MaxCodePoint := hs c (List.mem_cons_self ..)
    have hrest : Runes rest := fun d hd => hs d (List.mem_cons_of_mem _ hd)
    show unescape (escapeChar c ++ escape rest) = some (c :: rest)
    exact unescape_escapeChar c rest hc (ih hrest)

theorem escape_injective (s t : List Nat) (hs : Runes s) (ht : Runes t)
    (h : escape s = escape t) : s = t := by
  have := unescape_escape s hs
  rw [h, unescape_escape t ht] at this
  exact (Option.some.inj this).symm

/-- A sequence never places two underscores side by side. -/
def NoDouble : List Nat → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => ¬ (a = 95 ∧ b = 95) ∧ NoDouble (b :: rest)

/-- The last code point of a sequence is not an underscore. -/
def LastNe95 : List Nat → Prop
  | [] => True
  | [a] => a ≠ 95
  | _ :: rest => LastNe95 rest

theorem noDouble_append (l r : List Nat) (hl : NoDouble l) (hlast : LastNe95 l) (hr : NoDouble r) :
    NoDouble (l ++ r) := by
  induction l with
  | nil => simpa using hr
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases r with
      | nil => trivial
      | cons b r' =>
        simp only [LastNe95] at hlast
        simp only [List.singleton_append, NoDouble]
        exact ⟨fun h => hlast h.1, hr⟩
    | cons b rest' =>
      simp only [NoDouble] at hl
      simp only [LastNe95] at hlast
      simp only [List.cons_append, NoDouble]
      exact ⟨hl.1, ih hl.2 hlast⟩

theorem escapeChar_noDouble (c : Nat) (h : c < MaxCodePoint) : NoDouble (escapeChar c) := by
  unfold escapeChar
  by_cases ha : isAlnum c = true
  · simp [ha, NoDouble]
  · by_cases h95 : c = 95
    · subst h95; simp [ha, NoDouble]
    · by_cases h47 : c = 47
      · subst h47; simp [ha, NoDouble]
      · by_cases h46 : c = 46
        · subst h46; simp [ha, NoDouble]
        · by_cases h45 : c = 45
          · subst h45; simp [ha, NoDouble]
          · simp only [ha, h95, h47, h46, h45, Bool.false_eq_true, if_false, hex6, NoDouble, Bool.false_eq_true]
            refine ⟨by decide, ?_⟩
            refine ⟨fun h => hexChar_ne_underscore _ (Nat.mod_lt _ (by decide)) h.2, ?_⟩
            refine ⟨fun h => hexChar_ne_underscore _ (Nat.mod_lt _ (by decide)) h.2, ?_⟩
            refine ⟨fun h => hexChar_ne_underscore _ (Nat.mod_lt _ (by decide)) h.2, ?_⟩
            refine ⟨fun h => hexChar_ne_underscore _ (Nat.mod_lt _ (by decide)) h.2, ?_⟩
            refine ⟨fun h => hexChar_ne_underscore _ (Nat.mod_lt _ (by decide)) h.2, ?_⟩
            exact ⟨fun h => hexChar_ne_underscore _ (Nat.mod_lt _ (by decide)) h.2, trivial⟩

theorem escapeChar_lastNe95 (c : Nat) (h : c < MaxCodePoint) : LastNe95 (escapeChar c) := by
  unfold escapeChar
  by_cases ha : isAlnum c = true
  · simp [ha, LastNe95, alnum_ne_underscore c ha]
  · by_cases h95 : c = 95
    · subst h95; simp [ha, LastNe95]
    · by_cases h47 : c = 47
      · subst h47; simp [ha, LastNe95]
      · by_cases h46 : c = 46
        · subst h46; simp [ha, LastNe95]
        · by_cases h45 : c = 45
          · subst h45; simp [ha, LastNe95]
          · simp only [ha, h95, h47, h46, h45, Bool.false_eq_true, if_false, hex6, LastNe95, Bool.false_eq_true]
            exact hexChar_ne_underscore _ (Nat.mod_lt _ (by decide))

theorem lastNe95_append (l r : List Nat) (hr : LastNe95 r) (hl : LastNe95 l) (hne : r ≠ []) :
    LastNe95 (l ++ r) := by
  induction l with
  | nil => simpa using hr
  | cons a rest ih =>
    cases rest with
    | nil =>
      cases r with
      | nil => exact absurd rfl hne
      | cons b r' => simpa [LastNe95] using hr
    | cons b rest' =>
      simp only [LastNe95] at hl
      simpa [LastNe95] using ih hl

theorem escapeChar_ne_nil (c : Nat) : escapeChar c ≠ [] := by
  unfold escapeChar
  by_cases ha : isAlnum c = true
  · simp [ha]
  · by_cases h95 : c = 95
    · subst h95; simp [ha]
    · by_cases h47 : c = 47
      · subst h47; simp [ha]
      · by_cases h46 : c = 46
        · subst h46; simp [ha]
        · by_cases h45 : c = 45
          · subst h45; simp [ha]
          · simp [ha, h95, h47, h46, h45]

theorem escape_lastNe95 (s : List Nat) (hs : Runes s) : LastNe95 (escape s) := by
  induction s with
  | nil => trivial
  | cons c rest ih =>
    have hc : c < MaxCodePoint := hs c (List.mem_cons_self ..)
    have hrest : Runes rest := fun d hd => hs d (List.mem_cons_of_mem _ hd)
    cases rest with
    | nil => simpa [escape] using escapeChar_lastNe95 c hc
    | cons d rest' =>
      have hne : escape (d :: rest') ≠ [] := by
        simp only [escape]
        intro h
        exact escapeChar_ne_nil d (List.append_eq_nil_iff.mp h).1
      exact lastNe95_append _ _ (ih hrest) (escapeChar_lastNe95 c hc) hne

/-- **Escaped text has no adjacent underscores**, so the separator `__` can
    only occur where `mangle` writes it. -/
theorem escape_noDouble (s : List Nat) (hs : Runes s) : NoDouble (escape s) := by
  induction s with
  | nil => trivial
  | cons c rest ih =>
    have hc : c < MaxCodePoint := hs c (List.mem_cons_self ..)
    have hrest : Runes rest := fun d hd => hs d (List.mem_cons_of_mem _ hd)
    exact noDouble_append _ _ (escapeChar_noDouble c hc) (escapeChar_lastNe95 c hc) (ih hrest)

/-- Transliteration of `modules.Mangle`. -/
def mangle (path name : List Nat) : List Nat := escape path ++ 95 :: 95 :: escape name

/-- Split at the first occurrence of `__` (transliteration of the
    `strings.Index(internal, Separator)` step of `modules.Demangle`). -/
def splitDouble : List Nat → Option (List Nat × List Nat)
  | [] => none
  | [_] => none
  | a :: b :: rest =>
    if a = 95 ∧ b = 95 then some ([], rest)
    else (splitDouble (b :: rest)).map (fun p => (a :: p.1, p.2))

theorem splitDouble_append (l r : List Nat) (hl : NoDouble l) (hlast : LastNe95 l) :
    splitDouble (l ++ 95 :: 95 :: r) = some (l, r) := by
  induction l with
  | nil => simp [splitDouble]
  | cons a rest ih =>
    cases rest with
    | nil =>
      simp only [LastNe95] at hlast
      simp [splitDouble, hlast]
    | cons b rest' =>
      simp only [NoDouble] at hl
      simp only [LastNe95] at hlast
      have hrec := ih hl.2 hlast
      simp only [List.cons_append] at hrec
      simp [splitDouble, hl.1, hrec]

/-- Transliteration of `modules.Demangle`: split, unescape both halves. -/
def decode (internal : List Nat) : Option (List Nat × List Nat) :=
  match splitDouble internal with
  | none => none
  | some (l, r) =>
    match unescape l, unescape r with
    | some path, some name => some (path, name)
    | _, _ => none

/-- **Mangled names decode exactly**: the internal name of a declaration
    determines its package path and source name. Two distinct
    (path, name) pairs therefore never share an internal name — no cross-package
    collision in the single C translation unit. -/
theorem decode_mangle (path name : List Nat) (hp : Runes path) (hn : Runes name) :
    decode (mangle path name) = some (path, name) := by
  unfold decode mangle
  rw [splitDouble_append _ _ (escape_noDouble path hp) (escape_lastNe95 path hp)]
  simp [unescape_escape path hp, unescape_escape name hn]

theorem mangle_injective (p₁ n₁ p₂ n₂ : List Nat) (hp₁ : Runes p₁) (hn₁ : Runes n₁)
    (hp₂ : Runes p₂) (hn₂ : Runes n₂) (h : mangle p₁ n₁ = mangle p₂ n₂) :
    p₁ = p₂ ∧ n₁ = n₂ := by
  have h₁ := decode_mangle p₁ n₁ hp₁ hn₁
  rw [h, decode_mangle p₂ n₂ hp₂ hn₂] at h₁
  have := Option.some.inj h₁
  exact ⟨(Prod.mk.inj this).1.symm, (Prod.mk.inj this).2.symm⟩

/-- An identifier is reserved when it contains `__`; user code may never
    spell one (`OAK-M0108`). -/
def Reserved (ident : List Nat) : Prop := splitDouble ident ≠ none

/-- **Capture freedom**: every internal name is reserved, so an identifier
    user code may spell is never an internal name. -/
theorem mangle_reserved (path name : List Nat) (hp : Runes path) : Reserved (mangle path name) := by
  unfold Reserved mangle
  rw [splitDouble_append _ _ (escape_noDouble path hp) (escape_lastNe95 path hp)]
  simp

end Mangle

namespace Order

/-- Packages are numbered; `imports n` lists the packages `n` imports. -/
structure Graph where
  imports : Nat → List Nat

/-- All imports of a package are already placed. -/
def allPlaced (g : Graph) (placed : List Nat) (node : Nat) : Bool :=
  (g.imports node).all (· ∈ placed)

/-- One scan over the remaining packages, in order, placing every package
    whose imports are placed — including those placed earlier in the same
    scan (transliteration of the inner loop of `modules.Order`). Returns the
    placed list, the newly appended order, and the still-remaining list. -/
def pass (g : Graph) : List Nat → List Nat → List Nat × List Nat × List Nat
  | placed, [] => (placed, [], [])
  | placed, node :: rest =>
    if allPlaced g placed node then
      let r := pass g (placed ++ [node]) rest
      (r.1, node :: r.2.1, r.2.2)
    else
      let r := pass g placed rest
      (r.1, r.2.1, node :: r.2.2)

/-- The outer loop, with fuel bounding the number of scans (a scan that places
    nothing terminates the loop; `order` passes one more than the package
    count, which `kahn_stuck` shows is always enough). -/
def kahn (g : Graph) : Nat → List Nat → List Nat → List Nat × List Nat
  | 0, _, remaining => ([], remaining)
  | fuel + 1, placed, remaining =>
    if remaining = [] then ([], [])
    else
      let r := pass g placed remaining
      if r.2.1 = [] then ([], r.2.2)
      else
        let k := kahn g fuel r.1 r.2.2
        (r.2.1 ++ k.1, k.2)

/-- Transliteration of `modules.Order`: the compile order and the stuck set. -/
def order (g : Graph) (nodes : List Nat) : List Nat × List Nat :=
  kahn g (nodes.length + 1) [] nodes

/-- An order is valid relative to already-placed packages when each package's
    imports lie in the placed prefix before it. -/
def OrderedFrom (g : Graph) : List Nat → List Nat → Prop
  | _, [] => True
  | placed, node :: rest =>
    (∀ d ∈ g.imports node, d ∈ placed) ∧ OrderedFrom g (placed ++ [node]) rest

theorem orderedFrom_append (g : Graph) (placed a b : List Nat) :
    OrderedFrom g placed (a ++ b) ↔ OrderedFrom g placed a ∧ OrderedFrom g (placed ++ a) b := by
  induction a generalizing placed with
  | nil => simp [OrderedFrom]
  | cons n rest ih =>
    simp only [List.cons_append, OrderedFrom, ih, List.append_assoc, List.singleton_append]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩

theorem allPlaced_iff (g : Graph) (placed : List Nat) (node : Nat) :
    allPlaced g placed node = true ↔ ∀ d ∈ g.imports node, d ∈ placed := by
  simp [allPlaced, List.all_eq_true]

theorem not_allPlaced (g : Graph) (placed : List Nat) (node : Nat)
    (h : ¬ allPlaced g placed node = true) : ∃ d ∈ g.imports node, d ∉ placed := by
  apply Classical.byContradiction
  intro hno
  apply h
  rw [allPlaced_iff]
  intro d hd
  apply Classical.byContradiction
  intro hnot
  exact hno ⟨d, hd, hnot⟩

theorem pass_placed (g : Graph) (placed remaining : List Nat) :
    (pass g placed remaining).1 = placed ++ (pass g placed remaining).2.1 := by
  induction remaining generalizing placed with
  | nil => simp [pass]
  | cons node rest ih =>
    by_cases h : allPlaced g placed node = true
    · simp only [pass, h, if_true]
      rw [ih (placed ++ [node])]
      simp
    · simp only [pass, h, Bool.false_eq_true, if_false]
      exact ih placed

theorem pass_ordered (g : Graph) (placed remaining : List Nat) :
    OrderedFrom g placed (pass g placed remaining).2.1 := by
  induction remaining generalizing placed with
  | nil => simp [pass, OrderedFrom]
  | cons node rest ih =>
    by_cases h : allPlaced g placed node = true
    · simp only [pass, h, if_true, OrderedFrom]
      exact ⟨(allPlaced_iff g placed node).mp h, ih (placed ++ [node])⟩
    · simp only [pass, h, Bool.false_eq_true, if_false]
      exact ih placed

/-- Every package is either placed or remaining (as a multiset). -/
theorem pass_perm (g : Graph) (placed remaining : List Nat) :
    ((pass g placed remaining).2.1 ++ (pass g placed remaining).2.2).Perm remaining := by
  induction remaining generalizing placed with
  | nil => simp [pass]
  | cons node rest ih =>
    by_cases h : allPlaced g placed node = true
    · simp only [pass, h, if_true, List.cons_append]
      exact (ih (placed ++ [node])).cons node
    · simp only [pass, h, Bool.false_eq_true, if_false]
      exact List.perm_middle.trans ((ih placed).cons node)

theorem pass_length_lt (g : Graph) (placed remaining : List Nat)
    (h : (pass g placed remaining).2.1 ≠ []) :
    (pass g placed remaining).2.2.length < remaining.length := by
  have hlen := (pass_perm g placed remaining).length_eq
  rw [List.length_append] at hlen
  have : 0 < (pass g placed remaining).2.1.length := List.length_pos_iff.mpr h
  omega

/-- Whatever a scan that placed nothing leaves behind has an import outside
    the placed set. -/
theorem pass_stuck_unplaced (g : Graph) (placed remaining : List Nat)
    (hnone : (pass g placed remaining).2.1 = []) :
    ∀ node ∈ (pass g placed remaining).2.2, ∃ d ∈ g.imports node, d ∉ placed := by
  induction remaining generalizing placed with
  | nil => simp [pass]
  | cons node rest ih =>
    by_cases h : allPlaced g placed node = true
    · simp only [pass, h, if_true] at hnone
      exact absurd hnone (List.cons_ne_nil _ _)
    · simp only [pass, h, Bool.false_eq_true, if_false] at hnone ⊢
      intro n hn
      simp only [List.mem_cons] at hn
      rcases hn with rfl | hn
      · exact not_allPlaced g placed n h
      · exact ih placed hnone n hn

/-- **Every placed package follows its imports.** -/
theorem kahn_ordered (g : Graph) (fuel : Nat) (placed remaining : List Nat) :
    OrderedFrom g placed (kahn g fuel placed remaining).1 := by
  induction fuel generalizing placed remaining with
  | zero => simp [kahn, OrderedFrom]
  | succ fuel ih =>
    by_cases hrem : remaining = []
    · simp [kahn, hrem, OrderedFrom]
    · by_cases hord : (pass g placed remaining).2.1 = []
      · simp [kahn, hrem, hord, OrderedFrom]
      · simp only [kahn, hrem, hord, Bool.false_eq_true, if_false]
        rw [orderedFrom_append]
        refine ⟨pass_ordered g placed remaining, ?_⟩
        rw [← pass_placed]
        exact ih _ _

theorem order_ordered (g : Graph) (nodes : List Nat) : OrderedFrom g [] (order g nodes).1 :=
  kahn_ordered g _ [] nodes

theorem kahn_perm (g : Graph) (fuel : Nat) (placed remaining : List Nat) :
    ((kahn g fuel placed remaining).1 ++ (kahn g fuel placed remaining).2).Perm remaining := by
  induction fuel generalizing placed remaining with
  | zero => simp [kahn]
  | succ fuel ih =>
    by_cases hrem : remaining = []
    · simp [kahn, hrem]
    · by_cases hord : (pass g placed remaining).2.1 = []
      · simp only [kahn, hrem, hord, Bool.false_eq_true, if_false, if_true, List.nil_append]
        have := pass_perm g placed remaining
        rw [hord] at this
        simpa using this
      · simp only [kahn, hrem, hord, Bool.false_eq_true, if_false, List.append_assoc]
        exact ((ih _ _).append_left _).trans (pass_perm g placed remaining)

/-- **Every package is placed or stuck**: the order and the stuck set
    together are a permutation of the input. -/
theorem order_perm (g : Graph) (nodes : List Nat) :
    ((order g nodes).1 ++ (order g nodes).2).Perm nodes :=
  kahn_perm g _ [] nodes

/-- With enough fuel, a stuck package has an import that was never placed. -/
theorem kahn_stuck (g : Graph) (fuel : Nat) (placed remaining : List Nat)
    (hfuel : remaining.length < fuel) :
    ∀ node ∈ (kahn g fuel placed remaining).2,
      ∃ d ∈ g.imports node, d ∉ placed ++ (kahn g fuel placed remaining).1 := by
  induction fuel generalizing placed remaining with
  | zero => exact absurd hfuel (Nat.not_lt_zero _)
  | succ fuel ih =>
    by_cases hrem : remaining = []
    · simp [kahn, hrem]
    · by_cases hord : (pass g placed remaining).2.1 = []
      · simp only [kahn, hrem, hord, Bool.false_eq_true, if_false, if_true, List.append_nil]
        exact pass_stuck_unplaced g placed remaining hord
      · simp only [kahn, hrem, hord, Bool.false_eq_true, if_false]
        rw [pass_placed g placed remaining]
        intro n hn
        have hlt := pass_length_lt g placed remaining hord
        obtain ⟨d, hd, hnot⟩ := ih (placed ++ (pass g placed remaining).2.1)
          (pass g placed remaining).2.2 (by omega) n hn
        exact ⟨d, hd, by simpa [List.append_assoc] using hnot⟩

/-- **A stuck package imports a stuck package.** When the graph is closed
    (every import names a package of the graph), the stuck set has no
    dependency-free member: it carries an import cycle, which the compiler
    reports (`OAK-M0104`). -/
theorem order_stuck_cycle (g : Graph) (nodes : List Nat)
    (hclosed : ∀ n ∈ nodes, ∀ d ∈ g.imports n, d ∈ nodes) :
    ∀ n ∈ (order g nodes).2, ∃ d ∈ g.imports n, d ∈ (order g nodes).2 := by
  intro n hn
  obtain ⟨d, hd, hnot⟩ := kahn_stuck g (nodes.length + 1) [] nodes (Nat.lt_succ_self _) n hn
  have hperm := order_perm g nodes
  have hnodes : n ∈ nodes := hperm.mem_iff.mp (List.mem_append_right _ hn)
  have hdnodes : d ∈ nodes := hclosed n hnodes d hd
  have hd' : d ∈ (order g nodes).1 ++ (order g nodes).2 := hperm.mem_iff.mpr hdnodes
  simp only [List.nil_append] at hnot
  rcases List.mem_append.mp hd' with h | h
  · exact absurd h hnot
  · exact ⟨d, hd, h⟩

end Order

namespace Visibility

/-- What a package records about one package-level declaration. -/
structure Member where
  exported : Bool
  isOpaque : Bool
  kind : Nat
  deriving DecidableEq, Repr

/-- A sealed import's signature: the member names it exposes. -/
structure Signature where
  members : List Nat
  deriving Repr

/-- Result of resolving `alias.name` (transliteration of `modules.Outcome`). -/
inductive Outcome where
  | resolved (m : Member)
  | noSuchMember
  | notExported
  | notInSignature
  deriving DecidableEq, Repr

/-- Existence, then visibility. -/
def lookupMember (exports : Nat → Option Member) (name : Nat) : Outcome :=
  match exports name with
  | none => .noSuchMember
  | some m => if m.exported then .resolved m else .notExported

/-- Transliteration of `modules.Lookup`: sealing narrows first. -/
def lookup (exports : Nat → Option Member) (sig : Option Signature) (name : Nat) : Outcome :=
  match sig with
  | some s => if name ∈ s.members then lookupMember exports name else .notInSignature
  | none => lookupMember exports name

theorem lookupMember_resolved (exports : Nat → Option Member) (name : Nat) (m : Member)
    (h : lookupMember exports name = .resolved m) : exports name = some m ∧ m.exported = true := by
  unfold lookupMember at h
  split at h
  · cases h
  · rename_i m' hm
    by_cases he : m'.exported = true
    · simp [he] at h
      subst h
      exact ⟨hm, he⟩
    · simp [he] at h

/-- **Encapsulation**: a qualified reference never resolves to a private
    declaration, sealed or not. -/
theorem lookup_never_private (exports : Nat → Option Member) (sig : Option Signature) (name : Nat)
    (m : Member) (h : lookup exports sig name = .resolved m) : m.exported = true := by
  unfold lookup at h
  cases sig with
  | none => exact (lookupMember_resolved exports name m h).2
  | some s =>
    by_cases hs : name ∈ s.members
    · simp only [hs, if_true] at h
      exact (lookupMember_resolved exports name m h).2
    · simp [hs] at h

/-- **Sealing hides**: through a sealed import only signature members resolve. -/
theorem lookup_sealed_subset (exports : Nat → Option Member) (s : Signature) (name : Nat)
    (m : Member) (h : lookup exports (some s) name = .resolved m) : name ∈ s.members := by
  unfold lookup at h
  by_cases hs : name ∈ s.members
  · exact hs
  · simp [hs] at h

/-- **Sealing never widens**: whatever resolves through a sealed import
    resolves to the same declaration through the unsealed import. -/
theorem lookup_sealed_narrows (exports : Nat → Option Member) (s : Signature) (name : Nat)
    (m : Member) (h : lookup exports (some s) name = .resolved m) :
    lookup exports none name = .resolved m := by
  unfold lookup at h ⊢
  by_cases hs : name ∈ s.members
  · simpa [hs] using h
  · simp [hs] at h

/-- **Exported members are reachable**: an unsealed import resolves every
    exported declaration (completeness of the rule). -/
theorem lookup_exported_resolves (exports : Nat → Option Member) (name : Nat) (m : Member)
    (hm : exports name = some m) (he : m.exported = true) :
    lookup exports none name = .resolved m := by
  simp [lookup, lookupMember, hm, he]

/-- Transliteration of `modules.ProjectionAllowed`. -/
def projectionAllowed (declaring user : Nat) (isOpaque : Bool) : Bool :=
  !isOpaque || declaring == user

/-- **Opaque types are projectable only at home**: literals, field access,
    and variant matching on an opaque type are admitted exactly inside the
    declaring package. -/
theorem opaque_projection_local (declaring user : Nat) :
    projectionAllowed declaring user true = true ↔ declaring = user := by
  simp [projectionAllowed]

/-- Transparent types are projectable everywhere. -/
theorem transparent_projection_free (declaring user : Nat) :
    projectionAllowed declaring user false = true := by
  simp [projectionAllowed]

end Visibility

namespace Versions

/-- A SemVer version (`packageapi.Version`). -/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  deriving DecidableEq, Repr

/-- Lexicographic order on versions. -/
def LE (a b : Version) : Prop :=
  a.major < b.major ∨ (a.major = b.major ∧
    (a.minor < b.minor ∨ (a.minor = b.minor ∧ a.patch ≤ b.patch)))

/-- Transliteration of `modules.Less`. -/
def less (a b : Version) : Bool :=
  if a.major ≠ b.major then decide (a.major < b.major)
  else if a.minor ≠ b.minor then decide (a.minor < b.minor)
  else decide (a.patch < b.patch)

theorem less_true (a b : Version) (h : less a b = true) : LE a b := by
  unfold less at h
  unfold LE
  by_cases h1 : a.major ≠ b.major
  · simp [h1] at h; omega
  · by_cases h2 : a.minor ≠ b.minor
    · simp [h1, h2] at h; omega
    · simp [h1, h2] at h; omega

theorem less_false (a b : Version) (h : less a b = false) : LE b a := by
  unfold less at h
  unfold LE
  by_cases h1 : a.major ≠ b.major
  · simp [h1] at h; omega
  · by_cases h2 : a.minor ≠ b.minor
    · simp [h1, h2] at h; omega
    · simp [h1, h2] at h; omega

theorem LE_refl (a : Version) : LE a a := by unfold LE; omega

theorem LE_trans (a b c : Version) (h₁ : LE a b) (h₂ : LE b c) : LE a c := by
  unfold LE at *; omega

/-- One step of the Go fold: keep the larger of the running maximum and the
    next requirement. -/
def step (current next : Version) : Version := if less current next then next else current

/-- Transliteration of the per-module fold of `modules.Select`. -/
def select : List Version → Option Version
  | [] => none
  | v :: rest => some (rest.foldl step v)

theorem step_ge_left (current next : Version) : LE current (step current next) := by
  unfold step
  by_cases h : less current next = true
  · simp [h]; exact less_true _ _ h
  · simp [h]; exact LE_refl _

theorem step_ge_right (current next : Version) : LE next (step current next) := by
  unfold step
  by_cases h : less current next = true
  · simp [h]; exact LE_refl _
  · simp [h]
    exact less_false _ _ (by simpa using h)

theorem step_le (current next bound : Version) (h₁ : LE current bound) (h₂ : LE next bound) :
    LE (step current next) bound := by
  unfold step
  by_cases h : less current next = true
  · simp [h]; exact h₂
  · simp [h]; exact h₁

theorem foldl_ge_acc (acc : Version) (rest : List Version) : LE acc (rest.foldl step acc) := by
  induction rest generalizing acc with
  | nil => exact LE_refl _
  | cons v rest ih =>
    simp only [List.foldl_cons]
    exact LE_trans _ _ _ (step_ge_left acc v) (ih (step acc v))

theorem foldl_ge_mem (acc : Version) (rest : List Version) :
    ∀ v ∈ rest, LE v (rest.foldl step acc) := by
  induction rest generalizing acc with
  | nil => simp
  | cons w rest ih =>
    intro v hv
    simp only [List.foldl_cons]
    simp only [List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact LE_trans _ _ _ (step_ge_right acc v) (foldl_ge_acc _ _)
    · exact ih (step acc w) v hv

theorem foldl_le_bound (acc : Version) (rest : List Version) (bound : Version)
    (hacc : LE acc bound) (hrest : ∀ v ∈ rest, LE v bound) : LE (rest.foldl step acc) bound := by
  induction rest generalizing acc with
  | nil => exact hacc
  | cons w rest ih =>
    simp only [List.foldl_cons]
    exact ih (step acc w) (step_le _ _ _ hacc (hrest w (List.mem_cons_self ..)))
      (fun v hv => hrest v (List.mem_cons_of_mem _ hv))

/-- **Selection satisfies every requirement.** -/
theorem select_satisfies (reqs : List Version) (s : Version) (h : select reqs = some s) :
    ∀ v ∈ reqs, LE v s := by
  cases reqs with
  | nil => cases h
  | cons v rest =>
    simp only [select, Option.some.injEq] at h
    subst h
    intro w hw
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact foldl_ge_acc _ _
    · exact foldl_ge_mem _ _ w hw

/-- **Selection is minimal**: any version satisfying every requirement is at
    least the selected one — minimal version selection, reproducible from the
    manifests alone. -/
theorem select_minimal (reqs : List Version) (s bound : Version) (h : select reqs = some s)
    (hbound : ∀ v ∈ reqs, LE v bound) : LE s bound := by
  cases reqs with
  | nil => cases h
  | cons v rest =>
    simp only [select, Option.some.injEq] at h
    subst h
    exact foldl_le_bound v rest bound (hbound v (List.mem_cons_self ..))
      (fun w hw => hbound w (List.mem_cons_of_mem _ hw))

/-- Selection never invents a version: the result is one of the requirements. -/
theorem foldl_mem (acc : Version) (rest : List Version) :
    rest.foldl step acc = acc ∨ rest.foldl step acc ∈ rest := by
  induction rest generalizing acc with
  | nil => exact Or.inl rfl
  | cons w rest ih =>
    simp only [List.foldl_cons]
    rcases ih (step acc w) with h | h
    · rw [h]
      unfold step
      by_cases hl : less acc w = true
      · simp [hl]
      · simp [hl]
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem select_mem (reqs : List Version) (s : Version) (h : select reqs = some s) : s ∈ reqs := by
  cases reqs with
  | nil => cases h
  | cons v rest =>
    simp only [select, Option.some.injEq] at h
    subst h
    rcases foldl_mem v rest with h | h
    · rw [h]; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ h

end Versions

/-! ## Open imports (docs/spec/83-modules.md section 3.2)

`open import(path)` binds every exported member of a package unqualified.
The rule that keeps it honest: a name an open would bind may not already be
bound by anything else — a declaration, an alias, a selective import, or
another open. `openBind` is the loader's check: given the names already
bound and the package's exports, it either rejects (some export is bound)
or yields exactly the exports, none of them previously bound. Meaning
therefore never depends on precedence, and a dependency that later adds an
export can only make an open fail, never silently change what a name
denotes. -/
namespace OpenImports

/-- Bind an open import's exports against the names already bound: `none`
on any collision, otherwise the exports. -/
def openBind (bound : Nat → Bool) (exports : List Nat) : Option (List Nat) :=
  if exports.any bound then none else some exports

/-- An open is rejected exactly when one of its exports is already bound. -/
theorem openBind_none_iff (bound : Nat → Bool) (exports : List Nat) :
    openBind bound exports = none ↔ ∃ n ∈ exports, bound n = true := by
  unfold openBind
  split <;> simp_all [List.any_eq_true]

/-- An accepted open binds exactly the exports, and none of them was bound
before: no precedence, no shadowing. -/
theorem openBind_some (bound : Nat → Bool) (exports names : List Nat)
    (h : openBind bound exports = some names) :
    names = exports ∧ ∀ n ∈ names, bound n = false := by
  unfold openBind at h
  split at h
  · cases h
  · rename_i hany
    simp only [Option.some.injEq] at h
    subst h
    refine ⟨rfl, fun n hn => ?_⟩
    simp only [List.any_eq_true, not_exists, not_and] at hany
    have := hany n hn
    simpa using this

/-- Growth is monotone toward rejection: adding exports never turns a
rejected open into an accepted one. -/
theorem openBind_none_mono (bound : Nat → Bool) (exports more : List Nat)
    (h : openBind bound exports = none) : openBind bound (exports ++ more) = none := by
  rw [openBind_none_iff] at *
  obtain ⟨n, hn, hb⟩ := h
  exact ⟨n, List.mem_append_left _ hn, hb⟩

end OpenImports

/-! ## Nested modules (docs/spec/83-modules.md section 3.5)

A nested module `module name { ... }` inside package `parent` is the package
`parent/name`. Packages belong to the module whose path is the longest
prefix of theirs (`moduleOfPath`); a nested module's path extends its
parent's by one segment, so unless some module's path is exactly that
extension — which the loader rejects as a directory conflict — the nested
module belongs to the same module as its parent, and so inherits its
discipline profile and version. -/
namespace NestedPaths

/-- Import paths as segment lists. -/
abbrev Path := List Nat

/-- The longest module path that is a prefix of `p`, if any. -/
def moduleOf (mods : List Path) (p : Path) : Option Path :=
  (mods.filter (fun m => m.isPrefixOf p)).foldl
    (fun best m => match best with
      | none => some m
      | some b => if b.length < m.length then some m else some b) none

/-- A module path that is a prefix of the nested path is a prefix of the
parent, or is the nested path itself. -/
theorem prefix_of_nested (m parent : Path) (name : Nat)
    (h : m.isPrefixOf (parent ++ [name]) = true) :
    m.isPrefixOf parent = true ∨ m = parent ++ [name] := by
  rw [List.isPrefixOf_iff_prefix] at *
  obtain ⟨rest, hrest⟩ := h
  rcases rest with _ | ⟨r, rest⟩
  · right; simpa using hrest
  · left
    have hlen : m.length + (rest.length + 1) = parent.length + 1 := by
      have := congrArg List.length hrest
      simp at this
      omega
    have : m.length ≤ parent.length := by omega
    have hpre : m <+: parent ++ [name] := ⟨r :: rest, hrest⟩
    exact List.prefix_of_prefix_length_le hpre (List.prefix_append parent [name]) this

/-- The candidate module set of a nested path is the parent's unless some
module is exactly the nested path (the directory conflict the loader
rejects). -/
theorem candidates_nested (mods : List Path) (parent : Path) (name : Nat)
    (h : parent ++ [name] ∉ mods) :
    mods.filter (fun m => m.isPrefixOf (parent ++ [name])) =
      mods.filter (fun m => m.isPrefixOf parent) := by
  apply List.filter_congr
  intro m hm
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hp
    rcases prefix_of_nested m parent name hp with hp' | heq
    · exact hp'
    · exact absurd (heq ▸ hm) h
  · intro hp
    rw [List.isPrefixOf_iff_prefix] at *
    exact hp.trans (List.prefix_append parent [name])

/-- **Nested modules keep their parent's module.** -/
theorem moduleOf_nested (mods : List Path) (parent : Path) (name : Nat)
    (h : parent ++ [name] ∉ mods) :
    moduleOf mods (parent ++ [name]) = moduleOf mods parent := by
  unfold moduleOf
  rw [candidates_nested mods parent name h]

end NestedPaths

end Oak.Modules
