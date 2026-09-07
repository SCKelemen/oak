/-!
# Typed field tags: schema conformance

`docs/spec/40-records.md` §12: a field tag names a declared schema and
provides values for schema fields. The checker
(`typechecker.checkFieldTags`) is maintained as the transliteration of
`checkTags` below: an entry is accepted exactly when its field exists in
the schema with the matching type atom — so a typo'd namespace or field,
or a mistyped value, can never become silent metadata (the Go failure
mode this design exists to close).

Fields and atoms are abstract identities (names and types after
interning); the theorems are checker soundness and completeness against
the conformance relation.
-/

namespace Oak.FieldTags

structure SchemaField where
  identity : Nat
  atom : Nat
  deriving DecidableEq, Repr

structure TagEntry where
  identity : Nat
  atom : Nat
  deriving DecidableEq, Repr

/-- First schema field with the given identity, if any. -/
def lookup : List SchemaField -> Nat -> Option Nat
  | [], _ => none
  | field :: rest, identity =>
      if field.identity = identity then some field.atom else lookup rest identity

/-- One entry is checked: its field exists in the schema and the value's
    type atom matches the declared one. -/
def entryChecked (schema : List SchemaField) (entry : TagEntry) : Bool :=
  lookup schema entry.identity == some entry.atom

/-- The transliterated checker: every provided entry checks. Omitted
    schema fields are simply absent — tags are sparse. -/
def checkTags (schema : List SchemaField) : List TagEntry -> Bool
  | [] => true
  | entry :: rest => entryChecked schema entry && checkTags schema rest

/-- Conformance: every provided entry resolves in the schema to exactly
    its own type atom. -/
def Conformant (schema : List SchemaField) (entries : List TagEntry) : Prop :=
  ∀ entry, entry ∈ entries -> lookup schema entry.identity = some entry.atom

theorem entryChecked_iff (schema : List SchemaField) (entry : TagEntry) :
    entryChecked schema entry = true ↔
      lookup schema entry.identity = some entry.atom := by
  simp [entryChecked]

/-- Soundness: an accepted tag list is conformant — nothing unchecked
    survives. -/
theorem checkTags_sound (schema : List SchemaField) (entries : List TagEntry)
    (h : checkTags schema entries = true) : Conformant schema entries := by
  induction entries with
  | nil => intro entry hmem; cases hmem
  | cons entry rest ih =>
      have hsplit : entryChecked schema entry = true ∧ checkTags schema rest = true := by
        simpa [checkTags, Bool.and_eq_true] using h
      intro candidate hmem
      cases hmem with
      | head => exact (entryChecked_iff schema entry).mp hsplit.1
      | tail _ hrest => exact ih hsplit.2 candidate hrest

/-- Completeness: every conformant tag list is accepted — the checker
    rejects nothing legal. -/
theorem checkTags_complete (schema : List SchemaField) (entries : List TagEntry)
    (h : Conformant schema entries) : checkTags schema entries = true := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have hhead : lookup schema entry.identity = some entry.atom :=
        h entry (by simp)
      have hrest : Conformant schema rest := by
        intro candidate hmem
        exact h candidate (by simp [hmem])
      simp [checkTags, Bool.and_eq_true]
      exact ⟨(entryChecked_iff schema entry).mpr hhead, ih hrest⟩

/-- An unknown field (no schema entry with that identity) is always
    rejected: the anti-Go theorem — metadata can never be silently
    dropped. -/
theorem unknown_field_rejected (schema : List SchemaField) (entry : TagEntry)
    (h : lookup schema entry.identity = none) :
    entryChecked schema entry = false := by
  simp [entryChecked, h]

end Oak.FieldTags
