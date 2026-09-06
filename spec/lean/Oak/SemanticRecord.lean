namespace Oak.SemanticRecord

/-! # Semantic record construction

Model for `docs/spec/40-records.md`: a semantic record is an ordered list of
uniquely named fields — source order is authoritative declaration metadata,
representation is decided elsewhere. `addField` is maintained as the
transliteration of `ast.RecordLiteral.AddField`: it rejects duplicate names
and appends, so construction preserves the uniqueness invariant and the
declaration order of existing fields, and lookup returns exactly the member
associated with a name. -/

/-- An ordered semantic record: fields in declaration order. -/
structure Record (τ : Type) where
  fields : List (String × τ)

def names {τ : Type} (r : Record τ) : List String :=
  r.fields.map (·.1)

/-- The uniqueness invariant: no field name is declared twice. -/
def Unique {τ : Type} (r : Record τ) : Prop :=
  (names r).Nodup

/-- Transliteration of `ast.RecordLiteral.AddField`: reject a duplicate name,
    otherwise append in declaration order. -/
def addField {τ : Type} (r : Record τ) (name : String) (value : τ) :
    Option (Record τ) :=
  if r.fields.any (fun field => field.1 == name) then none
  else some ⟨r.fields ++ [(name, value)]⟩

/-- Field lookup: the first (hence, under `Unique`, the only) member with the
    name. -/
def lookup {τ : Type} (r : Record τ) (name : String) : Option τ :=
  (r.fields.find? (fun field => field.1 == name)).map (·.2)

theorem mem_names {τ : Type} {r : Record τ} {name : String} :
    name ∈ names r ↔ ∃ v, (name, v) ∈ r.fields := by
  simp only [names, List.mem_map]
  constructor
  · rintro ⟨⟨n, v⟩, hmem, rfl⟩
    exact ⟨v, hmem⟩
  · rintro ⟨v, hmem⟩
    exact ⟨(name, v), hmem, rfl⟩

/-- **Duplicate fields are rejected** (spec target: incompatible duplicate
    fields are rejected — at the semantic layer any redeclaration is). -/
theorem addField_rejects_duplicate {τ : Type} {r : Record τ} {name : String}
    {value : τ} (h : name ∈ names r) : addField r name value = none := by
  obtain ⟨v, hmem⟩ := mem_names.mp h
  have hany : r.fields.any (fun field => field.1 == name) = true :=
    List.any_eq_true.mpr ⟨(name, v), hmem, by simp⟩
  simp [addField, hany]

/-- **Construction preserves declaration order**: adding a field appends it,
    leaving every existing field's position untouched. -/
theorem addField_preserves_order {τ : Type} {r r' : Record τ} {name : String}
    {value : τ} (h : addField r name value = some r') :
    r'.fields = r.fields ++ [(name, value)] := by
  unfold addField at h
  by_cases hany : r.fields.any (fun field => field.1 == name)
  · simp [hany] at h
  · simp [hany] at h
    rw [← h]

theorem addField_fresh {τ : Type} {r r' : Record τ} {name : String}
    {value : τ} (h : addField r name value = some r') : name ∉ names r := by
  intro hmem
  rw [addField_rejects_duplicate hmem] at h
  simp at h

theorem nodup_append_singleton {l : List String} {a : String}
    (h : l.Nodup) (hmem : a ∉ l) : (l ++ [a]).Nodup := by
  induction l with
  | nil => simp
  | cons b rest ih =>
    rw [List.cons_append]
    rw [List.nodup_cons] at h
    rw [List.nodup_cons]
    obtain ⟨hb, hrest⟩ := h
    refine ⟨?_, ih hrest fun hx => hmem (by simp [hx])⟩
    simp only [List.mem_append, List.mem_singleton]
    rintro (hx | rfl)
    · exact hb hx
    · exact hmem (by simp)

/-- **Construction preserves uniqueness**: an accepted field was not already
    declared, so the invariant survives. -/
theorem addField_preserves_unique {τ : Type} {r r' : Record τ} {name : String}
    {value : τ} (hunique : Unique r) (h : addField r name value = some r') :
    Unique r' := by
  have horder := addField_preserves_order h
  have hfresh := addField_fresh h
  unfold Unique
  have : names r' = names r ++ [name] := by
    unfold names
    rw [horder]
    simp
  rw [this]
  exact nodup_append_singleton hunique hfresh

theorem find?_append_right_of_none {τ : Type} {l : List (String × τ)}
    {p : String × τ → Bool} {suffix : List (String × τ)}
    (h : ∀ f ∈ l, p f = false) :
    (l ++ suffix).find? p = suffix.find? p := by
  induction l with
  | nil => simp
  | cons f rest ih =>
    have hf : ¬ p f := by simp [h f (by simp)]
    rw [List.cons_append, List.find?_cons_of_neg hf]
    exact ih fun g hg => h g (by simp [hg])

theorem find?_append_left_of_some {τ : Type} {l suffix : List (String × τ)}
    {p : String × τ → Bool} {a : String × τ}
    (h : l.find? p = some a) : (l ++ suffix).find? p = some a := by
  induction l with
  | nil => simp at h
  | cons f rest ih =>
    by_cases hf : p f
    · rw [List.find?_cons_of_pos hf] at h
      rw [List.cons_append, List.find?_cons_of_pos hf]
      exact h
    · rw [List.find?_cons_of_neg hf] at h
      rw [List.cons_append, List.find?_cons_of_neg hf]
      exact ih h

/-- **Lookup returns the member associated with the name** (spec target):
    the freshly added field is found with its value. -/
theorem lookup_added {τ : Type} {r r' : Record τ} {name : String} {value : τ}
    (h : addField r name value = some r') : lookup r' name = some value := by
  have horder := addField_preserves_order h
  have hfresh := addField_fresh h
  have hnone : ∀ f ∈ r.fields, (f.1 == name) = false := by
    intro f hf
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro heq
    exact hfresh (mem_names.mpr ⟨f.2, by rw [← heq]; exact hf⟩)
  unfold lookup
  rw [horder, find?_append_right_of_none hnone]
  simp [List.find?]

/-- **Existing members are undisturbed**: lookup of a previously declared
    field returns the same member after construction. -/
theorem lookup_preserved {τ : Type} {r r' : Record τ} {name added : String}
    {value w : τ} (h : addField r added value = some r')
    (hfound : lookup r name = some w) : lookup r' name = some w := by
  have horder := addField_preserves_order h
  unfold lookup at hfound ⊢
  rw [horder]
  obtain ⟨found, hfind, hsnd⟩ := Option.map_eq_some_iff.mp hfound
  rw [find?_append_left_of_some hfind]
  simp [hsnd]

end Oak.SemanticRecord
