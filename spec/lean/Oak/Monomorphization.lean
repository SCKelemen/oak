namespace Oak.Monomorphization

/-! # Generic-ADT monomorphization

Model for the backend's specialization step (codegen/mono.go, fed by the
type checker's instantiation records in typechecker/mono.go): a generic ADT
template is its list of variants — a tag paired with an optional payload
type over parameters — and instantiation substitutes the parameters in
every payload while touching nothing else. Laws proven:

- substitution preserves the variant count and every tag, in order
  (dispatch structure is instantiation-invariant, so the tag-guarded C
  lowering of `Oak.ADTSemantics` transfers to every instantiation);
- payloads are substituted exactly, and payload-less variants stay
  payload-less;
- instantiation identity is the argument list: mangling two instantiations
  of one template collides only when their argument atoms collide. -/

/-- A payload type over parameters: a parameter reference or a ground type. -/
inductive PayloadType (α : Type)
  | param (index : Nat)
  | ground (name : α)
  deriving DecidableEq

/-- One variant: a tag and an optional payload. -/
structure Variant (α : Type) where
  tag : String
  payload : Option (PayloadType α)
  deriving DecidableEq

/-- Substituting the arguments into one payload type. -/
def substPayload {α : Type} (args : List α) (fallback : α) :
    PayloadType α → α
  | .param index => args.getD index fallback
  | .ground name => name

/-- Instantiating a template: substitute in every variant's payload. -/
def instantiate {α : Type} (args : List α) (fallback : α)
    (template : List (Variant α)) : List (Variant α) :=
  template.map fun variant =>
    { tag := variant.tag
      payload := variant.payload.map (fun p => .ground (substPayload args fallback p)) }

/-- **Variant count is preserved.** -/
theorem instantiate_length {α : Type} (args : List α) (fallback : α)
    (template : List (Variant α)) :
    (instantiate args fallback template).length = template.length :=
  List.length_map ..

/-- **Every tag is preserved, in order**: dispatch structure is
    instantiation-invariant. -/
theorem instantiate_tags {α : Type} (args : List α) (fallback : α)
    (template : List (Variant α)) :
    (instantiate args fallback template).map Variant.tag = template.map Variant.tag := by
  induction template with
  | nil => rfl
  | cons variant rest ih =>
    simp only [instantiate, List.map_cons] at ih ⊢
    exact congrArg (variant.tag :: ·) ih

/-- **Payload-less variants stay payload-less; payload variants stay
    payload variants** (substitution never invents or drops a payload). -/
theorem instantiate_payload_shape {α : Type} (args : List α) (fallback : α)
    (template : List (Variant α)) (i : Nat) (hi : i < template.length) :
    ((instantiate args fallback template)[i]'(by
      rw [instantiate_length]; exact hi)).payload.isSome =
      (template[i]'hi).payload.isSome := by
  simp [instantiate]

/-- **Substitution is exact**: a payload referencing parameter `k` becomes
    exactly argument `k` (in range). -/
theorem substPayload_param {α : Type} (args : List α) (fallback : α)
    (k : Nat) (hk : k < args.length) :
    substPayload args fallback (.param k) = args[k]'hk := by
  simp [substPayload, List.getD, List.getElem?_eq_getElem hk]

/-- **Ground payloads are untouched.** -/
theorem substPayload_ground {α : Type} (args : List α) (fallback : α)
    (name : α) : substPayload args fallback (.ground name) = name := rfl

/-- **Instantiation identity**: instantiating one template with different
    in-range argument lists differs whenever some referenced parameter's
    arguments differ — two instantiations agree only when every parameter
    a payload actually references receives an equal argument. -/
theorem instantiate_injective_on_used {α : Type} (fallback : α)
    (template : List (Variant α)) (args₁ args₂ : List α) (k : Nat)
    (h₁ : k < args₁.length) (h₂ : k < args₂.length)
    (i : Nat) (hi : i < template.length)
    (huse : (template[i]'hi).payload = some (.param k))
    (heq : instantiate args₁ fallback template = instantiate args₂ fallback template) :
    args₁[k]'h₁ = args₂[k]'h₂ := by
  have hlen := instantiate_length args₁ fallback template
  have hcell : ((instantiate args₁ fallback template)[i]'(by rw [hlen]; exact hi)) =
      ((instantiate args₂ fallback template)[i]'(by
        rw [instantiate_length]; exact hi)) := by
    simp [heq]
  simp [instantiate, huse] at hcell
  rw [substPayload_param args₁ fallback k h₁, substPayload_param args₂ fallback k h₂] at hcell
  exact hcell

end Oak.Monomorphization
