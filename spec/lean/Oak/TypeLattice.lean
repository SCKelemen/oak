namespace Oak.TypeLattice

universe u

abbrev Ty (α : Type u) := α → Prop

def Subtype {α : Type u} (a b : Ty α) : Prop :=
  ∀ x, a x → b x

infix:50 " ≤ₜ " => Subtype

def bottom {α : Type u} : Ty α := fun _ => False

def top {α : Type u} : Ty α := fun _ => True

def join {α : Type u} (a b : Ty α) : Ty α := fun x => a x ∨ b x

def meet {α : Type u} (a b : Ty α) : Ty α := fun x => a x ∧ b x

theorem subtype_refl {α : Type u} (a : Ty α) : a ≤ₜ a := by
  intro x hx
  exact hx

theorem subtype_trans {α : Type u} {a b c : Ty α}
    (hab : a ≤ₜ b) (hbc : b ≤ₜ c) : a ≤ₜ c := by
  intro x hx
  exact hbc x (hab x hx)

theorem bottom_le {α : Type u} (a : Ty α) : bottom ≤ₜ a := by
  intro x hx
  exact False.elim hx

theorem le_top {α : Type u} (a : Ty α) : a ≤ₜ top := by
  intro _ _
  trivial

theorem le_join_left {α : Type u} (a b : Ty α) : a ≤ₜ join a b := by
  intro x hx
  exact Or.inl hx

theorem le_join_right {α : Type u} (a b : Ty α) : b ≤ₜ join a b := by
  intro x hx
  exact Or.inr hx

theorem join_least {α : Type u} {a b c : Ty α}
    (hac : a ≤ₜ c) (hbc : b ≤ₜ c) : join a b ≤ₜ c := by
  intro x hx
  cases hx with
  | inl ha => exact hac x ha
  | inr hb => exact hbc x hb

theorem meet_le_left {α : Type u} (a b : Ty α) : meet a b ≤ₜ a := by
  intro x hx
  exact hx.1

theorem meet_le_right {α : Type u} (a b : Ty α) : meet a b ≤ₜ b := by
  intro x hx
  exact hx.2

theorem meet_greatest {α : Type u} {a b c : Ty α}
    (hca : c ≤ₜ a) (hcb : c ≤ₜ b) : c ≤ₜ meet a b := by
  intro x hx
  exact ⟨hca x hx, hcb x hx⟩

theorem join_comm {α : Type u} (a b : Ty α) : join a b = join b a := by
  funext x
  apply propext
  constructor
  · intro h
    cases h with
    | inl ha => exact Or.inr ha
    | inr hb => exact Or.inl hb
  · intro h
    cases h with
    | inl hb => exact Or.inr hb
    | inr ha => exact Or.inl ha

theorem meet_comm {α : Type u} (a b : Ty α) : meet a b = meet b a := by
  funext x
  apply propext
  constructor
  · intro h
    exact ⟨h.2, h.1⟩
  · intro h
    exact ⟨h.2, h.1⟩

theorem join_assoc {α : Type u} (a b c : Ty α) :
    join a (join b c) = join (join a b) c := by
  funext x
  apply propext
  constructor
  · intro h
    cases h with
    | inl ha => exact Or.inl (Or.inl ha)
    | inr hbc =>
      cases hbc with
      | inl hb => exact Or.inl (Or.inr hb)
      | inr hc => exact Or.inr hc
  · intro h
    cases h with
    | inl hab =>
      cases hab with
      | inl ha => exact Or.inl ha
      | inr hb => exact Or.inr (Or.inl hb)
    | inr hc => exact Or.inr (Or.inr hc)

theorem meet_assoc {α : Type u} (a b c : Ty α) :
    meet a (meet b c) = meet (meet a b) c := by
  funext x
  apply propext
  constructor
  · intro h
    exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  · intro h
    exact ⟨h.1.1, ⟨h.1.2, h.2⟩⟩

theorem join_idem {α : Type u} (a : Ty α) : join a a = a := by
  funext x
  apply propext
  constructor
  · intro h
    cases h with
    | inl ha => exact ha
    | inr ha => exact ha
  · intro ha
    exact Or.inl ha

theorem meet_idem {α : Type u} (a : Ty α) : meet a a = a := by
  funext x
  apply propext
  constructor
  · intro h
    exact h.1
  · intro ha
    exact ⟨ha, ha⟩

theorem join_bottom {α : Type u} (a : Ty α) : join a bottom = a := by
  funext x
  apply propext
  constructor
  · intro h
    cases h with
    | inl ha => exact ha
    | inr hf => exact False.elim hf
  · intro ha
    exact Or.inl ha

theorem meet_top {α : Type u} (a : Ty α) : meet a top = a := by
  funext x
  apply propext
  constructor
  · intro h
    exact h.1
  · intro ha
    exact ⟨ha, trivial⟩

theorem join_top {α : Type u} (a : Ty α) : join a top = top := by
  funext x
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact Or.inr trivial

theorem meet_bottom {α : Type u} (a : Ty α) : meet a bottom = bottom := by
  funext x
  apply propext
  constructor
  · intro h
    exact h.2
  · intro hf
    exact False.elim hf

theorem join_absorption {α : Type u} (a b : Ty α) :
    join a (meet a b) = a := by
  funext x
  apply propext
  constructor
  · intro h
    cases h with
    | inl ha => exact ha
    | inr hab => exact hab.1
  · intro ha
    exact Or.inl ha

theorem meet_absorption {α : Type u} (a b : Ty α) :
    meet a (join a b) = a := by
  funext x
  apply propext
  constructor
  · intro h
    exact h.1
  · intro ha
    exact ⟨ha, Or.inl ha⟩

end Oak.TypeLattice
