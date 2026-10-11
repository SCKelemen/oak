import Oak.Typestate

/-!
# Capability algebra: the pure authority component

This is a mathematical model of *permission*, not a kernel handle allocator.
An authority is a predicate over requests, so scopes, actions, time and
context can be represented without a baked-in object taxonomy.

Meet is intersection. Join is an upper bound in the mathematics, **not** an
API that mints a runtime capability. Attenuation is constrained by the order.
Transfer, duplication, revocation, budgets and physical enforcement require
stateful protocols and are intentionally not conflated with this algebra.
-/

namespace Oak.CapabilityAlgebra

universe u
variable {Request : Type u}

structure Authority (Request : Type u) where
  permits : Request → Prop

def le (a b : Authority Request) : Prop :=
  ∀ r, a.permits r → b.permits r

def meet (a b : Authority Request) : Authority Request :=
  ⟨fun r => a.permits r ∧ b.permits r⟩

def join (a b : Authority Request) : Authority Request :=
  ⟨fun r => a.permits r ∨ b.permits r⟩

def bottom : Authority Request := ⟨fun _ => False⟩

theorem le_refl (a : Authority Request) : le a a := by
  intro r h
  exact h

theorem le_trans (a b c : Authority Request)
    (hab : le a b) (hbc : le b c) : le a c := by
  intro r h
  exact hbc r (hab r h)

theorem meet_left (a b : Authority Request) : le (meet a b) a := by
  intro r h
  exact h.1

theorem meet_right (a b : Authority Request) : le (meet a b) b := by
  intro r h
  exact h.2

theorem meet_greatest (a b c : Authority Request)
    (hca : le c a) (hcb : le c b) : le c (meet a b) := by
  intro r h
  exact ⟨hca r h, hcb r h⟩

theorem join_left (a b : Authority Request) : le a (join a b) := by
  intro r h
  exact Or.inl h

theorem join_right (a b : Authority Request) : le b (join a b) := by
  intro r h
  exact Or.inr h

theorem join_least (a b c : Authority Request)
    (hac : le a c) (hbc : le b c) : le (join a b) c := by
  intro r h
  cases h with
  | inl ha => exact hac r ha
  | inr hb => exact hbc r hb

theorem bottom_le (a : Authority Request) : le bottom a := by
  intro r h
  exact False.elim h

/-- A delegation certificate is an explicit proof of non-amplification.
It does not assert that the OS has installed a child handle. -/
structure Attenuation (parent child : Authority Request) : Prop where
  subset : le child parent

theorem attenuate_meet (parent requested : Authority Request) :
    Attenuation parent (meet parent requested) :=
  ⟨meet_left parent requested⟩

theorem attenuation_compose {a b c : Authority Request}
    (ab : Attenuation a b) (bc : Attenuation b c) :
    Attenuation a c :=
  ⟨le_trans c b a bc.subset ab.subset⟩

/-- A valid delegated child never permits a request denied by its parent. -/
theorem no_amplification {parent child : Authority Request}
    (h : Attenuation parent child) (r : Request)
    (allowed : child.permits r) : parent.permits r :=
  h.subset r allowed

end Oak.CapabilityAlgebra
