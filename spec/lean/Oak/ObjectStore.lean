/-!
# Oak.ObjectStore — generation preconditions

`docs/spec/121-object-store.md` fixes one port two realizations satisfy:
keyed objects, each with a generation drawn from one monotone counter, and
the conditional mutations put-if-generation and delete-if-generation. This
module states the §3 contract over a minimal model — a store is the
generation of every key (0 for absent) and the next generation to hand
out — and proves what both `objsim` and `objfs` are held to:

* `putIf_admits`: a put applies exactly when its precondition holds
  against the key's current generation (`any`, `absent`, or exact);
* `putIf_exclusive`: two puts naming the same exact generation of one key
  cannot both apply — after the first, the second is refused;
* `gen_monotone`: an applied mutation hands out a generation above every
  generation the store handed out before, and changes no other key;
* `delete_then_put_above`: a key deleted and re-created receives a
  generation above the one deleted;
* `refusal_reports_current`: a refused mutation reports the key's current
  generation, so a caller resynchronizes from the completion alone.

Values are left out: the contract is about who may write, not what.
-/

namespace Oak.ObjectStore

/-- A store: each key's generation (`0` is absent) and the next generation
to hand out; `next` is above every generation ever handed out. -/
structure Store where
  gen : Nat → Nat
  next : Nat
  bound : ∀ k, gen k < next

/-- The precondition of a mutation. -/
inductive Pre
  | any
  | exact (g : Nat)   -- `exact 0` is `obj_absent`

/-- Whether a precondition holds against a current generation. -/
def Pre.admits : Pre → Nat → Bool
  | .any, _ => true
  | .exact g, current => decide (g = current)

/-- The completion of a mutation: applied with the new generation, or
refused with the current one. -/
inductive Outcome
  | applied (generation : Nat)
  | refused (current : Nat)

/-- put-if-generation: when the precondition holds, the key takes the next
generation and the counter advances. -/
def putIf (s : Store) (k : Nat) (p : Pre) : Store × Outcome :=
  if p.admits (s.gen k) then
    (⟨fun j => if j = k then s.next else s.gen j, s.next + 1, by
      intro j
      by_cases h : j = k
      · simp [h]
      · simp [h]; exact Nat.lt_succ_of_lt (s.bound j)⟩, .applied s.next)
  else (s, .refused (s.gen k))

/-- delete-if-generation: when the precondition holds, the key becomes
absent; the counter does not move back. -/
def deleteIf (s : Store) (k : Nat) (p : Pre) : Store × Outcome :=
  if p.admits (s.gen k) then
    (⟨fun j => if j = k then 0 else s.gen j, s.next, by
      intro j
      by_cases h : j = k
      · simp [h]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) (s.bound k)
      · simp [h]; exact s.bound j⟩, .applied (s.gen k))
  else (s, .refused (s.gen k))

theorem putIf_admits (s : Store) (k : Nat) (p : Pre) :
    (∃ g, (putIf s k p).2 = .applied g) ↔ p.admits (s.gen k) = true := by
  unfold putIf
  split <;> simp_all

/-- The winner of a compare-and-set is alone: after a put admitted "if g"
on key k, a second put "if g" on k is refused. -/
theorem putIf_exclusive (s : Store) (k g : Nat) (h : (putIf s k (.exact g)).2 = .applied s.next) :
    ∃ current, (putIf (putIf s k (.exact g)).1 k (.exact g)).2 = .refused current ∧ current ≠ g := by
  have hg : g = s.gen k := by
    unfold putIf at h
    split at h
    · rename_i hp
      simpa [Pre.admits] using hp
    · simp at h
  subst hg
  have hne : s.gen k ≠ s.next := Nat.ne_of_lt (s.bound k)
  refine ⟨s.next, ?_, Ne.symm hne⟩
  unfold putIf
  simp [Pre.admits, hne]

/-- An applied put hands out a generation above every earlier one and
touches no other key. -/
theorem gen_monotone (s : Store) (k : Nat) (p : Pre) (g : Nat)
    (h : (putIf s k p).2 = .applied g) :
    (∀ j, s.gen j < g) ∧ (putIf s k p).1.gen k = g ∧ ∀ j, j ≠ k → (putIf s k p).1.gen j = s.gen j := by
  unfold putIf at *
  split at h
  · rename_i hp
    have hg : g = s.next := by simpa using h.symm
    subst hg
    simp only [hp, ite_true]
    exact ⟨s.bound, by first | trivial | exact if_pos rfl | simp, fun j hj => by first | exact if_neg hj | simp [hj]⟩
  · simp at h

/-- A deleted key is absent, and a put that follows receives a generation
above the deleted one. -/
theorem delete_then_put_above (s : Store) (k : Nat) (g : Nat)
    (hd : (deleteIf s k .any).2 = .applied g) :
    (deleteIf s k .any).1.gen k = 0 ∧
      ∀ g', (putIf (deleteIf s k .any).1 k .any).2 = .applied g' → g < g' := by
  unfold deleteIf at *
  simp [Pre.admits] at hd
  have hg : g = s.gen k := by simpa using hd.symm
  subst hg
  refine ⟨by simp [Pre.admits], ?_⟩
  intro g' h'
  unfold putIf at h'
  simp [Pre.admits] at h'
  subst h'
  exact s.bound k

/-- A refusal reports the key's current generation. -/
theorem refusal_reports_current (s : Store) (k : Nat) (p : Pre) (current : Nat)
    (h : (putIf s k p).2 = .refused current) : current = s.gen k := by
  unfold putIf at h
  split at h <;> simp_all

end Oak.ObjectStore
