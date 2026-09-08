import CertifiedStream

set_option autoImplicit false
namespace OakVerification.InitialDecoder
open Ranges

-- Successful traversal determines every lookup, including indices past the end.
theorem mapM_lookup {α β : Type} (f : α → Option β) (xs : List α) (ys : List β)
    (decoded : xs.mapM f = some ys) :
    ∀ slot : Nat, (xs[slot]?).bind f = ys[slot]? := by
  induction xs generalizing ys with
  | nil =>
    simp at decoded
    subst ys
    simp
  | cons x xs ih =>
    cases head : f x with
    | none => simp [head] at decoded
    | some y =>
      cases tail : xs.mapM f with
      | none => simp [head, tail] at decoded
      | some rest =>
        have same : y :: rest = ys := by simpa [head, tail] using decoded
        subst ys
        intro slot
        cases slot with
        | zero => simpa using head
        | succ n => simpa using ih rest tail n

-- Extract the actual initial traversal from a successful complete decoder run.
theorem clauses_decoded (raw : Layout) (d : Decoded)
    (decoded : decodeLayout raw = some d) :
    (raw.starts.zip raw.sizes).mapM (fun r => readClause raw.pool r.1 r.2) = some d.clauses := by
  unfold decodeLayout at decoded
  split at decoded
  · contradiction
  · split at decoded
    · contradiction
    · cases clauses : (raw.starts.zip raw.sizes).mapM (fun r => readClause raw.pool r.1 r.2) with
      | none => simp [clauses] at decoded
      | some cs =>
        cases cmds : raw.commands.mapM (decodeCommand raw.pool raw.refs) with
        | none => simp [clauses, cmds] at decoded
        | some instructions =>
          have same : (⟨cs, instructions⟩ : Decoded) = d := by simpa [clauses, cmds] using decoded
          subst d
          rfl

theorem origin_refines (raw : Layout) (d : Decoded)
    (decoded : decodeLayout raw = some d) :
    CertifiedStream.origin raw = initialDatabase d.clauses := by
  exact LiveTable.initialize_refines raw.pool (raw.starts.zip raw.sizes) d.clauses
    (mapM_lookup _ _ _ (clauses_decoded raw d decoded))

theorem decoded_sound (raw : Layout) (d : Decoded)
    (decoded : decodeLayout raw = some d) (accepted : CertifiedStream.check raw = true) :
    Unsatisfiable (initialDatabase d.clauses) := by
  rw [← origin_refines raw d decoded]
  exact CertifiedStream.check_sound raw accepted

-- This composition needs no caller-supplied representation equation.
def check (raw : Layout) : Bool :=
  match decodeLayout raw with
  | none => false
  | some _ => CertifiedStream.check raw

theorem check_sound (raw : Layout) (accepted : check raw = true) :
    ∃ d, decodeLayout raw = some d ∧ Unsatisfiable (initialDatabase d.clauses) := by
  cases decoded : decodeLayout raw with
  | none => simp [check, decoded] at accepted
  | some d =>
    exact ⟨d, rfl, decoded_sound raw d decoded (by simpa [check, decoded] using accepted)⟩

#print axioms mapM_lookup
#print axioms clauses_decoded
#print axioms origin_refines
#print axioms decoded_sound
#print axioms check
#print axioms check_sound
end OakVerification.InitialDecoder
