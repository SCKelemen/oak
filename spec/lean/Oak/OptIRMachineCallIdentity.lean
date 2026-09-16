/-!
# OptIR-to-machine call identity

This module specifies the small, fail-closed check that binds the direct calls
in a selected machine body to the call occurrences certified for its OptIR
control-flow graph.  A source occurrence is identified by a nonzero site ID
and an exact callee name.  Machine instruction order is deliberately
irrelevant: selection may reorder independent operations, but it may neither
drop nor add an occurrence, change its target, or duplicate its identity.

The model begins after concrete machine instructions have been classified as
non-calls, direct calls, or opaque/indirect calls.  Correct classification,
the construction and preservation of site tags, symbol resolution, call ABI
correctness, and machine instruction semantics are separate obligations.
-/

namespace Oak.OptIRMachineCallIdentity

/-- One direct call occurrence authorized by the checked OptIR projection. -/
structure Occurrence where
  site : Nat
  target : String
  deriving BEq, DecidableEq, Repr

/-- Equality-relevant classification of an emitted machine instruction. -/
inductive MachineForm where
  /-- A machine instruction which is not a call. -/
  | other (site : Option Nat := none)
  /-- A statically named direct call. -/
  | direct (site : Option Nat) (target : String)
  /-- An indirect, unresolved, or otherwise opaque call. -/
  | opaque (site : Option Nat := none)
  deriving BEq, DecidableEq, Repr

/-- Collect direct machine calls, rejecting every ambiguous tag shape.

Direct calls require a nonzero certified site.  Non-call instructions may not
carry a call-site tag, and opaque calls are never admitted, tagged or not. -/
def collect : List MachineForm → Option (List Occurrence)
  | [] => some []
  | .other none :: rest => collect rest
  | .other (some _) :: _ => none
  | .direct none _ :: _ => none
  | .direct (some 0) _ :: _ => none
  | .direct (some site) target :: rest =>
      match collect rest with
      | none => none
      | some calls => some (⟨site, target⟩ :: calls)
  | .opaque _ :: _ => none

/-- The expected certificate has unique site IDs and the emitted body contains
exactly the same call occurrences, modulo machine layout order. -/
def check (expected : List Occurrence) (machine : List MachineForm) : Bool :=
  decide (expected.map Occurrence.site).Nodup &&
    match collect machine with
    | none => false
    | some actual => decide (actual.Perm expected)

/-- Acceptance exposes both certificate-ID uniqueness and exact occurrence
multiset correspondence. -/
theorem check_sound {expected : List Occurrence} {machine : List MachineForm}
    (accepted : check expected machine = true) :
    (expected.map Occurrence.site).Nodup ∧
      ∃ actual, collect machine = some actual ∧ actual.Perm expected := by
  unfold check at accepted
  simp only [Bool.and_eq_true, decide_eq_true_eq] at accepted
  rcases accepted with ⟨unique, accepted⟩
  generalize hcollect : collect machine = collected at accepted
  cases collected with
  | none => simp at accepted
  | some actual =>
      simp only [decide_eq_true_eq] at accepted
      exact ⟨unique, actual, rfl, accepted⟩

/-- Any concrete list returned by `collect` after acceptance is a permutation
of the expected occurrences. -/
theorem check_actual_perm {expected : List Occurrence} {machine : List MachineForm}
    {actual : List Occurrence} (accepted : check expected machine = true)
    (collected : collect machine = some actual) :
    actual.Perm expected := by
  rcases check_sound accepted with ⟨_, witnessed, hwitnessed, perm⟩
  rw [collected] at hwitnessed
  cases hwitnessed
  exact perm

/-- No expected call occurrence is missing from an accepted machine body. -/
theorem check_no_missing {expected : List Occurrence} {machine : List MachineForm}
    {actual : List Occurrence} (accepted : check expected machine = true)
    (collected : collect machine = some actual) {occurrence : Occurrence}
    (member : occurrence ∈ expected) :
    occurrence ∈ actual := by
  exact (check_actual_perm accepted collected).mem_iff.mpr member

/-- No unexpected call occurrence is added to an accepted machine body. -/
theorem check_no_extra {expected : List Occurrence} {machine : List MachineForm}
    {actual : List Occurrence} (accepted : check expected machine = true)
    (collected : collect machine = some actual) {occurrence : Occurrence}
    (member : occurrence ∈ actual) :
    occurrence ∈ expected := by
  exact (check_actual_perm accepted collected).mem_iff.mp member

/-- An exact call occurrence has the same multiplicity before and after
machine selection. -/
theorem check_multiplicity {expected : List Occurrence} {machine : List MachineForm}
    {actual : List Occurrence} (accepted : check expected machine = true)
    (collected : collect machine = some actual) (occurrence : Occurrence) :
    actual.count occurrence = expected.count occurrence :=
  (check_actual_perm accepted collected).count_eq occurrence

/-- Unique site IDs make the target at a certified site unambiguous. -/
theorem occurrence_eq_of_site_eq_of_mem {occurrences : List Occurrence}
    (unique : (occurrences.map Occurrence.site).Nodup)
    {left right : Occurrence} (leftMember : left ∈ occurrences)
    (rightMember : right ∈ occurrences) (sameSite : left.site = right.site) :
    left = right := by
  induction occurrences with
  | nil => simp at leftMember
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftMember
      · rcases rightMember with rfl | rightMember
        · rfl
        · exfalso
          apply unique.1
          rw [sameSite]
          exact List.mem_map.mpr ⟨right, rightMember, rfl⟩
      · rcases rightMember with rfl | rightMember
        · exfalso
          apply unique.1
          rw [← sameSite]
          exact List.mem_map.mpr ⟨left, leftMember, rfl⟩
        · exact ih unique.2 leftMember rightMember

/-- If an accepted actual call and an expected call carry the same site ID,
their targets are equal (indeed, the complete occurrences are equal). -/
theorem check_target_at_site {expected : List Occurrence} {machine : List MachineForm}
    {actual : List Occurrence} (accepted : check expected machine = true)
    (collected : collect machine = some actual) {emitted certified : Occurrence}
    (emittedMember : emitted ∈ actual) (certifiedMember : certified ∈ expected)
    (sameSite : emitted.site = certified.site) :
    emitted.target = certified.target := by
  have expectedMember : emitted ∈ expected :=
    check_no_extra accepted collected emittedMember
  have unique := (check_sound accepted).1
  have equal : emitted = certified :=
    occurrence_eq_of_site_eq_of_mem unique expectedMember certifiedMember sameSite
  exact congrArg Occurrence.target equal

/-- Accepted emitted calls also have unique IDs, independently of their
machine layout order. -/
theorem check_actual_ids_unique {expected : List Occurrence}
    {machine : List MachineForm} {actual : List Occurrence}
    (accepted : check expected machine = true)
    (collected : collect machine = some actual) :
    (actual.map Occurrence.site).Nodup := by
  have perm := (check_actual_perm accepted collected).map Occurrence.site
  exact perm.symm.nodup (check_sound accepted).1

/-! ## Executable correspondence pins -/

def expectedExample : List Occurrence :=
  [⟨1, "alpha"⟩, ⟨2, "beta"⟩]

-- Reordering independent calls is accepted.
example : check expectedExample
    [.direct (some 2) "beta", .other, .direct (some 1) "alpha"] = true := by
  decide

-- Certificate IDs must be unique.
example : check [⟨1, "alpha"⟩, ⟨1, "alpha"⟩]
    [.direct (some 1) "alpha", .direct (some 1) "alpha"] = false := by
  decide

-- Missing, extra, retargeted, and duplicated machine occurrences reject.
example : check expectedExample [.direct (some 1) "alpha"] = false := by decide
example : check expectedExample
    [.direct (some 1) "alpha", .direct (some 2) "beta",
      .direct (some 3) "gamma"] = false := by decide
example : check expectedExample
    [.direct (some 1) "alpha", .direct (some 2) "gamma"] = false := by decide
example : check [⟨1, "alpha"⟩]
    [.direct (some 1) "alpha", .direct (some 1) "alpha"] = false := by decide

-- Every malformed tagging or call-classification shape rejects.
example : check [⟨1, "alpha"⟩] [.direct none "alpha"] = false := by decide
example : check [⟨1, "alpha"⟩] [.direct (some 0) "alpha"] = false := by decide
example : check [] [.other (some 1)] = false := by decide
example : check [] [.opaque] = false := by decide
example : check [] [.opaque (some 1)] = false := by decide

end Oak.OptIRMachineCallIdentity
