/-!
# OptIR call-summary certificates

This module gives the small semantic checker beneath OptIR's recursive
`NoModRef`/`Ref`/`Mod`/`ModRef` certificate graph.  It deliberately starts
after the concrete CFG has been projected to its active checked direct
accesses and calls.  A producer supplies nodes in child-before-parent order;
the checker accepts only unique names, exact child summaries, exact typed
per-region joins, a closed graph, and the requested root as the final node.

The model is structural.  SHA-256 fingerprints are cache/integrity identities,
not collision-free axioms here.  Correctness of CFG-to-active-projection,
source lowering, and the identity of a selected machine callee are separate
refinement seams.  Consequently the main theorem says exactly this: if the
small checker accepts an *exact active projection*, its root has an inductive
certificate whose summaries contain precisely the reachable read/write bits.
-/

namespace Oak.OptIRCallSummaryCertificate

/-! ## The effect lattice -/

inductive AccessKind where
  | read
  | write
  | readWrite
  deriving DecidableEq, Repr

def AccessKind.reads : AccessKind → Bool
  | .read | .readWrite => true
  | .write => false

def AccessKind.writes : AccessKind → Bool
  | .write | .readWrite => true
  | .read => false

/-- Absence is `NoModRef`; the three present elements are Ref, Mod, ModRef. -/
abbrev Effect := Option AccessKind

def Effect.reads : Effect → Bool
  | none => false
  | some kind => kind.reads

def Effect.writes : Effect → Bool
  | none => false
  | some kind => kind.writes

/-- Union of may-effects. -/
def Effect.join : Effect → Effect → Effect
  | none, right => right
  | left, none => left
  | some .read, some .read => some .read
  | some .write, some .write => some .write
  | _, _ => some .readWrite

def Effect.LE (left right : Effect) : Prop :=
  (left.reads = true → right.reads = true) ∧
  (left.writes = true → right.writes = true)

@[simp] theorem Effect.join_reads (left right : Effect) :
    (Effect.join left right).reads = (left.reads || right.reads) := by
  cases left with
  | none => rfl
  | some left =>
      cases right with
      | none => cases left <;> rfl
      | some right => cases left <;> cases right <;> rfl

@[simp] theorem Effect.join_writes (left right : Effect) :
    (Effect.join left right).writes = (left.writes || right.writes) := by
  cases left with
  | none => rfl
  | some left =>
      cases right with
      | none => cases left <;> rfl
      | some right => cases left <;> cases right <;> rfl

theorem Effect.bottom_le (effect : Effect) : Effect.LE none effect := by
  simp [Effect.LE, Effect.reads, Effect.writes]

theorem Effect.le_join_left (left right : Effect) :
    Effect.LE left (Effect.join left right) := by
  constructor <;> intro h <;> simp [h]

theorem Effect.le_join_right (left right : Effect) :
    Effect.LE right (Effect.join left right) := by
  constructor <;> intro h <;> simp [h]

/-- `join` is the least upper bound of the read/write bit order. -/
theorem Effect.join_least {left right upper : Effect}
    (hl : Effect.LE left upper) (hr : Effect.LE right upper) :
    Effect.LE (Effect.join left right) upper := by
  rcases hl with ⟨hlr, hlw⟩
  rcases hr with ⟨hrr, hrw⟩
  constructor
  · simp only [Effect.join_reads, Bool.or_eq_true]
    intro h
    cases h with
    | inl h => exact hlr h
    | inr h => exact hrr h
  · simp only [Effect.join_writes, Bool.or_eq_true]
    intro h
    cases h with
    | inl h => exact hlw h
    | inr h => exact hrw h

theorem Effect.join_commutative (left right : Effect) :
    Effect.join left right = Effect.join right left := by
  cases left with
  | none => cases right <;> rfl
  | some left =>
      cases right with
      | none => rfl
      | some right => cases left <;> cases right <;> rfl

theorem Effect.join_associative (a b c : Effect) :
    Effect.join (Effect.join a b) c = Effect.join a (Effect.join b c) := by
  cases a with
  | none => rfl
  | some a =>
      cases b with
      | none => rfl
      | some b =>
          cases c with
          | none => cases a <;> cases b <;> rfl
          | some c => cases a <;> cases b <;> cases c <;> rfl

theorem Effect.join_idempotent (effect : Effect) :
    Effect.join effect effect = effect := by
  cases effect with
  | none => rfl
  | some kind => cases kind <;> rfl

@[simp] theorem Effect.join_bottom_left (effect : Effect) :
    Effect.join none effect = effect := rfl

@[simp] theorem Effect.join_bottom_right (effect : Effect) :
    Effect.join effect none = effect := by
  cases effect <;> rfl

/-! ## Exact typed region summaries -/

structure Access where
  region : String
  kind : AccessKind
  valueType : String
  deriving DecidableEq, Repr

abbrev Summary := List Access

def SameCell (left right : Access) : Prop :=
  left.region = right.region ∧ left.valueType = right.valueType

def sameCell (left right : Access) : Bool :=
  left.region == right.region && left.valueType == right.valueType

def matchingRead (access : Access) (summary : Summary) : Bool :=
  summary.any fun candidate =>
    sameCell access candidate && candidate.kind.reads

def matchingWrite (access : Access) (summary : Summary) : Bool :=
  summary.any fun candidate =>
    sameCell access candidate && candidate.kind.writes

def coversReads (input output : Summary) : Bool :=
  input.all fun access => !access.kind.reads || matchingRead access output

def coversWrites (input output : Summary) : Bool :=
  input.all fun access => !access.kind.writes || matchingWrite access output

def typesAgree (input : Summary) : Bool :=
  input.all fun left =>
    input.all fun right =>
      left.region != right.region || left.valueType == right.valueType

/-- Strict region order makes a checked summary unique and duplicate-free. -/
def canonical : Summary → Bool
  | [] | [_] => true
  | left :: right :: rest => decide (left.region < right.region) && canonical (right :: rest)

/-- Check a producer-supplied result of the typed per-region effect fold.
Both directions are required: no reachable bit may be omitted, and no bit may
be invented.  `canonical` selects the one sorted representation. -/
def exactSummary (input output : Summary) : Bool :=
  typesAgree input && canonical output &&
  coversReads input output && coversWrites input output &&
  coversReads output input && coversWrites output input

def HasRead (summary : Summary) (region valueType : String) : Prop :=
  ∃ access ∈ summary,
    access.region = region ∧ access.valueType = valueType ∧ access.kind.reads = true

def HasWrite (summary : Summary) (region valueType : String) : Prop :=
  ∃ access ∈ summary,
    access.region = region ∧ access.valueType = valueType ∧ access.kind.writes = true

theorem matchingRead_iff (access : Access) (summary : Summary) :
    matchingRead access summary = true ↔
      ∃ candidate ∈ summary, SameCell access candidate ∧ candidate.kind.reads = true := by
  simp [matchingRead, sameCell, SameCell, Bool.and_eq_true]

theorem matchingWrite_iff (access : Access) (summary : Summary) :
    matchingWrite access summary = true ↔
      ∃ candidate ∈ summary, SameCell access candidate ∧ candidate.kind.writes = true := by
  simp [matchingWrite, sameCell, SameCell, Bool.and_eq_true]

theorem coversReads_preserves {input output : Summary}
    (h : coversReads input output = true) {region valueType : String}
    (present : HasRead input region valueType) : HasRead output region valueType := by
  obtain ⟨access, member, hr, ht, reads⟩ := present
  have covered := List.all_eq_true.mp h access member
  simp [reads] at covered
  obtain ⟨candidate, candidateMember, same, candidateReads⟩ :=
    (matchingRead_iff access output).mp covered
  exact ⟨candidate, candidateMember, same.1.symm.trans hr,
    same.2.symm.trans ht, candidateReads⟩

theorem coversWrites_preserves {input output : Summary}
    (h : coversWrites input output = true) {region valueType : String}
    (present : HasWrite input region valueType) : HasWrite output region valueType := by
  obtain ⟨access, member, hr, ht, writes⟩ := present
  have covered := List.all_eq_true.mp h access member
  simp [writes] at covered
  obtain ⟨candidate, candidateMember, same, candidateWrites⟩ :=
    (matchingWrite_iff access output).mp covered
  exact ⟨candidate, candidateMember, same.1.symm.trans hr,
    same.2.symm.trans ht, candidateWrites⟩

/-- A successful fold-result check contains exactly the input read bits. -/
theorem exactSummary_read_iff {input output : Summary}
    (h : exactSummary input output = true) (region valueType : String) :
    HasRead output region valueType ↔ HasRead input region valueType := by
  have parts :
      typesAgree input = true ∧ canonical output = true ∧
      coversReads input output = true ∧ coversWrites input output = true ∧
      coversReads output input = true ∧ coversWrites output input = true := by
    simpa [exactSummary, Bool.and_eq_true, and_assoc] using h
  rcases parts with ⟨_, _, inputRead, _, outputRead, _⟩
  exact ⟨coversReads_preserves outputRead, coversReads_preserves inputRead⟩

/-- A successful fold-result check contains exactly the input write bits. -/
theorem exactSummary_write_iff {input output : Summary}
    (h : exactSummary input output = true) (region valueType : String) :
    HasWrite output region valueType ↔ HasWrite input region valueType := by
  have parts :
      typesAgree input = true ∧ canonical output = true ∧
      coversReads input output = true ∧ coversWrites input output = true ∧
      coversReads output input = true ∧ coversWrites output input = true := by
    simpa [exactSummary, Bool.and_eq_true, and_assoc] using h
  rcases parts with ⟨_, _, _, inputWrite, _, outputWrite⟩
  exact ⟨coversWrites_preserves outputWrite, coversWrites_preserves inputWrite⟩

/-! ## A small postorder proof checker -/

structure Claim where
  callee : String
  accesses : Summary
  deriving DecidableEq, Repr

structure Step where
  name : String
  direct : Summary
  children : List Claim
  summary : Summary
  deriving DecidableEq, Repr

structure KnownSummary where
  name : String
  summary : Summary
  deriving DecidableEq, Repr

abbrev Known := List KnownSummary

def Known.lookup : Known → String → Option Summary
  | [], _ => none
  | known :: rest, name =>
      if known.name = name then some known.summary else Known.lookup rest name

def claimsMatch (known : Known) (claims : List Claim) : Bool :=
  claims.all fun claim =>
    match known.lookup claim.callee with
    | some summary => decide (summary = claim.accesses)
    | none => false

def stepInput (step : Step) : Summary :=
  step.direct ++ step.children.flatMap (·.accesses)

theorem stepInput_read_iff (step : Step) (region valueType : String) :
    HasRead (stepInput step) region valueType ↔
      HasRead step.direct region valueType ∨
        ∃ claim ∈ step.children, HasRead claim.accesses region valueType := by
  constructor
  · rintro ⟨access, member, hr, ht, reads⟩
    rw [stepInput, List.mem_append] at member
    rcases member with direct | children
    · exact Or.inl ⟨access, direct, hr, ht, reads⟩
    · obtain ⟨claim, claimMember, accessMember⟩ := List.mem_flatMap.mp children
      exact Or.inr ⟨claim, claimMember, access, accessMember, hr, ht, reads⟩
  · rintro (⟨access, member, hr, ht, reads⟩ |
      ⟨claim, claimMember, access, member, hr, ht, reads⟩)
    · exact ⟨access, by simp [stepInput, member], hr, ht, reads⟩
    · refine ⟨access, ?_, hr, ht, reads⟩
      rw [stepInput, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨claim, claimMember, member⟩)

theorem stepInput_write_iff (step : Step) (region valueType : String) :
    HasWrite (stepInput step) region valueType ↔
      HasWrite step.direct region valueType ∨
        ∃ claim ∈ step.children, HasWrite claim.accesses region valueType := by
  constructor
  · rintro ⟨access, member, hr, ht, writes⟩
    rw [stepInput, List.mem_append] at member
    rcases member with direct | children
    · exact Or.inl ⟨access, direct, hr, ht, writes⟩
    · obtain ⟨claim, claimMember, accessMember⟩ := List.mem_flatMap.mp children
      exact Or.inr ⟨claim, claimMember, access, accessMember, hr, ht, writes⟩
  · rintro (⟨access, member, hr, ht, writes⟩ |
      ⟨claim, claimMember, access, member, hr, ht, writes⟩)
    · exact ⟨access, by simp [stepInput, member], hr, ht, writes⟩
    · refine ⟨access, ?_, hr, ht, writes⟩
      rw [stepInput, List.mem_append]
      exact Or.inr (List.mem_flatMap.mpr ⟨claim, claimMember, member⟩)

def fresh (known : Known) (name : String) : Bool :=
  known.all fun entry => decide (entry.name ≠ name)

/-- Sequential validation makes the input list itself a topological witness. -/
def validFrom : Known → List Step → Bool
  | _, [] => true
  | known, step :: rest =>
      fresh known step.name && claimsMatch known step.children &&
      exactSummary (stepInput step) step.summary &&
      validFrom (⟨step.name, step.summary⟩ :: known) rest

def childNamesKnown (known : Known) (claims : List Claim) : Bool :=
  claims.all fun claim =>
    match known.lookup claim.callee with
    | some _ => true
    | none => false

/-- The graph-only part of validation: names are unique and every edge points
to an earlier node. Unlike `validFrom`, this predicate ignores summaries. -/
def postorderedFrom : Known → List Step → Bool
  | _, [] => true
  | known, step :: rest =>
      fresh known step.name && childNamesKnown known step.children &&
      postorderedFrom (⟨step.name, step.summary⟩ :: known) rest

theorem claimsMatch_childNamesKnown {known : Known} {claims : List Claim}
    (h : claimsMatch known claims = true) : childNamesKnown known claims = true := by
  apply List.all_eq_true.mpr
  intro claim member
  have matched := List.all_eq_true.mp h claim member
  cases lookup : known.lookup claim.callee with
  | none => simp [lookup] at matched
  | some summary => rfl

theorem validFrom_postordered {known : Known} {steps : List Step}
    (h : validFrom known steps = true) : postorderedFrom known steps = true := by
  induction steps generalizing known with
  | nil => rfl
  | cons step rest ih =>
      have parts :
          fresh known step.name = true ∧ claimsMatch known step.children = true ∧
          exactSummary (stepInput step) step.summary = true ∧
          validFrom (⟨step.name, step.summary⟩ :: known) rest = true := by
        simpa [validFrom, Bool.and_eq_true, and_assoc] using h
      rcases parts with ⟨freshName, claims, _, tail⟩
      simp [postorderedFrom, freshName, claimsMatch_childNamesKnown claims, ih tail]

def finalKnown (known : Known) (steps : List Step) : Known :=
  steps.foldl (fun state step => ⟨step.name, step.summary⟩ :: state) known

def lastName : List Step → Option String
  | [] => none
  | [step] => some step.name
  | _ :: rest => lastName rest

def referenced (steps : List Step) (name : String) : Bool :=
  steps.any fun parent => parent.children.any fun claim => decide (claim.callee = name)

/-- There are no unrelated certificate nodes: every non-root node has a
parent. Together with postorder this makes every node transitively lead to the
final root. -/
def closed (steps : List Step) (root : String) : Bool :=
  steps.all fun step => (step.name == root) || referenced steps step.name

def rooted : Known → String → Bool
  | [], _ => false
  | entry :: _, root => entry.name == root

def check (steps : List Step) (root : String) : Bool :=
  validFrom [] steps && closed steps root && rooted (finalKnown [] steps) root

/-- The proof relation denoted by an accepted structural certificate. -/
inductive Certifies (graph : List Step) : String → Summary → Prop where
  | node (step : Step)
      (member : step ∈ graph)
      (children : ∀ claim ∈ step.children,
        Certifies graph claim.callee claim.accesses)
      (exact : exactSummary (stepInput step) step.summary = true) :
      Certifies graph step.name step.summary

/-- One certificate node contains exactly its direct bits and the exact
summaries of recursively certified children. -/
theorem Certifies.read_exact {graph : List Step} {name : String} {summary : Summary}
    (certificate : Certifies graph name summary) (region valueType : String) :
    ∃ step ∈ graph,
      step.name = name ∧ step.summary = summary ∧
      (HasRead summary region valueType ↔
        HasRead step.direct region valueType ∨
          ∃ claim ∈ step.children, HasRead claim.accesses region valueType) ∧
      ∀ claim ∈ step.children, Certifies graph claim.callee claim.accesses := by
  cases certificate with
  | node step member children exact =>
      refine ⟨step, member, rfl, rfl, ?_, children⟩
      exact (exactSummary_read_iff exact region valueType).trans
        (stepInput_read_iff step region valueType)

/-- Write bits enjoy the same exact recursive decomposition. -/
theorem Certifies.write_exact {graph : List Step} {name : String} {summary : Summary}
    (certificate : Certifies graph name summary) (region valueType : String) :
    ∃ step ∈ graph,
      step.name = name ∧ step.summary = summary ∧
      (HasWrite summary region valueType ↔
        HasWrite step.direct region valueType ∨
          ∃ claim ∈ step.children, HasWrite claim.accesses region valueType) ∧
      ∀ claim ∈ step.children, Certifies graph claim.callee claim.accesses := by
  cases certificate with
  | node step member children exact =>
      refine ⟨step, member, rfl, rfl, ?_, children⟩
      exact (exactSummary_write_iff exact region valueType).trans
        (stepInput_write_iff step region valueType)

def KnownCertifies (graph : List Step) (known : Known) : Prop :=
  ∀ entry ∈ known, Certifies graph entry.name entry.summary

theorem known_lookup_mem {known : Known} {name : String} {summary : Summary}
    (h : known.lookup name = some summary) :
    ∃ entry ∈ known, entry.name = name ∧ entry.summary = summary := by
  induction known with
  | nil => simp [Known.lookup] at h
  | cons entry rest ih =>
      simp only [Known.lookup] at h
      split at h
      · rename_i equal
        simp only [Option.some.injEq] at h
        exact ⟨entry, by simp, equal, h⟩
      · obtain ⟨found, member, foundName, foundSummary⟩ := ih h
        exact ⟨found, by simp [member], foundName, foundSummary⟩

theorem validFrom_sound (graph : List Step) (steps : List Step) (known : Known)
    (suffix : ∀ step ∈ steps, step ∈ graph)
    (hknown : KnownCertifies graph known)
    (hvalid : validFrom known steps = true) :
    KnownCertifies graph (finalKnown known steps) := by
  induction steps generalizing known with
  | nil => simpa [finalKnown] using hknown
  | cons step rest ih =>
      have parts :
          fresh known step.name = true ∧ claimsMatch known step.children = true ∧
          exactSummary (stepInput step) step.summary = true ∧
          validFrom (⟨step.name, step.summary⟩ :: known) rest = true := by
        simpa [validFrom, Bool.and_eq_true, and_assoc] using hvalid
      rcases parts with ⟨_, claimsValid, stepExact, restValid⟩
      have childCertificates : ∀ claim ∈ step.children,
          Certifies graph claim.callee claim.accesses := by
        intro claim member
        have matched := List.all_eq_true.mp claimsValid claim member
        cases lookup : known.lookup claim.callee with
        | none => simp [lookup] at matched
        | some summary =>
            have equal : summary = claim.accesses := by
              simpa [claimsMatch, lookup] using matched
            obtain ⟨entry, entryMember, entryName, entrySummary⟩ := known_lookup_mem lookup
            have certified := hknown entry entryMember
            simpa [entryName, entrySummary, equal] using certified
      have stepCertificate : Certifies graph step.name step.summary :=
        .node step (suffix step (by simp)) childCertificates stepExact
      have extended : KnownCertifies graph (⟨step.name, step.summary⟩ :: known) := by
        intro entry member
        rcases List.mem_cons.mp member with rfl | old
        · exact stepCertificate
        · exact hknown entry old
      simp only [finalKnown, List.foldl_cons]
      apply ih (⟨step.name, step.summary⟩ :: known)
      · intro candidate member
        exact suffix candidate (by simp [member])
      · exact extended
      · exact restValid

theorem rooted_lookup {known : Known} {root : String}
    (h : rooted known root = true) :
    ∃ summary, known.lookup root = some summary := by
  cases known with
  | nil => simp [rooted] at h
  | cons entry rest =>
      have equal : entry.name = root := by simpa [rooted] using h
      exact ⟨entry.summary, by simp [Known.lookup, equal]⟩

/-- A graph is acyclic when its exact nodes admit a unique-name
child-before-parent ordering. Requiring a permutation of the steps, rather
than only their names, preserves every edge and summary claim. -/
def Acyclic (graph : List Step) : Prop :=
  ∃ order : List Step,
    order.Perm graph ∧ postorderedFrom [] order = true

/-- Acceptance exposes the three semantic facts the small checker is meant to
establish: closed graph, topological acyclicity, and an inductively exact root
summary. -/
theorem check_sound {steps : List Step} {root : String}
    (accepted : check steps root = true) :
    closed steps root = true ∧ Acyclic steps ∧
      ∃ summary, Certifies steps root summary := by
  simp only [check, Bool.and_eq_true] at accepted
  refine ⟨accepted.1.2,
    ⟨steps, List.Perm.refl _, validFrom_postordered accepted.1.1⟩, ?_⟩
  have knownSound := validFrom_sound steps steps [] (by simp) (by simp [KnownCertifies]) accepted.1.1
  obtain ⟨summary, found⟩ := rooted_lookup accepted.2
  obtain ⟨entry, member, entryName, entrySummary⟩ := known_lookup_mem found
  exact ⟨summary, by simpa [entryName, entrySummary] using knownSound entry member⟩

/-! ## Go decision pins

The Go correspondence test renders the live small-checker cases as these exact
single-line equations. -/

example : Effect.join (some .read) (some .read) = some .read := by decide
example : Effect.join (some .read) (some .write) = some .readWrite := by decide
example : Effect.join (some .read) (some .readWrite) = some .readWrite := by decide
example : Effect.join (some .write) (some .read) = some .readWrite := by decide
example : Effect.join (some .write) (some .write) = some .write := by decide
example : Effect.join (some .write) (some .readWrite) = some .readWrite := by decide
example : Effect.join (some .readWrite) (some .read) = some .readWrite := by decide
example : Effect.join (some .readWrite) (some .write) = some .readWrite := by decide
example : Effect.join (some .readWrite) (some .readWrite) = some .readWrite := by decide
example : check [⟨"root", [], [], []⟩] "root" = true := by decide
example : check [⟨"leaf", [⟨"global:x", .read, "u32"⟩], [], [⟨"global:x", .read, "u32"⟩]⟩] "leaf" = true := by decide
example : check [⟨"leaf", [⟨"global:x", .read, "u32"⟩], [], [⟨"global:x", .read, "u32"⟩]⟩, ⟨"root", [], [⟨"leaf", [⟨"global:x", .read, "u32"⟩]⟩], [⟨"global:x", .read, "u32"⟩]⟩] "root" = true := by decide
example : check [⟨"leaf", [⟨"global:x", .read, "u32"⟩], [], [⟨"global:x", .read, "u32"⟩]⟩, ⟨"left", [⟨"global:y", .write, "u64"⟩], [⟨"leaf", [⟨"global:x", .read, "u32"⟩]⟩], [⟨"global:x", .read, "u32"⟩, ⟨"global:y", .write, "u64"⟩]⟩, ⟨"right", [⟨"global:x", .write, "u32"⟩], [], [⟨"global:x", .write, "u32"⟩]⟩, ⟨"root", [], [⟨"left", [⟨"global:x", .read, "u32"⟩, ⟨"global:y", .write, "u64"⟩]⟩, ⟨"right", [⟨"global:x", .write, "u32"⟩]⟩], [⟨"global:x", .readWrite, "u32"⟩, ⟨"global:y", .write, "u64"⟩]⟩] "root" = true := by decide
example : check [⟨"root", [], [⟨"leaf", [⟨"global:x", .read, "u32"⟩]⟩], [⟨"global:x", .read, "u32"⟩]⟩, ⟨"leaf", [⟨"global:x", .read, "u32"⟩], [], [⟨"global:x", .read, "u32"⟩]⟩] "leaf" = false := by decide
example : check [⟨"leaf", [⟨"global:x", .read, "u32"⟩], [], [⟨"global:x", .read, "u32"⟩]⟩, ⟨"leaf", [⟨"global:x", .read, "u32"⟩], [], [⟨"global:x", .read, "u32"⟩]⟩] "leaf" = false := by decide
example : check [⟨"leaf", [⟨"global:x", .read, "u32"⟩], [], [⟨"global:x", .read, "u32"⟩]⟩] "other" = false := by decide
example : check [⟨"leaf", [⟨"global:x", .read, "u32"⟩], [], [⟨"global:x", .read, "u32"⟩]⟩, ⟨"root", [], [], []⟩] "root" = false := by decide
example : check [⟨"leaf", [⟨"global:x", .read, "u32"⟩], [], [⟨"global:x", .read, "u32"⟩]⟩, ⟨"root", [], [⟨"leaf", [⟨"global:x", .write, "u32"⟩]⟩], [⟨"global:x", .write, "u32"⟩]⟩] "root" = false := by decide
example : check [⟨"root", [⟨"global:x", .read, "u32"⟩, ⟨"global:x", .write, "u64"⟩], [], [⟨"global:x", .readWrite, "u32"⟩]⟩] "root" = false := by decide

end Oak.OptIRCallSummaryCertificate
