import Oak.OptIRCallSummaryCertificate

/-!
# OptIR checked-memory authority projection

This module models the small structural checker that projects a sequence of
already-verified CFG operations through separate checked-memory authority.
Operations carry only opaque access/call identifiers.  Acceptance requires
each active identifier to resolve exactly once, at the original source and
with the exact direct-operation shape or callee recorded by authority.  An
untagged direct access, call, or opaque effect is rejected.

Two coverage modes are explicit.  `exact` is used for original non-root call
graph nodes and requires every authority record to remain active.  `upperBound`
is used for an optimized root and permits soundly unused authority records,
while still requiring every operation that remains active to resolve exactly.

The concrete Go CFG walk, `optir.Verify`, source-location representation,
load/store type validation, authority-record construction, SHA-256 identities,
and the semantic truth of a transported callee summary are outside this
module.  `Source` and `DirectShape` below are opaque exact atoms standing for
the output of those checks.  The theorem here is the structural seam from an
operation list plus valid authority to its active direct accesses and child
summary claims.
-/

namespace Oak.OptIRMemoryAuthorityProjection

open Oak.OptIRCallSummaryCertificate

abbrev Source := String

/-- The equality-relevant result of concrete direct-operation validation. -/
structure DirectShape where
  opcode : String
  kind : AccessKind
  valueType : String
  wholeRegion : Bool
  volatile : Bool
  deriving DecidableEq, Repr

inductive OperationForm where
  | pure
  | direct (shape : DirectShape)
  | call (callee : String)
  | opaqueEffect
  deriving DecidableEq, Repr

/-- One operation in verified CFG layout order. -/
structure Operation where
  source : Source
  form : OperationForm
  accessID : Option String := none
  callID : Option String := none
  deriving DecidableEq, Repr

structure DirectRecord where
  id : String
  source : Source
  shape : DirectShape
  access : Access
  deriving DecidableEq, Repr

structure CallRecord where
  id : String
  source : Source
  callee : String
  accesses : Summary
  deriving DecidableEq, Repr

structure Authority where
  direct : List DirectRecord
  calls : List CallRecord
  deriving DecidableEq, Repr

def Authority.lookupDirect : Authority → String → Option DirectRecord
  | authority, id => authority.direct.find? fun record => record.id = id

def Authority.lookupCall : Authority → String → Option CallRecord
  | authority, id => authority.calls.find? fun record => record.id = id

def uniqueStrings : List String → Bool
  | [] => true
  | id :: rest => !rest.contains id && uniqueStrings rest

def DirectRecord.wellFormed (record : DirectRecord) : Bool :=
  decide (record.id ≠ "" ∧ record.access.region ≠ "" ∧
    record.shape.kind = record.access.kind ∧
    record.shape.valueType = record.access.valueType)

def CallRecord.wellFormed (record : CallRecord) : Bool :=
  decide (record.id ≠ "" ∧ record.callee ≠ "")

/-- Authority identities are nonempty, unique within each class, and disjoint
across direct accesses and calls. -/
def validAuthority (authority : Authority) : Bool :=
  authority.direct.all DirectRecord.wellFormed &&
  authority.calls.all CallRecord.wellFormed &&
  uniqueStrings (authority.direct.map (·.id)) &&
  uniqueStrings (authority.calls.map (·.id)) &&
  authority.direct.all fun direct =>
    authority.calls.all fun call => decide (direct.id ≠ call.id)

inductive Resolved where
  | inactive
  | direct (access : Access)
  | call (claim : Claim)
  deriving DecidableEq, Repr

/-- Resolve one operation without trusting the operation to describe its own
memory region, kind, type, or callee summary. -/
def resolve (authority : Authority) (operation : Operation) : Option Resolved :=
  match operation.accessID, operation.callID with
  | some _, some _ => none
  | some id, none =>
      match authority.lookupDirect id with
      | none => none
      | some record =>
          if decide (operation.source = record.source ∧
              operation.form = .direct record.shape) then
            some (.direct record.access)
          else none
  | none, some id =>
      match authority.lookupCall id with
      | none => none
      | some record =>
          if decide (operation.source = record.source ∧
              operation.form = .call record.callee) then
            some (.call ⟨record.callee, record.accesses⟩)
          else none
  | none, none =>
      match operation.form with
      | .pure => some .inactive
      | .direct _ | .call _ | .opaqueEffect => none

def referencedIDs (operations : List Operation) : List String :=
  operations.flatMap fun operation =>
    operation.accessID.toList ++ operation.callID.toList

def uniqueReferences (operations : List Operation) : Bool :=
  uniqueStrings (referencedIDs operations)

def resolvesAll (authority : Authority) (operations : List Operation) : Bool :=
  operations.all fun operation => (resolve authority operation).isSome

def referencesAccess (operations : List Operation) (id : String) : Bool :=
  operations.any fun operation => decide (operation.accessID = some id)

def referencesCall (operations : List Operation) (id : String) : Bool :=
  operations.any fun operation => decide (operation.callID = some id)

inductive CoverageMode where
  | exact
  | upperBound
  deriving DecidableEq, Repr

def coverageOK (mode : CoverageMode) (authority : Authority)
    (operations : List Operation) : Bool :=
  match mode with
  | .upperBound => true
  | .exact =>
      (authority.direct.all fun record => referencesAccess operations record.id) &&
      (authority.calls.all fun record => referencesCall operations record.id)

def collectDirect (authority : Authority) : List Operation → Summary
  | [] => []
  | operation :: rest =>
      match resolve authority operation with
      | some (.direct access) => access :: collectDirect authority rest
      | _ => collectDirect authority rest

def collectCalls (authority : Authority) : List Operation → List Claim
  | [] => []
  | operation :: rest =>
      match resolve authority operation with
      | some (.call claim) => claim :: collectCalls authority rest
      | _ => collectCalls authority rest

structure Projection where
  direct : Summary
  children : List Claim
  deriving DecidableEq, Repr

def prerequisites (mode : CoverageMode) (authority : Authority)
    (operations : List Operation) : Bool :=
  validAuthority authority && uniqueReferences operations &&
  resolvesAll authority operations && coverageOK mode authority operations

/-- The executable structural projection checker. -/
def project (mode : CoverageMode) (authority : Authority)
    (operations : List Operation) : Option Projection :=
  if prerequisites mode authority operations then
    some ⟨collectDirect authority operations, collectCalls authority operations⟩
  else none

/-- Check a producer-supplied projection rather than silently replacing it. -/
def check (mode : CoverageMode) (authority : Authority)
    (operations : List Operation) (claimed : Projection) : Bool :=
  match project mode authority operations with
  | none => false
  | some actual => decide (actual = claimed)

def ActiveDirect (authority : Authority) (operation : Operation)
    (access : Access) : Prop :=
  resolve authority operation = some (.direct access)

def ActiveCall (authority : Authority) (operation : Operation)
    (claim : Claim) : Prop :=
  resolve authority operation = some (.call claim)

/-! ## Resolution inversion -/

theorem resolve_direct_exact {authority : Authority} {operation : Operation}
    {access : Access} (active : ActiveDirect authority operation access) :
    ∃ id record,
      operation.accessID = some id ∧ operation.callID = none ∧
      authority.lookupDirect id = some record ∧
      operation.source = record.source ∧
      operation.form = .direct record.shape ∧ record.access = access := by
  unfold ActiveDirect at active
  cases accessID : operation.accessID with
  | none =>
      cases callID : operation.callID with
      | none =>
          cases form : operation.form <;>
            simp [resolve, accessID, callID, form] at active
      | some id =>
          cases lookup : authority.lookupCall id with
          | none => simp [resolve, accessID, callID, lookup] at active
          | some record =>
              by_cases exact : operation.source = record.source ∧
                  operation.form = .call record.callee <;>
                simp [resolve, accessID, callID, lookup, exact] at active
  | some id =>
      cases callID : operation.callID with
      | some call => simp [resolve, accessID, callID] at active
      | none =>
          cases lookup : authority.lookupDirect id with
          | none => simp [resolve, accessID, callID, lookup] at active
          | some record =>
              by_cases exact : operation.source = record.source ∧
                  operation.form = .direct record.shape
              · have accessEqual : record.access = access := by
                  simpa [resolve, accessID, callID, lookup, exact] using active
                exact ⟨id, record, rfl, rfl, lookup,
                  exact.1, exact.2, accessEqual⟩
              · simp [resolve, accessID, callID, lookup, exact] at active

theorem resolve_call_exact {authority : Authority} {operation : Operation}
    {claim : Claim} (active : ActiveCall authority operation claim) :
    ∃ id record,
      operation.accessID = none ∧ operation.callID = some id ∧
      authority.lookupCall id = some record ∧
      operation.source = record.source ∧
      operation.form = .call record.callee ∧
      (⟨record.callee, record.accesses⟩ : Claim) = claim := by
  unfold ActiveCall at active
  cases accessID : operation.accessID with
  | some access =>
      cases callID : operation.callID with
      | some call => simp [resolve, accessID, callID] at active
      | none =>
          cases lookup : authority.lookupDirect access with
          | none => simp [resolve, accessID, callID, lookup] at active
          | some record =>
              by_cases exact : operation.source = record.source ∧
                  operation.form = .direct record.shape <;>
                simp [resolve, accessID, callID, lookup, exact] at active
  | none =>
      cases callID : operation.callID with
      | none =>
          cases form : operation.form <;>
            simp [resolve, accessID, callID, form] at active
      | some id =>
          cases lookup : authority.lookupCall id with
          | none => simp [resolve, accessID, callID, lookup] at active
          | some record =>
              by_cases exact : operation.source = record.source ∧
                  operation.form = .call record.callee
              · have claimEqual : (⟨record.callee, record.accesses⟩ : Claim) = claim := by
                  simpa [resolve, accessID, callID, lookup, exact] using active
                exact ⟨id, record, rfl, rfl, lookup,
                  exact.1, exact.2, claimEqual⟩
              · simp [resolve, accessID, callID, lookup, exact] at active

/-! ## Exact active projection -/

theorem mem_collectDirect_iff (authority : Authority)
    (operations : List Operation) (access : Access) :
    access ∈ collectDirect authority operations ↔
      ∃ operation ∈ operations, ActiveDirect authority operation access := by
  induction operations with
  | nil => simp [collectDirect]
  | cons operation rest ih =>
      cases resolved : resolve authority operation with
      | none => simp [collectDirect, resolved, ActiveDirect, ih]
      | some result =>
          cases result with
          | inactive => simp [collectDirect, resolved, ActiveDirect, ih]
          | direct found => simp [collectDirect, resolved, ActiveDirect, ih, eq_comm]
          | call found => simp [collectDirect, resolved, ActiveDirect, ih]

theorem mem_collectCalls_iff (authority : Authority)
    (operations : List Operation) (claim : Claim) :
    claim ∈ collectCalls authority operations ↔
      ∃ operation ∈ operations, ActiveCall authority operation claim := by
  induction operations with
  | nil => simp [collectCalls]
  | cons operation rest ih =>
      cases resolved : resolve authority operation with
      | none => simp [collectCalls, resolved, ActiveCall, ih]
      | some result =>
          cases result with
          | inactive => simp [collectCalls, resolved, ActiveCall, ih]
          | direct found => simp [collectCalls, resolved, ActiveCall, ih]
          | call found => simp [collectCalls, resolved, ActiveCall, ih, eq_comm]

theorem check_project {mode : CoverageMode} {authority : Authority}
    {operations : List Operation} {claimed : Projection}
    (accepted : check mode authority operations claimed = true) :
    project mode authority operations = some claimed := by
  unfold check at accepted
  cases result : project mode authority operations with
  | none => simp [result] at accepted
  | some actual =>
      have equal : actual = claimed := by simpa [result] using accepted
      simp [equal]

theorem project_payload {mode : CoverageMode} {authority : Authority}
    {operations : List Operation} {projection : Projection}
    (accepted : project mode authority operations = some projection) :
    projection = ⟨collectDirect authority operations,
      collectCalls authority operations⟩ := by
  unfold project at accepted
  split at accepted
  · exact (Option.some.inj accepted).symm
  · simp at accepted

theorem project_prerequisites {mode : CoverageMode} {authority : Authority}
    {operations : List Operation} {projection : Projection}
    (accepted : project mode authority operations = some projection) :
    prerequisites mode authority operations = true := by
  unfold project at accepted
  split at accepted
  · assumption
  · simp at accepted

/-- An accepted projection contains every and only active direct access. -/
theorem check_direct_iff {mode : CoverageMode} {authority : Authority}
    {operations : List Operation} {claimed : Projection}
    (accepted : check mode authority operations claimed = true)
    (access : Access) :
    access ∈ claimed.direct ↔
      ∃ operation ∈ operations, ActiveDirect authority operation access := by
  have projected := check_project accepted
  have payload := project_payload projected
  rw [payload]
  exact mem_collectDirect_iff authority operations access

/-- An accepted projection contains every and only active call claim.  Empty
claim access lists (NoModRef) are preserved as ordinary child claims. -/
theorem check_call_iff {mode : CoverageMode} {authority : Authority}
    {operations : List Operation} {claimed : Projection}
    (accepted : check mode authority operations claimed = true)
    (claim : Claim) :
    claim ∈ claimed.children ↔
      ∃ operation ∈ operations, ActiveCall authority operation claim := by
  have projected := check_project accepted
  have payload := project_payload projected
  rw [payload]
  exact mem_collectCalls_iff authority operations claim

/-- The complete semantic payload of acceptance: integrity preconditions hold,
and both output classes are exact rather than merely conservative. -/
theorem check_sound {mode : CoverageMode} {authority : Authority}
    {operations : List Operation} {claimed : Projection}
    (accepted : check mode authority operations claimed = true) :
    (validAuthority authority = true ∧ uniqueReferences operations = true ∧
      resolvesAll authority operations = true ∧
      coverageOK mode authority operations = true) ∧
    (∀ access, access ∈ claimed.direct ↔
      ∃ operation ∈ operations, ActiveDirect authority operation access) ∧
    (∀ claim, claim ∈ claimed.children ↔
      ∃ operation ∈ operations, ActiveCall authority operation claim) := by
  have prerequisiteProof := project_prerequisites (check_project accepted)
  have parts :
      validAuthority authority = true ∧ uniqueReferences operations = true ∧
      resolvesAll authority operations = true ∧
      coverageOK mode authority operations = true := by
    simpa [prerequisites, Bool.and_eq_true, and_assoc] using prerequisiteProof
  exact ⟨parts, check_direct_iff accepted, check_call_iff accepted⟩

/-! ## Composition with the exact summary fold -/

/-- Once the existing exact-summary checker accepts the projection payload,
its output contains exactly the read bits of active direct operations and
active checked call claims. -/
theorem check_exactSummary_read_iff {mode : CoverageMode}
    {authority : Authority} {operations : List Operation}
    {claimed : Projection} {summary : Summary}
    (accepted : check mode authority operations claimed = true)
    (folded : exactSummary
      (claimed.direct ++ claimed.children.flatMap (·.accesses)) summary = true)
    (region valueType : String) :
    HasRead summary region valueType ↔
      (∃ operation ∈ operations, ∃ access,
        ActiveDirect authority operation access ∧
        access.region = region ∧ access.valueType = valueType ∧
        access.kind.reads = true) ∨
      (∃ operation ∈ operations, ∃ claim,
        ActiveCall authority operation claim ∧
        HasRead claim.accesses region valueType) := by
  have split :
      HasRead (claimed.direct ++ claimed.children.flatMap (·.accesses))
          region valueType ↔
        HasRead claimed.direct region valueType ∨
          ∃ claim ∈ claimed.children,
            HasRead claim.accesses region valueType := by
    simpa [stepInput] using
      (stepInput_read_iff
        (⟨"", claimed.direct, claimed.children, []⟩ : Step) region valueType)
  rw [exactSummary_read_iff folded, split]
  constructor
  · rintro (⟨access, member, accessRegion, accessType, reads⟩ |
      ⟨claim, member, reads⟩)
    · obtain ⟨operation, operationMember, active⟩ :=
        (check_direct_iff accepted access).mp member
      exact Or.inl ⟨operation, operationMember, access, active,
        accessRegion, accessType, reads⟩
    · obtain ⟨operation, operationMember, active⟩ :=
        (check_call_iff accepted claim).mp member
      exact Or.inr ⟨operation, operationMember, claim, active, reads⟩
  · rintro (⟨operation, operationMember, access, active,
        accessRegion, accessType, reads⟩ |
      ⟨operation, operationMember, claim, active, reads⟩)
    · exact Or.inl ⟨access,
        (check_direct_iff accepted access).mpr
          ⟨operation, operationMember, active⟩,
        accessRegion, accessType, reads⟩
    · exact Or.inr ⟨claim,
        (check_call_iff accepted claim).mpr
          ⟨operation, operationMember, active⟩,
        reads⟩

/-- The analogous composition theorem for write bits. -/
theorem check_exactSummary_write_iff {mode : CoverageMode}
    {authority : Authority} {operations : List Operation}
    {claimed : Projection} {summary : Summary}
    (accepted : check mode authority operations claimed = true)
    (folded : exactSummary
      (claimed.direct ++ claimed.children.flatMap (·.accesses)) summary = true)
    (region valueType : String) :
    HasWrite summary region valueType ↔
      (∃ operation ∈ operations, ∃ access,
        ActiveDirect authority operation access ∧
        access.region = region ∧ access.valueType = valueType ∧
        access.kind.writes = true) ∨
      (∃ operation ∈ operations, ∃ claim,
        ActiveCall authority operation claim ∧
        HasWrite claim.accesses region valueType) := by
  have split :
      HasWrite (claimed.direct ++ claimed.children.flatMap (·.accesses))
          region valueType ↔
        HasWrite claimed.direct region valueType ∨
          ∃ claim ∈ claimed.children,
            HasWrite claim.accesses region valueType := by
    simpa [stepInput] using
      (stepInput_write_iff
        (⟨"", claimed.direct, claimed.children, []⟩ : Step) region valueType)
  rw [exactSummary_write_iff folded, split]
  constructor
  · rintro (⟨access, member, accessRegion, accessType, writes⟩ |
      ⟨claim, member, writes⟩)
    · obtain ⟨operation, operationMember, active⟩ :=
        (check_direct_iff accepted access).mp member
      exact Or.inl ⟨operation, operationMember, access, active,
        accessRegion, accessType, writes⟩
    · obtain ⟨operation, operationMember, active⟩ :=
        (check_call_iff accepted claim).mp member
      exact Or.inr ⟨operation, operationMember, claim, active, writes⟩
  · rintro (⟨operation, operationMember, access, active,
        accessRegion, accessType, writes⟩ |
      ⟨operation, operationMember, claim, active, writes⟩)
    · exact Or.inl ⟨access,
        (check_direct_iff accepted access).mpr
          ⟨operation, operationMember, active⟩,
        accessRegion, accessType, writes⟩
    · exact Or.inr ⟨claim,
        (check_call_iff accepted claim).mpr
          ⟨operation, operationMember, active⟩,
        writes⟩

theorem referencesAccess_iff (operations : List Operation) (id : String) :
    referencesAccess operations id = true ↔
      ∃ operation ∈ operations, operation.accessID = some id := by
  simp [referencesAccess]

theorem referencesCall_iff (operations : List Operation) (id : String) :
    referencesCall operations id = true ↔
      ∃ operation ∈ operations, operation.callID = some id := by
  simp [referencesCall]

/-- Exact (non-root) mode proves that no direct authority entry disappeared. -/
theorem exact_uses_every_direct {authority : Authority}
    {operations : List Operation} {claimed : Projection}
    (accepted : check .exact authority operations claimed = true)
    (record : DirectRecord) (member : record ∈ authority.direct) :
    ∃ operation ∈ operations, operation.accessID = some record.id := by
  have prerequisitesTrue := project_prerequisites (check_project accepted)
  have coverage : coverageOK .exact authority operations = true := by
    have parts :
        validAuthority authority = true ∧ uniqueReferences operations = true ∧
        resolvesAll authority operations = true ∧
        coverageOK .exact authority operations = true := by
      simpa [prerequisites, Bool.and_eq_true, and_assoc] using prerequisitesTrue
    exact parts.2.2.2
  have parts :
      (authority.direct.all fun record => referencesAccess operations record.id) = true ∧
      (authority.calls.all fun record => referencesCall operations record.id) = true := by
    simpa [coverageOK, Bool.and_eq_true] using coverage
  have referenced := List.all_eq_true.mp parts.1 record member
  exact (referencesAccess_iff operations record.id).mp referenced

/-- Exact (non-root) mode also proves that no call authority entry disappeared. -/
theorem exact_uses_every_call {authority : Authority}
    {operations : List Operation} {claimed : Projection}
    (accepted : check .exact authority operations claimed = true)
    (record : CallRecord) (member : record ∈ authority.calls) :
    ∃ operation ∈ operations, operation.callID = some record.id := by
  have prerequisitesTrue := project_prerequisites (check_project accepted)
  have coverage : coverageOK .exact authority operations = true := by
    have parts :
        validAuthority authority = true ∧ uniqueReferences operations = true ∧
        resolvesAll authority operations = true ∧
        coverageOK .exact authority operations = true := by
      simpa [prerequisites, Bool.and_eq_true, and_assoc] using prerequisitesTrue
    exact parts.2.2.2
  have parts :
      (authority.direct.all fun record => referencesAccess operations record.id) = true ∧
      (authority.calls.all fun record => referencesCall operations record.id) = true := by
    simpa [coverageOK, Bool.and_eq_true] using coverage
  have referenced := List.all_eq_true.mp parts.2 record member
  exact (referencesCall_iff operations record.id).mp referenced

/-! ## Executable refusal/coverage pins -/

private def readShape : DirectShape :=
  ⟨"memory.region-load", .read, "u32", false, false⟩

private def readAccess : Access := ⟨"global:x", .read, "u32"⟩

private def directRecord : DirectRecord :=
  ⟨"access:1", "source:1", readShape, readAccess⟩

private def callRecord : CallRecord :=
  ⟨"call:1", "source:2", "leaf", []⟩

private def authority : Authority := ⟨[directRecord], [callRecord]⟩

private def directOperation : Operation :=
  ⟨"source:1", .direct readShape, some "access:1", none⟩

private def callOperation : Operation :=
  ⟨"source:2", .call "leaf", none, some "call:1"⟩

private def expected : Projection :=
  ⟨[readAccess], [⟨"leaf", []⟩]⟩

example : check .exact authority [directOperation, callOperation] expected = true := by decide
example : check .upperBound authority [] ⟨[], []⟩ = true := by decide
example : check .exact authority [] ⟨[], []⟩ = false := by decide

-- Both IDs, unknown IDs, and a duplicate active identity fail closed.
example : check .upperBound authority
    [⟨"source:1", .direct readShape, some "access:1", some "call:1"⟩]
    ⟨[], []⟩ = false := by decide
example : check .upperBound authority
    [⟨"source:1", .direct readShape, some "unknown", none⟩]
    ⟨[], []⟩ = false := by decide
example : check .upperBound authority [directOperation, directOperation]
    ⟨[readAccess, readAccess], []⟩ = false := by decide

-- Untagged effects and source/shape/callee substitutions fail closed.
example : check .upperBound authority
    [⟨"source:1", .direct readShape, none, none⟩] ⟨[], []⟩ = false := by decide
example : check .upperBound authority
    [⟨"source:1", .opaqueEffect, none, none⟩] ⟨[], []⟩ = false := by decide
example : check .upperBound authority
    [⟨"moved", .direct readShape, some "access:1", none⟩] ⟨[], []⟩ = false := by decide
example : check .upperBound authority
    [⟨"source:1", .direct { readShape with valueType := "u64" },
      some "access:1", none⟩] ⟨[], []⟩ = false := by decide
example : check .upperBound authority
    [⟨"source:2", .call "other", none, some "call:1"⟩] ⟨[], []⟩ = false := by decide

end Oak.OptIRMemoryAuthorityProjection
