import Oak.PatternAnalysis

namespace Oak.PatternAnalysisRefinement

open Oak.PatternAnalysis

/-- Terminal leaves of the implementation's unary constructor/payload tree. -/
inductive SemanticLeaf where
  | unit
  | bool : Bool → SemanticLeaf
  | scalar : Nat → SemanticLeaf
  deriving DecidableEq, Repr

/-- A recursively expanded semantic case is a constructor path and its leaf. -/
structure SemanticCase where
  constructors : List Nat
  leaf : SemanticLeaf
  deriving DecidableEq, Repr

/-- The checker-side pattern fragment handled by the structural coverage tree. -/
inductive LeafPattern where
  | any
  | unit
  | bool : Bool → LeafPattern
  | scalar : Nat → LeafPattern
  deriving DecidableEq, Repr

structure ConcretePattern where
  constructors : List Nat
  leaf : LeafPattern
  deriving DecidableEq, Repr

def PrefixBool : List Nat → List Nat → Bool
  | [], _ => true
  | _, [] => false
  | expected :: expectedRest, actual :: actualRest =>
      expected == actual && PrefixBool expectedRest actualRest

/-- Executable recursive matching corresponding to `applyCoverage`: a catch-all
    covers the current subtree, and constructor payloads are checked recursively. -/
def MatchesBool (pattern : ConcretePattern) (value : SemanticCase) : Bool :=
  match pattern.leaf with
  | .any => PrefixBool pattern.constructors value.constructors
  | .unit => pattern.constructors == value.constructors && value.leaf == .unit
  | .bool expected =>
      pattern.constructors == value.constructors && value.leaf == .bool expected
  | .scalar expected =>
      pattern.constructors == value.constructors && value.leaf == .scalar expected

def CoveredBool (arms : List ConcretePattern) (value : SemanticCase) : Bool :=
  arms.any fun pattern => MatchesBool pattern value

/-- The abstract covered-case set denoted by the concrete pattern list. -/
def CoveredCases (cases : List SemanticCase) (arms : List ConcretePattern) :
    List SemanticCase :=
  cases.filter fun value => CoveredBool arms value

/-- Concrete missing-case enumeration. Its order is the semantic constructor
    order, matching the deterministic traversal used by `coverageWitnesses`. -/
def MissingCases
    (cases reachable : List SemanticCase)
    (arms : List ConcretePattern) : List SemanticCase :=
  reachable.filter fun value =>
    decide (value ∈ cases) && !CoveredBool arms value

def CompleteBool
    (cases reachable : List SemanticCase)
    (arms : List ConcretePattern) : Bool :=
  (MissingCases cases reachable arms).isEmpty

def Witnesses
    (cases reachable : List SemanticCase)
    (arms : List ConcretePattern)
    (limit : Nat) : List SemanticCase :=
  (MissingCases cases reachable arms).take limit

/-- Cases denoted by one concrete arm, used to relate the checker's unchanged
    coverage result to the abstract redundancy definition. -/
def ArmCases (cases : List SemanticCase) (arm : ConcretePattern) :
    List SemanticCase :=
  cases.filter fun value => MatchesBool arm value

def RedundantBool
    (covered cases : List SemanticCase)
    (arm : ConcretePattern) : Bool :=
  (ArmCases cases arm).all fun value => decide (value ∈ covered)

private theorem all_eq_true_iff {xs : List α} {p : α → Bool} :
    xs.all p = true ↔ ∀ x ∈ xs, p x = true := by
  induction xs with
  | nil => simp
  | cons head tail ih => simp [List.all, ih]

/-- The concrete recursive matcher populates exactly the abstract covered list
    supplied to the semantic pattern-analysis relation. -/
theorem mem_coveredCases_iff
    (cases : List SemanticCase)
    (arms : List ConcretePattern)
    (value : SemanticCase) :
    value ∈ CoveredCases cases arms ↔
      value ∈ cases ∧ CoveredBool arms value = true := by
  simp [CoveredCases]

/-- Soundness of every generated source-level witness: each reported leaf is
    reachable, belongs to the closed case universe, and is not covered. -/
theorem witness_is_counterexample
    {cases reachable : List SemanticCase}
    {arms : List ConcretePattern}
    {limit : Nat}
    {value : SemanticCase}
    (h : value ∈ Witnesses cases reachable arms limit) :
    Counterexample cases reachable (CoveredCases cases arms) value := by
  have hmissing : value ∈ MissingCases cases reachable arms :=
    List.mem_of_mem_take h
  have hparts :
      value ∈ reachable ∧ value ∈ cases ∧ CoveredBool arms value = false := by
    simpa [MissingCases, Bool.and_eq_true] using hmissing
  apply missing_reachable_is_counterexample hparts.2.1 hparts.1
  simp [CoveredCases, hparts.2.2]

/-- Completeness refinement for finite recursive domains: the executable check
    succeeds exactly when the abstract reachable-case relation is exhaustive. -/
theorem completeBool_iff_exhaustive
    (cases reachable : List SemanticCase)
    (arms : List ConcretePattern) :
    CompleteBool cases reachable arms = true ↔
      Exhaustive cases reachable (CoveredCases cases arms) := by
  constructor
  · intro hcomplete value hreachable
    by_cases hcovered : value ∈ CoveredCases cases arms
    · exact hcovered
    · have hcoveredFalse : CoveredBool arms value = false := by
        cases hbool : CoveredBool arms value with
        | false => rfl
        | true =>
            exact False.elim (hcovered (by
              simp [CoveredCases, hreachable.1, hbool]))
      have hmissing : value ∈ MissingCases cases reachable arms := by
        simp [MissingCases, hreachable.2, hreachable.1, hcoveredFalse]
      cases hlist : MissingCases cases reachable arms with
      | nil => simp [hlist] at hmissing
      | cons head tail => simp [CompleteBool, hlist] at hcomplete
  · intro hexhaustive
    cases hlist : MissingCases cases reachable arms with
    | nil => simp [CompleteBool, hlist]
    | cons value rest =>
        have hmissing : value ∈ MissingCases cases reachable arms := by
          simp [hlist]
        have hparts :
            value ∈ reachable ∧ value ∈ cases ∧ CoveredBool arms value = false := by
          simpa [MissingCases, Bool.and_eq_true] using hmissing
        have hcovered := hexhaustive value ⟨hparts.2.1, hparts.1⟩
        simp [CoveredCases, hparts.2.2] at hcovered

/-- The checker's no-change decision for an arm coincides with the abstract
    definition of redundancy over the finite semantic case expansion. -/
theorem redundantBool_iff_redundant
    (covered cases : List SemanticCase)
    (arm : ConcretePattern) :
    RedundantBool covered cases arm = true ↔
      Redundant covered (ArmCases cases arm) := by
  constructor
  · intro h value hvalue
    have hall := all_eq_true_iff.mp h
    simpa using hall value hvalue
  · intro h
    apply all_eq_true_iff.mpr
    intro value hvalue
    simpa using h value hvalue

end Oak.PatternAnalysisRefinement
