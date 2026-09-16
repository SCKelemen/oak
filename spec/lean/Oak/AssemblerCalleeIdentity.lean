/-!
# Assembler direct-callee identity

The assembler verifier may summarize a direct machine call at an Oak
declaration's body.  This module specifies the small identity decision at
that boundary.  A lookup result is canonical only when its map key is a
nonempty, non-reserved Oak name and the declaration reached through that key
has exactly the same name.

Scalar lookup uses the machine symbol's exact map slot.  Vector lookup is
preclassified with the active lane's suffix and exposes both the exact-symbol
slot and the base-name slot.  An occupied exact slot makes a vector spelling
ambiguous and rejects before its contents are considered; fallback to the
base is allowed only when that slot is absent.  Missing, aliased, malformed,
wrong-lane, and ambiguous requests therefore all fail closed.

This model begins after concrete instructions have been classified as direct
calls and suffix lookup has been projected into `Request`.  Instruction
decoding, Go map implementation, vector-contract checking, ABI correctness,
body semantics, and linker resolution are separate obligations.
-/

namespace Oak.AssemblerCalleeIdentity

inductive Arch where
  | arm64
  | rv64
  deriving BEq, DecidableEq, Repr

inductive Contract where
  | scalar
  | vector
  deriving BEq, DecidableEq, Repr

/-- The lane-specific suffix used by the native vector calling contract. -/
def vectorSuffix : Arch → String
  | .arm64 => "_neon_abi"
  | .rv64 => "_rvv_abi"

/-- Source declarations may not occupy either backend-owned ABI namespace,
independently of the active target. -/
def reservedSourceName (name : String) : Bool :=
  name.endsWith (vectorSuffix .arm64) ||
    name.endsWith (vectorSuffix .rv64)

/-- The only native symbol a declaration may authorize under a contract. -/
def canonicalNativeSymbol (arch : Arch) (contract : Contract)
    (declaration : String) : String :=
  match contract with
  | .scalar => declaration
  | .vector => declaration ++ vectorSuffix arch

/-- One concrete callee-map result, including the key used for its lookup. -/
structure Binding where
  lookupKey : String
  declarationName : String
  contract : Contract
  deriving BEq, DecidableEq, Repr

/-- Map lookup and AST declaration identity agree on one source-level name. -/
def CanonicalBinding (binding : Binding) : Prop :=
  binding.lookupKey ≠ "" ∧
    reservedSourceName binding.lookupKey = false ∧
    binding.declarationName = binding.lookupKey

instance (binding : Binding) : Decidable (CanonicalBinding binding) := by
  unfold CanonicalBinding
  infer_instance

/-- A canonical binding is stored at the requested key and has the requested
scalar or vector contract. -/
def Authorizes (contract : Contract) (key : String)
    (binding : Binding) : Prop :=
  CanonicalBinding binding ∧
    binding.lookupKey = key ∧
    binding.contract = contract

instance (contract : Contract) (key : String) (binding : Binding) :
    Decidable (Authorizes contract key binding) := by
  unfold Authorizes
  infer_instance

def Binding.authorizes (binding : Binding) (contract : Contract)
    (key : String) : Bool :=
  decide (Authorizes contract key binding)

/-- The lookup slots selected by the concrete resolver.

For `vector`, `exactSlot` is the map slot at the fully suffixed machine
symbol and `baseSlot` is the slot at `base`.  Production consults the base
only if the exact slot is absent. -/
inductive Request where
  | exact (nativeSymbol : String) (slot : Option Binding)
  | vector (nativeSymbol base : String)
      (exactSlot baseSlot : Option Binding)
  | malformed (nativeSymbol : String)
  deriving BEq, DecidableEq, Repr

def Request.nativeSymbol : Request → String
  | .exact nativeSymbol _ => nativeSymbol
  | .vector nativeSymbol _ _ _ => nativeSymbol
  | .malformed nativeSymbol => nativeSymbol

/-- Successful resolution contains the exact slot used, a canonical binding
of the required contract, and the precise native symbol it authorizes. -/
def Authorized (arch : Arch) (request : Request) (binding : Binding) : Prop :=
  match request with
  | .exact nativeSymbol slot =>
      slot = some binding ∧
        Authorizes .scalar nativeSymbol binding ∧
        nativeSymbol =
          canonicalNativeSymbol arch .scalar binding.declarationName
  | .vector nativeSymbol base exactSlot baseSlot =>
      exactSlot = none ∧
        baseSlot = some binding ∧
        Authorizes .vector base binding ∧
        nativeSymbol =
          canonicalNativeSymbol arch .vector binding.declarationName
  | .malformed _ => False

/-- Resolve according to production's exact-first policy. -/
def resolve (arch : Arch) : Request → Option Binding
  | .exact _ none => none
  | .exact nativeSymbol (some binding) =>
      if Authorizes .scalar nativeSymbol binding then some binding else none
  | .vector _ _ (some _) _ => none
  | .vector _ _ none none => none
  | .vector nativeSymbol base none (some binding) =>
      if nativeSymbol = canonicalNativeSymbol arch .vector base ∧
          Authorizes .vector base binding then
        some binding
      else
        none
  | .malformed _ => none

theorem authorizes_iff (binding : Binding) (contract : Contract)
    (key : String) :
    binding.authorizes contract key = true ↔
      Authorizes contract key binding := by
  simp [Binding.authorizes]

theorem authorizes_declaration_eq_key {binding : Binding}
    {contract : Contract} {key : String}
    (authorized : Authorizes contract key binding) :
    binding.declarationName = key :=
  authorized.1.2.2.trans authorized.2.1

/-- Soundness: accepted resolution returns exactly the declaration stored in
the selected slot and exactly its canonical native symbol. -/
theorem resolve_sound {arch : Arch} {request : Request} {binding : Binding}
    (accepted : resolve arch request = some binding) :
    Authorized arch request binding := by
  cases request with
  | malformed nativeSymbol => simp [resolve] at accepted
  | exact nativeSymbol slot =>
      cases slot with
      | none => simp [resolve] at accepted
      | some candidate =>
          simp only [resolve] at accepted
          split at accepted
          · rename_i authorized
            cases accepted
            refine ⟨rfl, authorized, ?_⟩
            have sameName := authorizes_declaration_eq_key authorized
            simpa [canonicalNativeSymbol] using sameName.symm
          · simp at accepted
  | vector nativeSymbol base exactSlot baseSlot =>
      cases exactSlot with
      | some shadow => simp [resolve] at accepted
      | none =>
          cases baseSlot with
          | none => simp [resolve] at accepted
          | some candidate =>
              simp only [resolve] at accepted
              split at accepted
              · rename_i admitted
                cases accepted
                refine ⟨rfl, rfl, admitted.2, ?_⟩
                have sameName := authorizes_declaration_eq_key admitted.2
                simpa [sameName] using admitted.1
              · simp at accepted

/-- A successful request has only one authorized result: both exact and base
lookups are single map slots, and vector fallback proves the exact slot empty. -/
theorem resolve_unique {arch : Arch} {request : Request} {binding other : Binding}
    (accepted : resolve arch request = some binding)
    (otherAuthorized : Authorized arch request other) :
    other = binding := by
  have authorized := resolve_sound accepted
  cases request with
  | malformed nativeSymbol => simp [Authorized] at otherAuthorized
  | exact nativeSymbol slot =>
      exact Option.some.inj (otherAuthorized.1.symm.trans authorized.1)
  | vector nativeSymbol base exactSlot baseSlot =>
      exact Option.some.inj (otherAuthorized.2.1.symm.trans authorized.2.1)

theorem resolve_canonical {arch : Arch} {request : Request} {binding : Binding}
    (accepted : resolve arch request = some binding) :
    CanonicalBinding binding := by
  have authorized := resolve_sound accepted
  cases request with
  | malformed nativeSymbol => simp [Authorized] at authorized
  | exact nativeSymbol slot => exact authorized.2.1.1
  | vector nativeSymbol base exactSlot baseSlot => exact authorized.2.2.1.1

theorem resolve_canonical_name {arch : Arch} {request : Request}
    {binding : Binding} (accepted : resolve arch request = some binding) :
    binding.declarationName = binding.lookupKey :=
  (resolve_canonical accepted).2.2

theorem resolve_name_not_reserved {arch : Arch} {request : Request}
    {binding : Binding} (accepted : resolve arch request = some binding) :
    reservedSourceName binding.declarationName = false := by
  have canonical := resolve_canonical accepted
  simpa [canonical.2.2] using canonical.2.1

/-- The request's machine symbol is precisely the resolved declaration's
canonical scalar or active-lane vector symbol. -/
theorem resolve_exact_native_symbol {arch : Arch} {request : Request}
    {binding : Binding} (accepted : resolve arch request = some binding) :
    request.nativeSymbol =
      canonicalNativeSymbol arch binding.contract binding.declarationName := by
  have authorized := resolve_sound accepted
  cases request with
  | malformed nativeSymbol => simp [Authorized] at authorized
  | exact nativeSymbol slot =>
      rw [authorized.2.1.2.2]
      exact authorized.2.2
  | vector nativeSymbol base exactSlot baseSlot =>
      rw [authorized.2.2.1.2.2]
      exact authorized.2.2.2

theorem resolve_scalar_symbol {arch : Arch} {nativeSymbol : String}
    {slot : Option Binding} {binding : Binding}
    (accepted : resolve arch (.exact nativeSymbol slot) = some binding) :
    nativeSymbol = binding.declarationName := by
  have exact := resolve_exact_native_symbol accepted
  have authorized := resolve_sound accepted
  rw [authorized.2.1.2.2] at exact
  simpa [Request.nativeSymbol, canonicalNativeSymbol] using exact

theorem resolve_vector_symbol {arch : Arch} {nativeSymbol base : String}
    {exactSlot baseSlot : Option Binding} {binding : Binding}
    (accepted : resolve arch
      (.vector nativeSymbol base exactSlot baseSlot) = some binding) :
    nativeSymbol = binding.declarationName ++ vectorSuffix arch := by
  have exact := resolve_exact_native_symbol accepted
  have authorized := resolve_sound accepted
  rw [authorized.2.2.1.2.2] at exact
  simpa [Request.nativeSymbol, canonicalNativeSymbol] using exact

/-! ## Executable correspondence pins -/

def scalarInc : Binding := ⟨"inc", "inc", .scalar⟩
def armVectorDot : Binding := ⟨"dot", "dot", .vector⟩
def rvVectorDot : Binding := ⟨"dot", "dot", .vector⟩

-- Scalar identity is architecture-independent.
example : resolve .arm64 (.exact "inc" (some scalarInc)) = some scalarInc := by
  native_decide
example : resolve .rv64 (.exact "inc" (some scalarInc)) = some scalarInc := by
  native_decide

-- Vector identity uses only the active lane's suffix and an empty exact slot.
example : resolve .arm64
    (.vector "dot_neon_abi" "dot" none (some armVectorDot)) =
    some armVectorDot := by native_decide
example : resolve .rv64
    (.vector "dot_rvv_abi" "dot" none (some rvVectorDot)) =
    some rvVectorDot := by native_decide
example : resolve .arm64
    (.vector "dot_rvv_abi" "dot" none (some armVectorDot)) = none := by
  native_decide
example : resolve .rv64
    (.vector "dot_neon_abi" "dot" none (some rvVectorDot)) = none := by
  native_decide

-- A map key may not alias a differently named declaration.
example : resolve .arm64
    (.exact "inc" (some ⟨"inc", "dec", .scalar⟩)) = none := by native_decide
example : resolve .rv64
    (.vector "dot_rvv_abi" "dot" none
      (some ⟨"dot", "other", .vector⟩)) = none := by native_decide

-- Both ABI suffixes are reserved from source names on every architecture.
example : reservedSourceName "user_neon_abi" = true := by native_decide
example : reservedSourceName "user_rvv_abi" = true := by native_decide
example : resolve .arm64
    (.exact "user_neon_abi"
      (some ⟨"user_neon_abi", "user_neon_abi", .scalar⟩)) = none := by
  native_decide
example : resolve .rv64
    (.exact "user_neon_abi"
      (some ⟨"user_neon_abi", "user_neon_abi", .scalar⟩)) = none := by
  native_decide

-- Any occupied exact-symbol slot shadows and rejects vector fallback, even
-- when the occupant is malformed rather than independently authorizing.
example : resolve .arm64
    (.vector "dot_neon_abi" "dot"
      (some ⟨"dot_neon_abi", "wrong", .scalar⟩)
      (some armVectorDot)) = none := by native_decide
example : resolve .rv64
    (.vector "dot_rvv_abi" "dot"
      (some ⟨"dot_rvv_abi", "", .scalar⟩)
      (some rvVectorDot)) = none := by native_decide

-- A canonical exact shadow is the ordinary ambiguity case and also rejects.
example : resolve .arm64
    (.vector "dot_neon_abi" "dot"
      (some ⟨"dot_neon_abi", "dot_neon_abi", .scalar⟩)
      (some armVectorDot)) = none := by native_decide

-- Missing, malformed, and contract-mismatched slots reject.
example : resolve .arm64 (.exact "inc" none) = none := by native_decide
example : resolve .arm64 (.malformed "inc") = none := by native_decide
example : resolve .arm64 (.exact "" (some ⟨"", "", .scalar⟩)) = none := by
  native_decide
example : resolve .arm64
    (.exact "inc" (some ⟨"inc", "", .scalar⟩)) = none := by native_decide
example : resolve .arm64
    (.vector "dot_neon_abi" "dot" none
      (some ⟨"dot", "dot", .scalar⟩)) = none := by native_decide
example : resolve .rv64
    (.exact "dot" (some ⟨"dot", "dot", .vector⟩)) = none := by native_decide
example : resolve .arm64
    (.vector "_neon_abi" "" none (some ⟨"", "", .vector⟩)) = none := by
  native_decide

end Oak.AssemblerCalleeIdentity
