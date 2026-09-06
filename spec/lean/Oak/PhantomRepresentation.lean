namespace Oak.PhantomRepresentation

/-- Runtime representation facts are intentionally independent of phantom
    identity. This mirrors Semantic IR's separation between Type.Parameters and
    Definition.Representation. -/
structure RuntimeRepresentation where
  bits : Nat
  size : Nat
  alignment : Nat
  deriving DecidableEq, Repr

/-- A generic definition whose parameter is phantom: the template fixes nominal
    identity and machine representation, while each instantiation chooses only
    a static phantom identity. -/
structure PhantomTemplate where
  nominal : Nat
  runtime : RuntimeRepresentation
  deriving DecidableEq, Repr

/-- One static instantiation of a phantom-parameterized type. -/
structure Instance where
  nominal : Nat
  phantom : Nat
  runtime : RuntimeRepresentation
  deriving DecidableEq, Repr

def instantiate (template : PhantomTemplate) (phantom : Nat) : Instance :=
  { nominal := template.nominal
    phantom := phantom
    runtime := template.runtime }

/-- Runtime lowering erases phantom identity completely. -/
def erasePhantom (instance : Instance) : RuntimeRepresentation :=
  instance.runtime

/-- Rebinding only the phantom parameter leaves all other semantic/runtime facts
    unchanged. -/
def rebindPhantom (instance : Instance) (phantom : Nat) : Instance :=
  { instance with phantom := phantom }

/-- All instantiations of one phantom template have exactly the same runtime
    representation. -/
theorem instantiate_runtime_invariant (template : PhantomTemplate)
    (left right : Nat) :
    erasePhantom (instantiate template left) =
      erasePhantom (instantiate template right) := by
  rfl

/-- Rebinding phantom identity is representation-preserving. -/
theorem rebind_runtime_invariant (instance : Instance) (phantom : Nat) :
    erasePhantom (rebindPhantom instance phantom) = erasePhantom instance := by
  rfl

/-- Phantom identity still participates in static type identity. -/
theorem different_phantoms_are_distinct (template : PhantomTemplate)
    (left right : Nat) (hne : left ≠ right) :
    instantiate template left ≠ instantiate template right := by
  intro heq
  apply hne
  exact congrArg Instance.phantom heq

/-- The zero-runtime law covers the whole representation record, therefore size
    is unchanged under phantom rebinding. -/
theorem rebind_preserves_size (instance : Instance) (phantom : Nat) :
    (erasePhantom (rebindPhantom instance phantom)).size =
      (erasePhantom instance).size := by
  rfl

/-- Alignment is likewise independent of phantom identity. -/
theorem rebind_preserves_alignment (instance : Instance) (phantom : Nat) :
    (erasePhantom (rebindPhantom instance phantom)).alignment =
      (erasePhantom instance).alignment := by
  rfl

/-- Machine bit width is likewise independent of phantom identity. -/
theorem rebind_preserves_bits (instance : Instance) (phantom : Nat) :
    (erasePhantom (rebindPhantom instance phantom)).bits =
      (erasePhantom instance).bits := by
  rfl

/-- Rebinding twice keeps only the final static phantom identity while retaining
    the original runtime representation. -/
theorem rebind_last_wins (instance : Instance) (first second : Nat) :
    rebindPhantom (rebindPhantom instance first) second =
      rebindPhantom instance second := by
  rfl

end Oak.PhantomRepresentation
