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
def erasePhantom (inst : Instance) : RuntimeRepresentation :=
  inst.runtime

/-- Rebinding only the phantom parameter leaves all other semantic/runtime facts
    unchanged. -/
def rebindPhantom (inst : Instance) (phantom : Nat) : Instance :=
  { inst with phantom := phantom }

/-- All instantiations of one phantom template have exactly the same runtime
    representation. -/
theorem instantiate_runtime_invariant (template : PhantomTemplate)
    (left right : Nat) :
    erasePhantom (instantiate template left) =
      erasePhantom (instantiate template right) := by
  rfl

/-- Rebinding phantom identity is representation-preserving. -/
theorem rebind_runtime_invariant (inst : Instance) (phantom : Nat) :
    erasePhantom (rebindPhantom inst phantom) = erasePhantom inst := by
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
theorem rebind_preserves_size (inst : Instance) (phantom : Nat) :
    (erasePhantom (rebindPhantom inst phantom)).size =
      (erasePhantom inst).size := by
  rfl

/-- Alignment is likewise independent of phantom identity. -/
theorem rebind_preserves_alignment (inst : Instance) (phantom : Nat) :
    (erasePhantom (rebindPhantom inst phantom)).alignment =
      (erasePhantom inst).alignment := by
  rfl

/-- Machine bit width is likewise independent of phantom identity. -/
theorem rebind_preserves_bits (inst : Instance) (phantom : Nat) :
    (erasePhantom (rebindPhantom inst phantom)).bits =
      (erasePhantom inst).bits := by
  rfl

/-- Rebinding twice keeps only the final static phantom identity while retaining
    the original runtime representation. -/
theorem rebind_last_wins (inst : Instance) (first second : Nat) :
    rebindPhantom (rebindPhantom inst first) second =
      rebindPhantom inst second := by
  rfl

end Oak.PhantomRepresentation
