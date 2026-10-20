import Sail
open PreSail

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open ConcurrencyInterfaceV1

abbrev bit := (BitVec 1)

abbrev bits k_n := (BitVec k_n)

/-- Type quantifiers: k_a : Type -/
inductive option (k_a : Type) where
  | Some (_ : k_a)
  | None (_ : Unit)
  deriving Inhabited, BEq, Repr
  open option

abbrev Register := PEmpty
abbrev RegisterType : Register -> Type := PEmpty.elim

abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception

