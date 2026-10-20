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

inductive Register : Type where
  | TCR_EL3
  | TCR_EL2
  | TCR_EL1
  deriving DecidableEq, Hashable, Repr
open Register

abbrev RegisterType : Register → Type
  | .TCR_EL3 => (BitVec 32)
  | .TCR_EL2 => (BitVec 64)
  | .TCR_EL1 => (BitVec 64)

instance : Inhabited (RegisterRef RegisterType (BitVec 32)) where
  default := .Reg TCR_EL3
instance : Inhabited (RegisterRef RegisterType (BitVec 64)) where
  default := .Reg TCR_EL1
abbrev exception := Unit

abbrev SailM := PreSailM RegisterType trivialChoiceSource exception
abbrev SailME := PreSailME RegisterType trivialChoiceSource exception

