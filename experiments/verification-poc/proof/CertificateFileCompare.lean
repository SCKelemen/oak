import CertificateFile
import Lean

/-! Test adapter only. Each corpus file holds DIMACS/LRAT texts labelled by the
    Go harness, on which compiled Oak has already agreed. The proved file model
    must return the same acceptance decision on every case. -/
open Lean OakVerification.CertificateFile

structure TextCase where
  name : String
  cnf : String
  proof : String
  expected : Bool
  deriving FromJson

def compare (path : String) : IO (Nat × Nat) := do
  let json ← IO.ofExcept (Json.parse (← IO.FS.readFile path))
  let cases ← IO.ofExcept (fromJson? json : Except String (Array TextCase))
  if cases.isEmpty then throw (IO.userError s!"{path}: empty text corpus")
  let mut accepted := 0
  for c in cases do
    let actual := check c.cnf c.proof
    if actual != c.expected then
      throw (IO.userError s!"{c.name}: file model={actual}, Go/Oak={c.expected}")
    if actual then accepted := accepted + 1
  return (cases.size, accepted)

def main (args : List String) : IO Unit := do
  if args.isEmpty then throw (IO.userError "usage: CertificateFileCompare CASES.json...")
  let mut total := 0
  let mut accepted := 0
  for path in args do
    let (n, a) ← compare path
    total := total + n
    accepted := accepted + a
  IO.println s!"Oak/Go/Lean certificate files: {total} cases ({accepted} accepted, {total - accepted} rejected)"
