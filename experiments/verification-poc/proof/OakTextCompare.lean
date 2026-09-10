import OakText
import Lean

/-! Test adapter only. Each corpus file holds DIMACS/LRAT texts labelled by the
    Go harness, on which compiled Oak has already agreed. The transliteration of
    the Oak decoder must return the same acceptance decision on every case, and
    so must the proved file model: three executables, one verdict. -/
open Lean OakVerification

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
    let transliterated := OakText.check c.cnf c.proof
    if transliterated != c.expected then
      throw (IO.userError s!"{c.name}: Oak transliteration={transliterated}, compiled Oak/Go={c.expected}")
    let model := CertificateFile.check c.cnf c.proof
    if model != transliterated then
      throw (IO.userError s!"{c.name}: file model={model}, Oak transliteration={transliterated}")
    if transliterated then accepted := accepted + 1
  return (cases.size, accepted)

def main (args : List String) : IO Unit := do
  if args.isEmpty then throw (IO.userError "usage: OakTextCompare CASES.json...")
  let mut total := 0
  let mut accepted := 0
  for path in args do
    let (n, a) ← compare path
    total := total + n
    accepted := accepted + a
  IO.println s!"Oak transliteration/file model/compiled Oak certificate files: {total} cases ({accepted} accepted, {total - accepted} rejected)"
