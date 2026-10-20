import Oak.WasmNumericSource

/-!
UNTRUSTED numeric-only computation-certificate emitter, never part of the theorem
dependency closure. It proposes lexer checkpoints as JSON data, not Lean syntax.
The Go gate rejects malformed/bounded-schema violations and supplies all theorem
names, statements, and proof templates independently. Lean then rechecks each
transition of the unchanged unsplit lexer with an arbitrary suffix/accumulator,
exact full-byte reconstruction, and acceptance of the independent original bytes.
-/
open Oak.WasmNumericSource

private def files : List String :=
  ["0.1-aux.vars.spectec", "1.1-syntax.values.spectec", "1.2-syntax.types.spectec",
   "1.3-syntax.instructions.spectec", "3.1-numerics.scalar.spectec"]

private def chunks (bs : Bytes) : IO (List Bytes) := do
  if bs.getLast? != some 10 then throw (IO.userError "source must end at a complete line")
  let lines := (bs.splitOn 10).dropLast.map (fun line => line ++ [10])
  let mut result : List Bytes := []
  let mut chunk : Bytes := []
  for line in lines do
    if line.length > 1024 then throw (IO.userError "source line exceeds checkpoint bound")
    if chunk.length + line.length > 1024 && !chunk.isEmpty then
      result := chunk :: result
      chunk := []
    chunk := chunk ++ line
  if !chunk.isEmpty then result := chunk :: result
  return result.reverse

private def fuelUsed (bs : Bytes) : Nat := Id.run do
  let mut lo := 0
  let mut hi := bs.length + 1
  while lo < hi do
    let mid := (lo+hi)/2
    if (lexAux mid 0 0 [] bs).isSome then hi := mid else lo := mid+1
  return lo

private def jsonArray (items : List String) : String :=
  "[" ++ String.intercalate "," items ++ "]"

private def jsonBytes (bs : Bytes) : String :=
  jsonArray (bs.map toString)

private def jsonToken (t : Token) : String :=
  "{\"spelling\":" ++ jsonBytes t.spelling ++ ",\"start\":" ++ toString t.start ++
    ",\"stop\":" ++ toString t.stop ++ ",\"line\":" ++ toString t.line ++ "}"

private def emit (index : Nat) (bs : Bytes) : IO String := do
  let parts ← chunks bs
  let mut fuel := bs.length+1
  let mut offset := 0
  let mut line := 0
  let mut records : List String := []
  for part in parts do
    let ts ← match lexAux fuel offset line [] part with
      | some ts => pure ts
      | none => throw (IO.userError "unsupported source checkpoint")
    let used := fuelUsed part
    records := records ++ ["{\"index\":" ++ toString records.length ++ ",\"bytes\":" ++ jsonBytes part ++
      ",\"tokens\":" ++ jsonArray (ts.reverse.map jsonToken) ++
      ",\"fuel_used\":" ++ toString used ++ "}"]
    fuel := fuel-used
    offset := offset+part.length
    line := line+(part.filter (· == 10)).length
  return "{\"index\":" ++ toString index ++ ",\"chunks\":" ++ jsonArray records ++ "}"

/-- Only fixed-schema numeric JSON is emitted. File order and identities are
fixed; no source text, identifiers, expressions, or commands are emitted. -/
def main (args : List String) : IO UInt32 := do
  let directory ← match args with
    | [dir] => pure dir
    | _ => throw (IO.userError "usage: NumericCertificate.lean SOURCE_DIRECTORY")
  let mut records : List String := []
  for i in List.range files.length do
    let data ← IO.FS.readBinFile (System.FilePath.mk directory / System.FilePath.mk files[i]!)
    records := records ++ [← emit i (data.data.toList.map UInt8.toNat)]
  IO.println ("{\"version\":1,\"files\":" ++ jsonArray records ++ "}")
  return 0
