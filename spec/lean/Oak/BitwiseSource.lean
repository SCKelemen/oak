import Oak.BitwiseModule
import Oak.ByteFields

/-!
# Independently checked original-source slice

This module recognizes original ASCII bytes, not a Go AST or a source hash.
The grammar is intentionally canonical: single ASCII spaces, the identifier-first
colon-return two-u32 signature, one parameter-ordered bitwise expression, and a
single final LF. It is a strict subset, not a whole-Oak parser correctness claim.
The parser guesses fields then independently checks the full grammar expansion;
no unconsumed prefix, suffix, declaration, comment, or alternate type can pass.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Oak.BitwiseSource
open Oak.BitwiseFunction

abbrev Bytes := List UInt8

def ascii (s : String) : Bytes := s.toUTF8.toList

def letter (b : UInt8) : Bool :=
  (65 ≤ b.toNat && b.toNat ≤ 90) || (97 ≤ b.toNat && b.toNat ≤ 122)

/-- Deliberately excludes keywords and built-in type names, even where a
context would allow shadowing. Identifiers have only ASCII letters/digits
(no underscores, hence no internal-name or native-ABI-suffix collision).
The profile is narrower than general Oak. -/
def reserved : List Bytes :=
  (["type", "interface", "struct", "true", "false", "package", "import",
    "while", "break", "defer", "unsafe", "fn", "pub", "try", "return",
    "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64",
    "f32", "f64", "Bool", "bool", "string", "unit", "main",
    "int", "uint", "ptr", "uptr", "byte", "rune"] : List String).map ascii

def identifier (name : Bytes) : Bool :=
  match name with
  | [] => false
  | first :: rest => letter first && rest.all (fun b =>
      letter b || (48 ≤ b.toNat && b.toNat ≤ 57)) &&
      !reserved.contains name

structure Decl where
  name : Bytes
  first : Bytes
  second : Bytes
  op : Op
  deriving DecidableEq, Repr

def valid (d : Decl) : Bool :=
  identifier d.name && identifier d.first && identifier d.second &&
    decide (d.first ≠ d.second ∧ d.name ≠ d.first ∧ d.name ≠ d.second)

def symbol : Op → Bytes
  | .and => [38] | .or => [124] | .xor => [94]

/-- Canonical grammar expansion includes the actual referenced parameter names. -/
def render (d : Decl) : Bytes :=
  d.name ++ ascii ": (" ++ d.first ++ ascii ": u32, " ++ d.second ++
  ascii ": u32): u32 = " ++ d.first ++ ascii " " ++ symbol d.op ++
  ascii " " ++ d.second ++ [10]

/-- Declarative byte grammar, independent of the candidate-discovery algorithm. -/
inductive Grammar : Bytes → Decl → Prop where
  | function (d : Decl) (wellFormed : valid d = true) : Grammar (render d) d

private def parseOp : Bytes → Option Op
  | [38] => some .and | [124] => some .or | [94] => some .xor | _ => none

/-- Field discovery is untrusted until the complete grammar expansion agrees. -/
def candidate (source : Bytes) : Option Decl := do
  match Oak.ByteFields.splitOn source.dropLast 32 with
  | [name, first, _, second, _, _, _, _, operator, _] =>
      let op ← parseOp operator
      some ⟨name.dropLast, (first.drop 1).dropLast, second.dropLast, op⟩
  | _ => none

def parse (source : Bytes) : Option Decl := do
  let d ← candidate source
  if valid d && decide (source = render d) then some d else none

/-- Parsing success entails exact original-byte membership in the grammar.
Reconstruction is an equality checked in the kernel, not a hashing assumption. -/
theorem parse_sound {source : Bytes} {d : Decl} (h : parse source = some d) :
    Grammar source d := by
  unfold parse at h
  cases hc : candidate source with
  | none => simp [hc] at h
  | some parsed =>
      rw [hc] at h
      change (if valid parsed && decide (source = render parsed) then
        some parsed else none) = some d at h
      split at h
      next good =>
        have hd : parsed = d := Option.some.inj h
        subst parsed
        have both : valid d = true ∧ source = render d := by simpa using good
        rw [both.2]
        exact Grammar.function d both.1
      next => simp at h

theorem parse_exact {source : Bytes} {d : Decl} (h : parse source = some d) :
    source = render d := by
  cases parse_sound h
  rfl

/-- A name environment makes binding and parameter order explicit. -/
def environment (d : Decl) (left right : BitVec 32) (name : Bytes) : Option (BitVec 32) :=
  if name = d.first then some left else if name = d.second then some right else none

/-- The declared expression reads the named arguments before applying its operator. -/
def evaluate (d : Decl) (left right : BitVec 32) : Option (BitVec 32) := do
  let x ← environment d left right d.first
  let y ← environment d left right d.second
  some (eval d.op x y)

theorem grammar_evaluation {source : Bytes} {d : Decl} (h : Grammar source d)
    (left right : BitVec 32) : evaluate d left right = some (eval d.op left right) := by
  cases h with
  | function d good =>
      have distinct : d.first ≠ d.second := by
        exact (of_decide_eq_true (Bool.and_eq_true_iff.mp good).2).1
      simp [evaluate, environment, Ne.symm distinct]

/-- Source meaning includes grammar membership and named-variable evaluation. -/
def Means (source : Bytes) (d : Decl) (left right result : BitVec 32) : Prop :=
  Grammar source d ∧ evaluate d left right = some result

/-- Replaying a claim for a different name, parameter order, operator, source,
ABI, target, or complete module must pass all checks again. -/
def accepts (source : Bytes) (claim : Decl) (target : Target) (abi : ABI)
    (bytes : Bytes) : Bool :=
  decide (parse source = some claim) &&
    BitwiseModule.acceptsModule target abi [32,32] 32 claim.op claim.name bytes

/-- A changed original byte string cannot reuse the same declaration claim,
regardless of its effect on the parser or on mathematical equivalence. -/
theorem refuses_source_replay (source : Bytes) (claim : Decl)
    (target : Target) (abi : ABI) (bytes : Bytes) (changed : source ≠ render claim) :
    accepts source claim target abi bytes = false := by
  have refused : parse source ≠ some claim := fun h => changed (parse_exact h)
  simp [accepts, refused]

/-- For every source and actual module admitted by the independent checkers,
every input pair has a source meaning and a successful named-module result. -/
theorem accepted_source_to_module {source bytes : Bytes} {claim : Decl}
    {target : Target} {abi : ABI}
    (h : accepts source claim target abi bytes = true) (left right : BitVec 32) :
    Means source claim left right (eval claim.op left right) ∧
    BitwiseModule.invokeModule claim.name bytes left right = .ok (eval claim.op left right) := by
  have both := Bool.and_eq_true_iff.mp h
  have parsed : parse source = some claim := by simpa using both.1
  have grammar := parse_sound parsed
  exact ⟨⟨grammar, grammar_evaluation grammar left right⟩,
    BitwiseModule.admitted_module_success both.2 left right⟩

/-! Original-source mutation checks. Consistent renaming creates a new valid
source; replaying the old claim against it fails. Swapping parameters plus
references also changes identity even though these three operators commute. -/
def fixture (op : Op) : Decl := ⟨ascii "bitwise", ascii "x", ascii "y", op⟩

theorem fixture_op (op : Op) : (fixture op).op = op := rfl

theorem fixture_name (op : Op) : (fixture op).name = BitwiseModule.entryName := by
  cases op <;> decide +kernel

theorem fixture_parsed (op : Op) : parse (render (fixture op)) = some (fixture op) := by
  cases op <;> decide +kernel

theorem fixture_admitted (op : Op) :
    accepts (render (fixture op)) (fixture op) .wasm .wasmLocals
      (BitwiseModule.moduleBytes op) = true := by
  cases op <;> decide +kernel

example : parse (ascii "mix: (left0: u32, Right9: u32): u32 = left0 ^ Right9\n") =
    some ⟨ascii "mix", ascii "left0", ascii "Right9", .xor⟩ := by decide +kernel
example : parse (ascii "kernel: (forall: u32, exists: u32): u32 = forall | exists\n") =
    some ⟨ascii "kernel", ascii "forall", ascii "exists", .or⟩ := by decide +kernel

/-- Every byte mutation of this source fails replay against the original claim. -/
theorem source_mutations_refused (op : Op) :
    ((List.range (render (fixture op)).length).all fun index =>
      (List.range 8).all fun bit =>
        !(accepts ((render (fixture op)).set index
          ((render (fixture op)).getD index 0 ^^^ UInt8.ofNat (2^bit)))
          (fixture op) .wasm .wasmLocals (BitwiseModule.moduleBytes op))) = true := by
  cases op <;> decide +kernel

example : accepts (ascii "other: (x: u32, y: u32): u32 = x & y\n")
    (fixture .and) .wasm .wasmLocals (BitwiseModule.moduleBytes .and) = false := by decide +kernel
example : accepts (ascii "bitwise: (y: u32, x: u32): u32 = y & x\n")
    (fixture .and) .wasm .wasmLocals (BitwiseModule.moduleBytes .and) = false := by decide +kernel
example : parse (ascii "bitwise: (x: u64, y: u32): u32 = x & y\n") = none := by decide +kernel
example : parse (ascii "bitwise: (x: u32, y: u32): u64 = x & y\n") = none := by decide +kernel
example : parse (ascii "bitwise: (x: u32, x: u32): u32 = x & x\n") = none := by decide +kernel
example : parse (ascii "bitwise: (x: u32, y: u32): u32 = x & x\n") = none := by decide +kernel
example : parse (ascii "bitwise: (x: u32, y: u32): u32 = y & x\n") = none := by decide +kernel
example : parse (ascii "bitwise: (x: u32, y: u32): u32 = x & y;\n") = none := by decide +kernel
example : parse (ascii "bitwise: (x: u32, y: u32): u32 = x & y\r\n") = none := by decide +kernel
example : parse (render (fixture .and) ++ render (fixture .or)) = none := by decide +kernel
example : parse (render (fixture .and) ++ ascii "// comment\n") = none := by decide +kernel
example : parse (ascii "fn: (x: u32, y: u32): u32 = x & y\n") = none := by decide +kernel
example : parse (ascii "bitwise: (true: u32, y: u32): u32 = true & y\n") = none := by decide +kernel
example : parse (ascii "bitwise: (_: u32, y: u32): u32 = _ & y\n") = none := by decide +kernel
example : parse (ascii "bitwise: (x__a: u32, y: u32): u32 = x__a & y\n") = none := by decide +kernel
example : accepts (render (fixture .and)) (fixture .and) .rv64 .wasmLocals
    (BitwiseModule.moduleBytes .and) = false := by decide +kernel
example : accepts (render (fixture .and)) (fixture .and) .arm64 .wasmLocals
    (BitwiseModule.moduleBytes .and) = false := by decide +kernel
example : accepts (render (fixture .and)) (fixture .and) .wasm .native
    (BitwiseModule.moduleBytes .and) = false := by decide +kernel
example : accepts (render (fixture .and)) (fixture .and) .wasm .wasmLocals
    (BitwiseModule.moduleBytes .xor) = false := by decide +kernel
example : accepts (render (fixture .and)) (fixture .and) .wasm .wasmLocals
    ((BitwiseModule.moduleBytes .and).dropLast) = false := by decide +kernel

end Oak.BitwiseSource
