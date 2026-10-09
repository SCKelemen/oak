import Init

/-! Classification of a restricted, exact textual clause grammar. This module
is not Sail's parser or generated decoder. Binding the embedded clause region
to the complete pinned file is a separately checked extraction boundary. -/
namespace Oak.ArmDecoderClassification

inductive Segment where
  | fixed (digits : String)
  | any (width : Nat)
  deriving Repr, BEq

structure Field where
  name : String
  width : Nat
  high : Nat
  low : Nat
  singleton : Bool
  deriving Repr, BEq

structure Clause where
  segments : List Segment
  index : Nat
  fields : List Field
  callee : String
  deriving Repr, BEq

/-- Conservative keyword exclusions for this restricted certificate grammar.
This is not a verified Sail lexer. -/
def reserved (s : String) : Bool :=
  let candidates : List String := match s.toList.head? with
    | some 'B' => ["Bool"]
    | some 'I' => ["Int"]
    | some 'N' => ["Nat"]
    | some 'O' => ["Order"]
    | some 'S' => ["SEE"]
    | some 'T' => ["Type"]
    | some 'a' => ["and", "as", "assert"]
    | some 'b' => ["bitzero", "bitone", "by", "bitfield", "backwards"]
    | some 'c' => ["config", "clause", "cast", "catch", "constraint", "constant", "configuration"]
    | some 'd' => ["dec", "default", "do", "downto"]
    | some 'e' => ["effect", "end", "enum", "else", "exit"]
    | some 'f' => ["false", "forall", "foreach", "function", "forwards", "from"]
    | some 'i' => ["if", "in", "inc", "impure", "instantiation", "impl", "import", "internal_plet", "internal_return", "internal_assume"]
    | some 'l' => ["let"]
    | some 'm' => ["match", "mapping", "monadic", "module", "mutual"]
    | some 'n' => ["newtype"]
    | some 'o' => ["op_code", "operator", "overload", "outcome"]
    | some 'p' => ["pure", "private"]
    | some 'r' => ["ref", "register", "return", "repeat"]
    | some 's' => ["scattered", "sizeof", "struct"]
    | some 't' => ["throw", "try", "then", "true", "type", "termination_measure", "to"]
    | some 'u' => ["undefined", "union", "until"]
    | some 'v' => ["var", "val"]
    | some 'w' => ["with", "when", "while"]
    | _ => []
  candidates.contains s

def identifier (s : String) : Bool :=
  let letter := fun c : Char => c.isAlpha && c.toNat < 128 || c == '_'
  match s.toList with
  | [] => false
  | h :: t => letter h && t.all (fun c => letter c || c.isDigit) && !reserved s

def Segment.width : Segment → Nat
  | .fixed s => s.length
  | .any n => n

def Segment.valid : Segment → Bool
  | .fixed s => !s.isEmpty && s.toList.all (fun c => c == '0' || c == '1')
  | .any n => n > 0 && n ≤ 32

def Segment.chunks : Segment → List String
  | .fixed s => ["0b", s]
  | .any n => ["_ : bits(", toString n, ")"]

def Field.valid (f : Field) : Bool :=
  identifier f.name && f.low ≤ f.high && f.high < 32 &&
  f.width == f.high - f.low + 1 && (!f.singleton || f.width == 1)

def Field.chunks (f : Field) : List String :=
  ["    ", f.name, " : bits(", toString f.width, ") = "] ++
  (if f.singleton then ["[op_code[", toString f.high, "]]"]
   else ["op_code[", toString f.high, " .. ", toString f.low, "]"]) ++ [";\n"]

def Clause.valid (c : Clause) : Bool :=
  c.segments.all Segment.valid && (c.segments.map Segment.width).sum == 32 &&
  c.fields.all (fun f => f.valid && f.name != c.callee) && identifier c.callee &&
  (c.fields.map Field.name).eraseDups == c.fields.map Field.name

def Clause.chunks (c : Clause) : List String :=
  ["function clause decode64 (("] ++
  ((c.segments.map Segment.chunks).intersperse [" @ "]).flatten ++
  [" as op_code) if SEE < ", toString c.index, ") = {\n    SEE = ", toString c.index, ";\n"] ++
  (c.fields.map Field.chunks).flatten ++ ["    ", c.callee, "("] ++
  (c.fields.map Field.name).intersperse ", " ++ [")\n}\n"]

/-- Every byte chunk, including all punctuation and whitespace, is checked.
The input is the complete clause represented as a sequence of string chunks. -/
def check (raw : List String) (c : Clause) : Bool := c.valid && c.chunks == raw

theorem check_sound {raw : List String} {c : Clause} (h : check raw c = true) :
    c.valid = true ∧ c.chunks = raw := by
  simpa [check, Bool.and_eq_true] using h

/-- Reassembling the checked chunks gives exactly the complete input clause;
this theorem requires no evaluation of a large concatenated string. -/
theorem checked_bytes {raw : List String} {c : Clause} (h : check raw c = true) :
    String.join c.chunks = String.join raw := congrArg String.join (check_sound h).2

def Segment.value : Segment → Nat
  | .fixed s => s.toList.foldl (fun n b => 2*n + if b == '1' then 1 else 0) 0
  | .any _ => 0

/-- Arguments represented by the admitted literal slice syntax, without
executing a Sail callee or asserting general Sail-expression equivalence. -/
def Field.extract (f : Field) (word : BitVec 32) : Nat :=
  (word.toNat / 2^f.low) % 2^f.width

def Clause.arguments (c : Clause) (word : BitVec 32) : List Nat :=
  c.fields.map (fun f => f.extract word)

def Clause.maskValue (c : Clause) : Nat × Nat :=
  c.segments.foldl (fun (m,v) s =>
    (m * 2^s.width + (match s with | .fixed _ => 2^s.width-1 | .any _ => 0),
     v * 2^s.width + s.value)) (0,0)

def Clause.matches (c : Clause) (word : BitVec 32) : Bool :=
  let (mask,value) := c.maskValue
  word &&& BitVec.ofNat 32 mask == BitVec.ofNat 32 value

structure Row where
  index : Nat
  mask : Nat
  value : Nat
  deriving Repr, BEq, DecidableEq

def Clause.row (c : Clause) : Row :=
  let (mask,value) := c.maskValue
  ⟨c.index,mask,value⟩

structure CheckedRow where
  raw : List String
  clause : Clause
  row : Row
  checked : check raw clause = true
  derived : clause.row = row

/-- No row can enter the checked table without both exact textual binding and
kernel-checked derivation of its mask from that same clause certificate. -/
theorem row_bound (a : CheckedRow) :
    a.clause.valid = true ∧ String.join a.clause.chunks = String.join a.raw ∧
    a.clause.row = a.row :=
  ⟨(check_sound a.checked).1, checked_bytes a.checked, a.derived⟩

def Row.matches (r : Row) (word : BitVec 32) : Bool :=
  word &&& BitVec.ofNat 32 r.mask == BitVec.ofNat 32 r.value

def choices (rows : List Row) (word : BitVec 32) (see : Int) : List Nat :=
  (rows.filter fun r => r.matches word && see < (r.index : Int)).map Row.index

/-- Ordered classification only; terminal callbacks are not executed. -/
def first (rows : List Row) (word : BitVec 32) (see : Int) : Option Nat :=
  (choices rows word see).head?

theorem choices_append (a b : List Row) (word : BitVec 32) (see : Int) :
    choices (a ++ b) word see = choices a word see ++ choices b word see := by
  simp [choices, List.filter_append, List.map_append]

end Oak.ArmDecoderClassification
