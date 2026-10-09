import Oak.WasmCoreBitwiseProjection

/-!
# Bounded source-byte reader for official scalar numeric dispatch

This is deliberately not a general SpecTec parser. Every byte of five dependency
files is lexed and every declaration head is owned. The protected footprint is
parsed into the typed syntax below; unsupported declarations in that footprint
fail closed. Other bodies are opaque, with declaration keywords fenced by the
lexer/owner reader. See spec/wasm-core/README.md for the remaining boundary.
-/
set_option autoImplicit false
namespace Oak.WasmNumericSource

/-- Exact octet values represented as naturals for inexpensive kernel reduction.
The lexer rejects non-ASCII values explicitly; no truncation or modular coercion
is used. File-loading code supplies each original byte's unchanged numeric value. -/
abbrev Bytes := List Nat

def ascii (s : String) : Bytes := s.toByteArray.data.toList.map UInt8.toNat

def isLetter (b : Nat) : Bool :=
  (Nat.ble 65 b && Nat.ble b 90) || (Nat.ble 97 b && Nat.ble b 122)
def isDigit (b : Nat) : Bool := Nat.ble 48 b && Nat.ble b 57
def isNumeral (b : Nat) : Bool := isDigit b || b == 95
def isHexDigit (b : Nat) : Bool := isDigit b || (Nat.ble 65 b && Nat.ble b 70)
def isHex (b : Nat) : Bool := isHexDigit b || b == 95
/-- Underscores may separate digits, never terminate a numeric token or stand
alone. Otherwise `0_def` could manufacture a false declaration boundary. -/
def digitTail (digit : Nat → Bool) : Bytes → Bool
  | [] => true
  | 95 :: [] => false
  | 95 :: d :: ds => digit d && digitTail digit ds
  | d :: ds => digit d && digitTail digit ds

def digitRun (digit : Nat → Bool) : Bytes → Bool
  | [] => false
  | d :: ds => digit d && digitTail digit ds

def isIdent (b : Nat) : Bool := isLetter b || isDigit b || b == 95 || b == 39
def isSpace (b : Nat) : Bool := b == 32 || b == 9 || b == 10 || b == 13

def text (bs : Bytes) : String := String.ofList (bs.map (fun b => Char.ofNat b))

structure Token where
  spelling : Bytes
  start : Nat
  stop : Nat
  line : Nat
  deriving BEq, DecidableEq, Repr

/-- Consume a quoted ASCII string. Escapes and newlines are unsupported and fail
closed; none occurs in the pinned dependencies. Quotes remain in the token, so a
string cannot become a declaration keyword. -/
def quoted : Bytes → Option (Bytes × Bytes)
  | [] => none
  | b :: bs =>
    if b == 34 then some ([b], bs)
    else if b == 92 || b == 10 || b == 13 || Nat.blt b 32 || Nat.blt 126 b then none
    else do
      let (front, rest) ← quoted bs
      some (b :: front, rest)

/-- Complete pinned symbolic-token family ending in identifier characters.
Without longest-match fencing, e.g. `_ |_def` without spaces could hide a
following `def` inside an opaque identifier. -/
def identifierEndingSymbol : Bytes → Option Bytes
  | 126 :: 62 :: 42 :: 95 :: _ => some [126,62,42,95]
  | 61 :: 61 :: 95 :: _ => some [61,61,95]
  | 126 :: 126 :: 95 :: _ => some [126,126,95]
  | 45 :: 62 :: 95 :: _ => some [45,62,95]
  | 61 :: 62 :: 95 :: _ => some [61,62,95]
  | 126 :: 62 :: 95 :: _ => some [126,62,95]
  | 60 :: 60 :: 95 :: _ => some [60,60,95]
  | 62 :: 62 :: 95 :: _ => some [62,62,95]
  | 124 :: 45 :: 95 :: _ => some [124,45,95]
  | 45 :: 124 :: 95 :: _ => some [45,124,95]
  | 95 :: 124 :: 95 :: _ => some [95,124,95]
  | 58 :: 95 :: _ => some [58,95]
  | 61 :: 95 :: _ => some [61,95]
  | _ => none

/-- Fuel is supplied from the full byte length, never by a caller-controlled
span. Each successful recursive step consumes at least one original byte. -/
def lexAux : Nat → Nat → Nat → List Token → Bytes → Option (List Token)
  | 0, _, _, acc, [] => some acc.reverse
  | 0, _, _, _, _ => none
  | _ + 1, _, _, acc, [] => some acc.reverse
  | fuel + 1, offset, line, acc, b :: bs => do
    if isSpace b then lexAux fuel (offset+1) (line + if b == 10 then 1 else 0) acc bs
    else if b == 59 && bs.head? == some 59 then
      let comment := bs.takeWhile (· != 10)
      if !(comment.all (fun c => Nat.ble c 127)) then none else
      lexAux fuel (offset + 1 + comment.length) line acc (bs.drop comment.length)
    else if b == 34 then
      let (s, rest) ← quoted bs
      lexAux fuel (offset + 1 + s.length) line (⟨b :: s, offset, offset + 1 + s.length, line⟩ :: acc) rest
    else if Nat.blt b 32 || Nat.blt 126 b || b == 59 then none
    else if b == 40 && bs.head? == some 59 then none
    else if b == 37 && bs.take 5 == [108,97,116,101,120] then none
    else if (identifierEndingSymbol (b :: bs)).isSome then
      let symbol := (identifierEndingSymbol (b :: bs)).getD []
      lexAux fuel (offset+symbol.length) line (⟨symbol, offset, offset+symbol.length, line⟩ :: acc) ((b :: bs).drop symbol.length)
    else if b == 46 && bs.take 2 == [46,46] then
      lexAux fuel (offset+3) line (⟨[46,46,46], offset, offset+3, line⟩ :: acc) (bs.drop 2)
    else if b == 45 && bs.head? == some 45 then
      lexAux fuel (offset+2) line (⟨[45,45], offset, offset+2, line⟩ :: acc) bs.tail
    else if b == 37 && (bs.head?.map isDigit).getD false then
      let digits := bs.takeWhile isNumeral
      if !digitRun isDigit digits then none else
      lexAux fuel (offset+1+digits.length) line (⟨b :: digits, offset, offset+1+digits.length, line⟩ :: acc) (bs.drop digits.length)
    else if b == 36 && bs.take 4 == [110,97,116,36] then
      lexAux fuel (offset+5) line (⟨[36,110,97,116,36], offset, offset+5, line⟩ :: acc) (bs.drop 4)
    else if b == 85 && bs.head? == some 43 then
      let digits := bs.tail.takeWhile isHex
      if !digitRun isHexDigit digits then none else
      lexAux fuel (offset+2+digits.length) line (⟨[b,43] ++ digits, offset, offset+2+digits.length, line⟩ :: acc) (bs.tail.drop digits.length)
    else if b == 48 && bs.head? == some 120 then
      let digits := bs.tail.takeWhile isHex
      if !digitRun isHexDigit digits then none else
      lexAux fuel (offset+2+digits.length) line (⟨[b,120] ++ digits, offset, offset+2+digits.length, line⟩ :: acc) (bs.tail.drop digits.length)
    else if isDigit b then
      let digits := b :: bs.takeWhile isNumeral
      if !digitRun isDigit digits then none else
      lexAux fuel (offset+digits.length) line (⟨digits, offset, offset+digits.length, line⟩ :: acc) (bs.drop (digits.length-1))
    else if isLetter b || b == 95 then
      let word := b :: bs.takeWhile isIdent
      let rest := bs.drop (word.length - 1)
      if word == [104,105,110,116] then
        if rest.head? == some 40 then
          lexAux fuel (offset + word.length + 1) line (⟨[104,105,110,116,40], offset, offset + word.length + 1, line⟩ :: acc) rest.tail
        else none
      else
        lexAux fuel (offset + word.length) line (⟨word, offset, offset + word.length, line⟩ :: acc) rest
    else
      lexAux fuel (offset+1) line (⟨[b], offset, offset+1, line⟩ :: acc) bs

def lex (bs : Bytes) : Option (List Token) := lexAux (bs.length + 1) 0 0 [] bs

inductive File where
  | variables | values | types | instructions | numerics
  deriving BEq, DecidableEq, Repr

structure Bundle where
  variables : Bytes
  values : Bytes
  types : Bytes
  instructions : Bytes
  numerics : Bytes
  deriving BEq, DecidableEq, Repr

inductive Kind where
  | syntax | definition | variable
  deriving BEq, DecidableEq, Repr

structure Block where
  kind : Kind
  owner : Bytes
  tokens : List String
  rawTokens : List Token
  start : Nat
  stop : Nat
  deriving BEq, DecidableEq, Repr

def startsDeclaration (s : Bytes) : Bool := s == ascii "syntax" || s == ascii "def" || s == ascii "var"

/-- These are the complete other top-level declaration keywords in the pinned
SpecTec parser. We do not silently skip them. -/
def forbiddenKeyword (s : Bytes) : Bool :=
  s == ascii "grammar" || s == ascii "relation" || s == ascii "rule"

/-- Owners whose declaration could change parsing or interpretation of this
footprint, including constructor-to-variable reclassification. Suffixes are
removed separately, as in SpecTec's identifier environment. -/
def protectedNames : List Bytes :=
  [
    [117,78], -- uN
    [105,78], -- iN
    [110,117,109,116,121,112,101], -- numtype
    [73,110,110], -- Inn
    [70,110,110], -- Fnn
    [110,117,109], -- num
    [98,105,110,111,112], -- binop
    [115,105,122,101], -- size
    [115,105,122,101,110,110], -- sizenn
    [105,97,110,100], -- iand
    [105,111,114], -- ior
    [105,120,111,114], -- ixor
    [110,116], -- nt
    [78], -- N
    [105], -- i
    [73,51,50], -- I32
    [73,54,52], -- I64
    [70,51,50], -- F32
    [70,54,52], -- F64
    [65,78,68], -- AND
    [79,82], -- OR
    [88,79,82], -- XOR
    [65,68,68], -- ADD
    [83,85,66], -- SUB
    [77,85,76], -- MUL
    [68,73,86], -- DIV
    [82,69,77], -- REM
    [83,72,76], -- SHL
    [83,72,82], -- SHR
    [82,79,84,76], -- ROTL
    [82,79,84,82], -- ROTR
    [77,73,78], -- MIN
    [77,65,88], -- MAX
    [67,79,80,89,83,73,71,78], -- COPYSIGN
    [110,97,116], -- nat
    [105,110,116], -- int
    [115,120], -- sx
    [102], -- f
    [85], -- U
    [83] -- S
  ]

def baseName (s : Bytes) : Bytes := s.takeWhile (fun b => b != 95 && b != 39)

def isProtected (s : Bytes) : Bool := protectedNames.contains (baseName s)

/-- Backticks force lexical identifier classes upstream. Refuse escaped
protected identifiers rather than silently giving them a different owner. -/
def tokensSafe : List Token → Bool
  | [] => true
  | a :: rest =>
    !forbiddenKeyword a.spelling &&
    (a.spelling != ascii "`" || !(rest.head?.map (fun t => isProtected t.spelling)).getD false) &&
    ((a.spelling != ascii "`" && a.spelling != ascii "." && a.spelling != [45,45] &&
      a.spelling != [47] && a.spelling != [45]) ||
      !(rest.head?.map (fun t => startsDeclaration t.spelling || forbiddenKeyword t.spelling)).getD false) &&
    tokensSafe rest

/-- One exception to a declaration-keyword fence: the pinned higher-order
`syntax list(syntax X)` header. It cannot bind any protected identifier. -/
def bodyTokens (ts : List Token) : List Token × List Token :=
  let front :=  ts.takeWhile (fun t => !startsDeclaration t.spelling)
  (front, ts.drop front.length)

def readBlocksAux : Nat → List Token → Option (List Block)
  | 0, [] => some []
  | 0, _ => none
  | _+1, [] => some []
  | fuel+1, head :: rest => do
    let (kind, ownerBytes, afterHead, header) ←
      if head.spelling == ascii "def" then
        match rest with
        | dollar :: name :: tail =>
          if dollar.spelling == ascii "$" then some (Kind.definition, name.spelling, tail, [dollar,name]) else none
        | _ => none
      else if head.spelling == ascii "syntax" then
        match rest with
        | name :: left :: syn :: x :: right :: tail =>
          if name.spelling == ascii "list" && left.spelling == ascii "(" && syn.spelling == ascii "syntax" &&
              x.spelling == ascii "X" && right.spelling == ascii ")" then
            some (Kind.syntax, name.spelling, tail, [name,left,syn,x,right])
          else some (Kind.syntax, name.spelling, left :: syn :: x :: right :: tail, [name])
        | name :: tail => some (Kind.syntax, name.spelling, tail, [name])
        | _ => none
      else if head.spelling == ascii "var" then
        match rest with
        | name :: tail => some (Kind.variable, name.spelling, tail, [name])
        | _ => none
      else none
    let owner := ownerBytes
    -- An escaped name or punctuation cannot masquerade as an opaque owner.
    if !(ownerBytes.all isIdent) || ownerBytes.isEmpty ||
        startsDeclaration ownerBytes || forbiddenKeyword ownerBytes then none else
    let (body, following) := bodyTokens afterHead
    let all := head :: header ++ body
    let tail ← readBlocksAux fuel following
    some (⟨kind, owner, all.map (fun t => text t.spelling), all, head.start,
      (all.getLast?).map Token.stop |>.getD head.stop⟩ :: tail)

def readBlocks (bs : Bytes) : Option (List Block) := do
  let ts ← lex bs
  if tokensSafe ts then readBlocksAux (ts.length+1) ts else none

inductive NumType where
  | i32 | i64 | f32 | f64
  deriving BEq, DecidableEq, Repr
inductive Domain where
  | integer | floating
  deriving BEq, DecidableEq, Repr
inductive OtherOperator where
  | add | sub | mul | div | rem | shl | shr | rotl | rotr | min | max | copysign
  deriving BEq, DecidableEq, Repr
inductive Primitive where
  | iand | ior | ixor
  deriving BEq, DecidableEq, Repr
inductive Operand where
  | first | second
  deriving BEq, DecidableEq, Repr
inductive Width where
  | sizenn | literal (n : Nat)
  deriving BEq, DecidableEq, Repr

structure Dispatch where
  op : Oak.BitwiseFunction.Op
  primitive : Primitive
  width : Width
  first : Operand
  second : Operand
  deriving BEq, DecidableEq, Repr

/-- Required domain, membership, signature and width declarations, plus genuine
parsed dispatch expression nodes. Builtins have no algorithm node. -/
inductive Decl where
  | widthVariable | unsignedDomain | integerDomain
  | numberTypes | integerTypes | floatTypes | numberVariable
  | sizeSignature | sizeCase (type : NumType) (width : Nat)
  | sizennSignature | sizennEquation
  | numberSignature | integerNumbers | floatNumbers
  | signedness | operatorSignature | integerOperators | floatOperators
  | primitiveSignature (primitive : Primitive) | builtin (primitive : Primitive)
  | dispatchSignature | dispatch (equation : Dispatch)
  | otherDispatch (type : Domain) (operator : OtherOperator)
  deriving BEq, DecidableEq, Repr

structure Owned where
  file : File
  declaration : Decl
  deriving BEq, DecidableEq, Repr

def primitive : Oak.BitwiseFunction.Op → Primitive
  | .and => .iand | .or => .ior | .xor => .ixor

def equation (op : Oak.BitwiseFunction.Op) : Dispatch :=
  ⟨op, primitive op, .sizenn, .first, .second⟩

def parseOp : String → Option Oak.BitwiseFunction.Op
  | "AND" => some .and | "OR" => some .or | "XOR" => some .xor | _ => none

def parsePrimitive : String → Option Primitive
  | "iand_" => some .iand | "ior_" => some .ior | "ixor_" => some .ixor | _ => none

def parseOperand : String → Option Operand
  | "i_1" => some .first | "i_2" => some .second | _ => none

/-- Relevant declarations must preserve SpecTec's name-parenthesis adjacency
and cannot contain significant blank-line gaps. This is intentionally stricter
than the full grammar. Spans always originate in the complete-file lexer. -/
def validGaps : List Token → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest =>
    Nat.ble a.stop b.start &&
    Nat.ble (b.line - a.line) 1 &&
    (b.spelling != ascii "(" || !(a.spelling.all isIdent) || a.stop == b.start) &&
    validGaps (b :: rest)

/-- AST construction is from the checked original tokens, not proposed
extractor constants. Each form consumes the complete owned declaration. -/
def parseDispatch (ts : List String) : Option Dispatch := do
  match ts with
  | ["def", "$", "binop_", "(", "Inn", ",", op, ",", "i_1", ",", "i_2", ")", "=",
      "$", p, "(", "$", "sizenn", "(", "Inn", ")", ",", a, ",", b, ")"] =>
    some ⟨← parseOp op, ← parsePrimitive p, .sizenn, ← parseOperand a, ← parseOperand b⟩
  | ["def", "$", "binop_", "(", "Inn", ",", op, ",", "i_1", ",", "i_2", ")", "=",
      "$", p, "(", n, ",", a, ",", b, ")"] =>
    some ⟨← parseOp op, ← parsePrimitive p, .literal (← match n with | "32" => some 32 | "64" => some 64 | _ => none), ← parseOperand a, ← parseOperand b⟩
  | _ => none

/-- Pre-tokenized grammar productions avoid re-lexing grammar constants in each
kernel reduction. These are grammar rules, not extracted source evidence. -/
def canonicalForms : List (List String × Decl) :=
  [(["syntax", "N", "hint(", "macro", "none", ")", "=", "nat"], .widthVariable),
 (["syntax", "sx", "hint(", "desc", "\"signedness\"", ")", "=", "U", "|", "S"], .signedness),
 (["syntax", "uN", "(", "N", ")", "hint(", "desc", "\"unsigned integer\"", ")", "hint(", "show", "u", "#", "%", ")",
   "hint(", "macro", "\"uNX\"", ")", "=", "0", "|", "...", "|", "$nat$", "(", "2", "^", "N", "-", "1", ")"],
  .unsignedDomain),
 (["syntax", "iN", "(", "N", ")", "hint(", "desc", "\"integer\"", ")", "hint(", "show", "i", "#", "%", ")", "hint(",
   "macro", "\"iNX\"", ")", "=", "uN", "(", "N", ")"],
  .integerDomain),
 (["syntax", "numtype", "hint(", "desc", "\"number type\"", ")", "=", "|", "I32", "|", "I64", "|", "F32", "|", "F64"],
  .numberTypes),
 (["syntax", "Inn", "hint(", "show", "I", "#", "N", ")", "hint(", "macro", "\"nt%\"", ")", "=", "I32", "|", "I64"],
  .integerTypes),
 (["syntax", "Fnn", "hint(", "show", "F", "#", "N", ")", "hint(", "macro", "\"nt%\"", ")", "=", "F32", "|", "F64"],
  .floatTypes),
 (["var", "nt", ":", "numtype"], .numberVariable),
 (["def", "$", "size", "(", "numtype", ")", ":", "nat", "hint(", "show", "|", "%", "|", ")"],
  .sizeSignature),
 (["def", "$", "size", "(", "I32", ")", "=", "32"],
  .sizeCase (Oak.WasmNumericSource.NumType.i32) 32),
 (["def", "$", "size", "(", "I64", ")", "=", "64"],
  .sizeCase (Oak.WasmNumericSource.NumType.i64) 64),
 (["def", "$", "size", "(", "F32", ")", "=", "32"],
  .sizeCase (Oak.WasmNumericSource.NumType.f32) 32),
 (["def", "$", "size", "(", "F64", ")", "=", "64"],
  .sizeCase (Oak.WasmNumericSource.NumType.f64) 64),
 (["def", "$", "sizenn", "(", "numtype", ")", ":", "nat", "hint(", "show", "N", ")", "hint(", "macro", "none", ")"],
  .sizennSignature),
 (["def", "$", "sizenn", "(", "nt", ")", "=", "$", "size", "(", "nt", ")"], .sizennEquation),
 (["syntax", "num_", "(", "numtype", ")"], .numberSignature),
 (["syntax", "num_", "(", "Inn", ")", "=", "iN", "(", "$", "sizenn", "(", "Inn", ")", ")"],
  .integerNumbers),
 (["syntax", "num_", "(", "Fnn", ")", "=", "fN", "(", "$", "sizenn", "(", "Fnn", ")", ")"],
  .floatNumbers),
 (["syntax", "binop_", "(", "numtype", ")"], .operatorSignature),
 (["syntax", "binop_", "(", "Inn", ")", "=", "|", "ADD", "|", "SUB", "|", "MUL", "|", "DIV", "sx", "hint(", "show",
   "DIV", "#", "_", "#", "%", ")", "|", "REM", "sx", "hint(", "show", "REM", "#", "_", "#", "%", ")", "|", "AND", "|",
   "OR", "|", "XOR", "|", "SHL", "|", "SHR", "sx", "hint(", "show", "SHR", "#", "_", "#", "%", ")", "|", "ROTL", "|",
   "ROTR"],
  .integerOperators),
 (["syntax", "binop_", "(", "Fnn", ")", "=", "|", "ADD", "|", "SUB", "|", "MUL", "|", "DIV", "|", "MIN", "hint(",
   "macro", "\"FMIN\"", ")", "|", "MAX", "hint(", "macro", "\"FMAX\"", ")", "|", "COPYSIGN"],
  .floatOperators),
 (["def", "$", "iand_", "(", "N", ",", "iN", "(", "N", ")", ",", "iN", "(", "N", ")", ")", ":", "iN", "(", "N", ")"],
  .primitiveSignature (Oak.WasmNumericSource.Primitive.iand)),
 (["def", "$", "ior_", "(", "N", ",", "iN", "(", "N", ")", ",", "iN", "(", "N", ")", ")", ":", "iN", "(", "N", ")"],
  .primitiveSignature (Oak.WasmNumericSource.Primitive.ior)),
 (["def", "$", "ixor_", "(", "N", ",", "iN", "(", "N", ")", ",", "iN", "(", "N", ")", ")", ":", "iN", "(", "N", ")"],
  .primitiveSignature (Oak.WasmNumericSource.Primitive.ixor)),
 (["def", "$", "iand_", "hint(", "builtin", ")"],
  .builtin (Oak.WasmNumericSource.Primitive.iand)),
 (["def", "$", "ior_", "hint(", "builtin", ")"],
  .builtin (Oak.WasmNumericSource.Primitive.ior)),
 (["def", "$", "ixor_", "hint(", "builtin", ")"],
  .builtin (Oak.WasmNumericSource.Primitive.ixor)),
 (["def", "$", "binop_", "(", "numtype", ",", "binop_", "(", "numtype", ")", ",", "num_", "(", "numtype", ")", ",",
   "num_", "(", "numtype", ")", ")", ":", "num_", "(", "numtype", ")", "*", "hint(", "show", "%2", "#", "$", "_", "(",
   "%1", ",", "%3", ",", "%4", ")", ")"],
  .dispatchSignature),
 (["def", "$", "binop_", "(", "Inn", ",", "ADD", ",", "i_1", ",", "i_2", ")", "=", "$", "iadd_", "(", "$", "sizenn",
   "(", "Inn", ")", ",", "i_1", ",", "i_2", ")"],
  .otherDispatch .integer .add),
 (["def", "$", "binop_", "(", "Inn", ",", "SUB", ",", "i_1", ",", "i_2", ")", "=", "$", "isub_", "(", "$", "sizenn",
   "(", "Inn", ")", ",", "i_1", ",", "i_2", ")"],
  .otherDispatch .integer .sub),
 (["def", "$", "binop_", "(", "Inn", ",", "MUL", ",", "i_1", ",", "i_2", ")", "=", "$", "imul_", "(", "$", "sizenn",
   "(", "Inn", ")", ",", "i_1", ",", "i_2", ")"],
  .otherDispatch .integer .mul),
 (["def", "$", "binop_", "(", "Inn", ",", "SHL", ",", "i_1", ",", "i_2", ")", "=", "$", "ishl_", "(", "$", "sizenn",
   "(", "Inn", ")", ",", "i_1", ",", "i_2", ")"],
  .otherDispatch .integer .shl),
 (["def", "$", "binop_", "(", "Inn", ",", "ROTL", ",", "i_1", ",", "i_2", ")", "=", "$", "irotl_", "(", "$", "sizenn",
   "(", "Inn", ")", ",", "i_1", ",", "i_2", ")"],
  .otherDispatch .integer .rotl),
 (["def", "$", "binop_", "(", "Inn", ",", "ROTR", ",", "i_1", ",", "i_2", ")", "=", "$", "irotr_", "(", "$", "sizenn",
   "(", "Inn", ")", ",", "i_1", ",", "i_2", ")"],
  .otherDispatch .integer .rotr),
 (["def", "$", "binop_", "(", "Inn", ",", "DIV", "sx", ",", "i_1", ",", "i_2", ")", "=", "$", "idiv_", "(", "$",
   "sizenn", "(", "Inn", ")", ",", "sx", ",", "i_1", ",", "i_2", ")"],
  .otherDispatch .integer .div),
 (["def", "$", "binop_", "(", "Inn", ",", "REM", "sx", ",", "i_1", ",", "i_2", ")", "=", "$", "irem_", "(", "$",
   "sizenn", "(", "Inn", ")", ",", "sx", ",", "i_1", ",", "i_2", ")"],
  .otherDispatch .integer .rem),
 (["def", "$", "binop_", "(", "Inn", ",", "SHR", "sx", ",", "i_1", ",", "i_2", ")", "=", "$", "ishr_", "(", "$",
   "sizenn", "(", "Inn", ")", ",", "sx", ",", "i_1", ",", "i_2", ")"],
  .otherDispatch .integer .shr),
 (["def", "$", "binop_", "(", "Fnn", ",", "ADD", ",", "f_1", ",", "f_2", ")", "=", "$", "fadd_", "(", "$", "sizenn",
   "(", "Fnn", ")", ",", "f_1", ",", "f_2", ")"],
  .otherDispatch .floating .add),
 (["def", "$", "binop_", "(", "Fnn", ",", "SUB", ",", "f_1", ",", "f_2", ")", "=", "$", "fsub_", "(", "$", "sizenn",
   "(", "Fnn", ")", ",", "f_1", ",", "f_2", ")"],
  .otherDispatch .floating .sub),
 (["def", "$", "binop_", "(", "Fnn", ",", "MUL", ",", "f_1", ",", "f_2", ")", "=", "$", "fmul_", "(", "$", "sizenn",
   "(", "Fnn", ")", ",", "f_1", ",", "f_2", ")"],
  .otherDispatch .floating .mul),
 (["def", "$", "binop_", "(", "Fnn", ",", "DIV", ",", "f_1", ",", "f_2", ")", "=", "$", "fdiv_", "(", "$", "sizenn",
   "(", "Fnn", ")", ",", "f_1", ",", "f_2", ")"],
  .otherDispatch .floating .div),
 (["def", "$", "binop_", "(", "Fnn", ",", "MIN", ",", "f_1", ",", "f_2", ")", "=", "$", "fmin_", "(", "$", "sizenn",
   "(", "Fnn", ")", ",", "f_1", ",", "f_2", ")"],
  .otherDispatch .floating .min),
 (["def", "$", "binop_", "(", "Fnn", ",", "MAX", ",", "f_1", ",", "f_2", ")", "=", "$", "fmax_", "(", "$", "sizenn",
   "(", "Fnn", ")", ",", "f_1", ",", "f_2", ")"],
  .otherDispatch .floating .max),
 (["def", "$", "binop_", "(", "Fnn", ",", "COPYSIGN", ",", "f_1", ",", "f_2", ")", "=", "$", "fcopysign_", "(", "$",
   "sizenn", "(", "Fnn", ")", ",", "f_1", ",", "f_2", ")"],
  .otherDispatch .floating .copysign)]

def parseDecl (b : Block) : Option (Option Decl) := do
  if !(if b.kind == .definition then
      [[115,105,122,101], [115,105,122,101,110,110], [98,105,110,111,112],
       [105,97,110,100], [105,111,114], [105,120,111,114]].contains (baseName b.owner)
    else isProtected b.owner) then some none else
  if !validGaps b.rawTokens then none else
  let ts := b.tokens
  match parseDispatch ts with
  | some d => some (some (.dispatch d))
  | none =>
    match canonicalForms.find? (fun form => form.1 == ts) with
    | some form => some (some form.2)
    | none => none

def parseFile (file : File) (bs : Bytes) : Option (List Owned) := do
  let blocks ← readBlocks bs
  let declarations ← blocks.mapM parseDecl
  some ((declarations.filterMap id).map (fun d => ⟨file, d⟩))

def parse (source : Bundle) : Option (List Owned) := do
  some ((← parseFile .variables source.variables) ++ (← parseFile .values source.values) ++ (← parseFile .types source.types) ++
    (← parseFile .instructions source.instructions) ++ (← parseFile .numerics source.numerics))

def expected : List Owned :=
  [⟨.variables, .widthVariable⟩] ++
  ([.unsignedDomain, .integerDomain].map (Owned.mk .values)) ++
  ([.numberTypes, .integerTypes, .floatTypes, .numberVariable, .sizeSignature,
    .sizeCase .i32 32, .sizeCase .i64 64, .sizeCase .f32 32, .sizeCase .f64 64,
    .sizennSignature, .sizennEquation].map (Owned.mk .types)) ++
  ([.numberSignature, .integerNumbers, .floatNumbers, .signedness, .operatorSignature,
    .integerOperators, .floatOperators].map (Owned.mk .instructions)) ++
  ([.primitiveSignature .iand, .primitiveSignature .ior, .primitiveSignature .ixor,
    .builtin .iand, .builtin .ior, .builtin .ixor, .dispatchSignature,
    .otherDispatch .integer .add, .otherDispatch .integer .sub, .otherDispatch .integer .mul,
    .otherDispatch .integer .div, .otherDispatch .integer .rem,
    .dispatch (equation .and), .dispatch (equation .or), .dispatch (equation .xor),
    .otherDispatch .integer .shl, .otherDispatch .integer .shr, .otherDispatch .integer .rotl,
    .otherDispatch .integer .rotr, .otherDispatch .floating .add, .otherDispatch .floating .sub,
    .otherDispatch .floating .mul, .otherDispatch .floating .div, .otherDispatch .floating .min,
    .otherDispatch .floating .max, .otherDispatch .floating .copysign].map (Owned.mk .numerics))

/-- Ordered ownership equality checks the complete multiset as well as source
file identity. Missing, additional, moved and duplicate declarations all fail. -/
def accepts (source : Bundle) : Bool := decide (parse source = some expected)

theorem accepts_parse {source : Bundle} (h : accepts source = true) :
    parse source = some expected := by simpa [accepts] using h

/-- Lookup uses the parsed declarations. It does not return a baked-in width. -/
def lookupSize (declarations : List Owned) (type : NumType) : Option Nat :=
  declarations.findSome? (fun d => match d.file, d.declaration with
    | .types, .sizeCase t n => if t == type then some n else none
    | _, _ => none)

def dispatches (declarations : List Owned) : List Dispatch :=
  declarations.filterMap (fun d => match d.file, d.declaration with
    | .numerics, .dispatch e => some e
    | _, _ => none)

/-- Exactly one owned equation per selected operator; all other binop clauses
were parsed and checked disjoint. This is not merely membership of a slice. -/
theorem checked_dispatches {source : Bundle} (h : accepts source = true) :
    (parse source).map dispatches = some [equation .and, equation .or, equation .xor] := by
  rw [accepts_parse h]
  rfl

theorem checked_width {source : Bundle} (h : accepts source = true) :
    (parse source).bind (fun ds => lookupSize ds .i32) = some 32 := by
  rw [accepts_parse h]
  rfl

structure Call (α : Type) where
  primitive : Primitive
  width : Nat
  first : α
  second : α
  deriving Repr

def operand {α : Type} : Operand → α → α → α
  | .first, a, _ => a
  | .second, _, b => b

def resolve {α : Type} (ds : List Owned) (op : Oak.BitwiseFunction.Op) (a b : α) : Option (Call α) := do
  let e ← (dispatches ds).find? (fun e => decide (e.op = op))
  let width ← match e.width with
    | .literal n => some n
    | .sizenn =>
      if ds.contains ⟨.types, .sizennEquation⟩ then lookupSize ds .i32 else none
  some ⟨e.primitive, width, operand e.first a b, operand e.second a b⟩

/-- The meaning of the checked DSL wiring is parametric in the primitives.
Width and both original operands remain observable, including for noncommutative
primitive interpretations. No builtin implementation is imported by this rule. -/
def denote {α : Type} (primitives : Primitive → Nat → α → α → α)
    (source : Bundle) (op : Oak.BitwiseFunction.Op) (a b : α) : Option α := do
  let ds ← parse source
  let call ← resolve ds op a b
  some (primitives call.primitive call.width call.first call.second)

theorem checked_call {α : Type} {source : Bundle} (h : accepts source = true)
    (op : Oak.BitwiseFunction.Op) (a b : α) :
    (parse source).bind (fun ds => resolve ds op a b) =
      some ⟨primitive op, 32, a, b⟩ := by
  rw [accepts_parse h]
  cases op <;> rfl

theorem checked_denote {α : Type} {source : Bundle} (h : accepts source = true)
    (primitives : Primitive → Nat → α → α → α)
    (op : Oak.BitwiseFunction.Op) (a b : α) :
    denote primitives source op a b = some (primitives (primitive op) 32 a b) := by
  simp only [denote, accepts_parse h]
  cases op <;> rfl

/-- Reviewed interpretation of the three opaque builtins at the admitted i32
width. Its pointwise bit semantics are proved by numeric_bits below; fidelity
to the normative prose remains an explicit primitive-interpretation boundary. -/
def bitVecPrimitives : Primitive → Nat → BitVec 32 → BitVec 32 → BitVec 32
  | .iand, _, a, b => a &&& b
  | .ior, _, a, b => a ||| b
  | .ixor, _, a, b => a ^^^ b

theorem checked_numeric_agrees {source : Bundle} (h : accepts source = true)
    (op : Oak.BitwiseFunction.Op) (a b : BitVec 32) :
    denote bitVecPrimitives source op a b =
      some (WasmCoreBitwiseProjection.numeric (WasmCoreBitwiseProjection.binop op) a b) := by
  rw [checked_denote h]
  cases op <;> rfl

/-- Connect the actual source-byte binding to the existing bit-string relation
and Oak evaluator, for every input pair. -/
theorem checked_numeric_bits {source : Bundle} (h : accepts source = true)
    (op : Oak.BitwiseFunction.Op) (a b : BitVec 32) :
    denote bitVecPrimitives source op a b = some (Oak.BitwiseFunction.eval op a b) ∧
    WasmCoreBitwiseProjection.NumericResult (WasmCoreBitwiseProjection.binop op)
      a b (Oak.BitwiseFunction.eval op a b) := by
  rw [checked_numeric_agrees h, ← WasmCoreBitwiseProjection.numeric_agrees]
  exact ⟨rfl, WasmCoreBitwiseProjection.numeric_bits _ _ _⟩

end Oak.WasmNumericSource
