import Oak.WasmNumericSource

/-! Kernel-checked negative controls. Small snippets exercise the same complete
byte scanner/owner parser as the required full-original-source integration gate.
They are not substituted for that gate. -/
open Oak.WasmNumericSource
set_option maxRecDepth 16384
set_option maxHeartbeats 0

namespace WasmNumericControls

def one (s : String) (op : Oak.BitwiseFunction.Op := .and) : Bool :=
  decide (parseFile .numerics (ascii s) = some [⟨.numerics, .dispatch (equation op)⟩])

def andRule := "def $binop_(Inn, AND, i_1, i_2) = $iand_($sizenn(Inn), i_1, i_2)\n"
def orRule := "def $binop_(Inn, OR, i_1, i_2) = $ior_($sizenn(Inn), i_1, i_2)\n"
def xorRule := "def $binop_(Inn, XOR, i_1, i_2) = $ixor_($sizenn(Inn), i_1, i_2)\n"

theorem actual_forms : one andRule = true ∧ one orRule .or = true ∧ one xorRule .xor = true := by
  decide +kernel

def rejectedRules : List String :=
  [orRule,
   "def $binop_(Inn, AND, i_1, i_2) = $ixor_($sizenn(Inn), i_1, i_2)\n",
   "def $binop_(Inn, AND, i_1, i_2) = $iand_(64, i_1, i_2)\n",
   "def $binop_(Inn, AND, i_1, i_2) = $iand_(32, i_1, i_2)\n",
   "def $binop_(Inn, AND, i_1, i_2) = $iand_($size(Inn), i_1, i_2)\n",
   "def $binop_(Inn, AND, i_1, i_2) = $iand_($sizenn(Inn), i_1)\n",
   "def $binop_(Inn, AND, i_1, i_2) = $iand_($sizenn(Inn), i_2, i_1)\n",
   "def $binop_(Inn, AND, i_1, i_2) = $iand_($sizenn(Inn), i_1, i_1)\n",
   "def $binop_(Inn, binop_, i_1, i_2) = $iand_($sizenn(Inn), i_1, i_2)\n",
   andRule ++ andRule,
   andRule ++ "def $binop_(Inn, AND, i_1, i_2) = $ixor_($sizenn(Inn), i_1, i_2)\n",
   "def $binop_(Inn, AND, i_1, i_2) = $iand_($sizenn(Inn), i_1, i_2) -- if false\n",
   "$binop_(Inn, AND, i_1, i_2) = $iand_($sizenn(Inn), i_1, i_2)\n",
   ";; " ++ andRule,
   "def $`binop_(Inn, AND, i_1, i_2) = $iand_($sizenn(Inn), i_1, i_2)\n",
   "def $binop_ (Inn, AND, i_1, i_2) = $iand_($sizenn(Inn), i_1, i_2)\n",
   "def $binop_(Inn, AND, i_1, i_2) = $iand_($sizenn(Inn), hint(show 0) i_1, i_2)\n",
   "def $binop_(Inn, AND, i_1, i_2) = $iand_($sizenn(Inn),\n\n i_1, i_2)\n",
   "(;" ++ andRule ++ ";)\n",
   "\"unterminated\n" ++ andRule]

theorem dispatch_mutations : rejectedRules.all (fun s => !one s) = true := by decide +kernel

/-- An opaque definition must not hide another definition through an upstream
longest-match lexical boundary. The appended conflicting equation is owned. -/
def hidden (separator : String) : String :=
  "def $opaque : nat\ndef $opaque = " ++ separator ++ andRule

def rejectsHidden (separator : String) : Bool :=
  decide (parseFile .numerics (ascii (hidden separator)) ≠ some [])

def hidingBoundaries : List String :=
  ["0", "0xFF", "U+FFFF", "%1_2", "_|_", ":_", "=_", "==_", "~~_", "->_",
   "=>_", "~>_", "~>*_", "<<_", ">>_", "|-_", "-|_", "%latex", ".", "`"]

theorem lexical_ownership_mutations : hidingBoundaries.all rejectsHidden = true := by decide +kernel

def malformedNumericBoundaries : List String :=
  ["0_", "0__1", "0xFF_", "0x_FF", "0x", "U+FFFF_", "U+_FFFF", "U+",
   "%1_", "%1__2"]

/-- These are rejection controls, not merely nonempty-owner controls: malformed
numerals must never manufacture a `def` from the identifier suffix `_def`. -/
theorem fabricated_numeric_owners : malformedNumericBoundaries.all
    (fun boundary => (parseFile .numerics (ascii (hidden boundary))).isNone) = true := by
  decide +kernel

def qualifierHiding : List String :=
  ["syntax opaque/syntax ", "syntax opaque/var ", "syntax opaque-syntax ",
   "syntax opaque-var ", "syntax opaque/def ", "syntax opaque-def "]

theorem qualifier_ownership_mutations : qualifierHiding.all
    (fun prefixText => (parseFile .numerics (ascii (prefixText ++ andRule))).isNone) = true := by
  decide +kernel

def malformedProtected : List String :=
  ["def $opaque : nat\ndef $opaque = 0 -- var nt : numtype\n",
   "syntax Inn/extra = I32\n",
   "syntax Inn-extra = I32\n",
   "syntax i_ = nat\n",
   "var AND : nat\n",
   "syntax I32 = nat\n",
   "var N : int\n",
   "syntax N hint(macro none) = int\n",
   "def $iand_(N, i_1, i_2) = i_1\n",
   "def $iand_ hint(partial)\n",
   "def $size(I32) = 64\n",
   "def $sizenn(nt) = 32\n",
   "syntax uN(N) hint(desc \"unsigned integer\") hint(show u#%) hint(macro \"uNX\") = 0 | . . . | $nat$(2^N-1)\n",
   "def $binop_(numtype, binop_(numtype), num_(numtype), num_(numtype)) : num_(numtype)* hint(show % 2#$_(%1,%3, %4))\n",
   "relation Hidden: I32\n",
   "grammar Hidden: I32\n",
   "rule Hidden: I32\n"]

theorem declaration_mutations : malformedProtected.all
    (fun s => (parseFile .numerics (ascii s)).isNone) = true := by decide +kernel

/-- The exact file identity remains part of every declaration, so moving a
valid equation into a different source file cannot satisfy its original owner. -/
theorem wrong_file_owner :
    decide (parseFile .values (ascii andRule) =
      some [⟨.numerics, .dispatch (equation .and)⟩]) = false := by decide +kernel

/-- Checkpoint proposals retain source byte offsets, end offsets, line numbers,
accumulator order and fuel. Wrong span/state proposals disagree with the actual
unsplit lexer, even though token spelling alone looks correct. -/
def badSpans : List (List Token) :=
  [[⟨[65,78,68], 1, 3, 0⟩], [⟨[65,78,68], 0, 2, 0⟩],
   [⟨[65,78,68], 0, 3, 1⟩], [⟨[65,78], 0, 3, 0⟩], []]

theorem span_mutations : badSpans.all
    (fun ts => decide (lex (ascii "AND\n") ≠ some ts)) = true := by decide +kernel

theorem checkpoint_fuel_mutation :
    lexAux 1 0 0 [] (ascii "AND\n") = none := by decide +kernel

theorem non_octet_rejection : lex [59,59,300,10] = none ∧ lex [300] = none ∧
    lex [34,300,34] = none := by decide +kernel

/-- Arbitrary interpretations can distinguish operand order and builtin choice;
the theorem is not rescued by AND/OR/XOR's commutativity. -/
theorem symbolic_dispatch {source : Bundle} (h : accepts source = true)
    (op : Oak.BitwiseFunction.Op) (a b : List Nat) :
    denote (fun p n x y => [match p with | .iand => 1 | .ior => 2 | .ixor => 3, n] ++ x ++ [99] ++ y)
      source op a b =
    some ([match primitive op with | .iand => 1 | .ior => 2 | .ixor => 3, 32] ++ a ++ [99] ++ b) :=
  checked_denote h _ op a b

end WasmNumericControls
#print axioms WasmNumericControls.actual_forms
#print axioms WasmNumericControls.dispatch_mutations
#print axioms WasmNumericControls.lexical_ownership_mutations
#print axioms WasmNumericControls.declaration_mutations
#print axioms WasmNumericControls.wrong_file_owner
#print axioms WasmNumericControls.symbolic_dispatch
#print axioms WasmNumericControls.span_mutations
#print axioms WasmNumericControls.checkpoint_fuel_mutation
#print axioms WasmNumericControls.fabricated_numeric_owners
#print axioms WasmNumericControls.qualifier_ownership_mutations
#print axioms WasmNumericControls.non_octet_rejection
