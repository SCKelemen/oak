import Oak.WasmCalls

/-! Bounded binary decoding and closed-table linking for the four-section scalar
profile. Structural decoding is NOT stack typing or a module validation proof. -/
namespace Oak.WasmModule
open WasmExecution
abbrev Parser (α : Type) := List UInt8 → Option (α × List UInt8)

structure Signature where
  params : List Width
  results : List Width
  deriving DecidableEq, Repr

structure Code where
  locals : List Width
  body : List WasmControl.Token
  deriving DecidableEq, Repr

structure Export where
  name : List UInt8
  index : Nat
  deriving DecidableEq, Repr

structure Module where
  functions : Array WasmCalls.Function
  exports : List Export
  deriving DecidableEq, Repr

def byte : Parser UInt8 | b :: rest => some (b, rest) | [] => none

def u32 : Parser Nat := fun bytes => do
  let (v, rest) ← WasmLEB.decode 32 false bytes
  some (v.toNat, rest)

def take (n : Nat) : Parser (List UInt8) := fun bytes =>
  if n ≤ bytes.length then some (bytes.take n, bytes.drop n) else none

def expect (value : UInt8) : Parser Unit := fun bytes => do
  let (b, rest) ← byte bytes
  if b = value then some ((), rest) else none

def parseMany (p : Parser α) : Nat → Parser (List α)
  | 0 => fun bytes => some ([], bytes)
  | n+1 => fun bytes => do
    let (v, tail) ← p bytes
    let (vs, suffix) ← parseMany p n tail
    some (v :: vs, suffix)

def vector (bound : Nat) (p : Parser α) : Parser (List α) := fun bytes => do
  let (n, rest) ← u32 bytes
  if n ≤ bound then parseMany p n rest else none

/-- A length-delimited parser only sees its declared region and must consume
that entire region; sibling sections/bodies cannot satisfy truncated content. -/
def sized (p : Parser α) : Parser α := fun bytes => do
  let (n, rest) ← u32 bytes
  let (front, suffix) ← take n rest
  let (value, []) ← p front | none
  some (value, suffix)

def parseSection (id : UInt8) (p : Parser α) : Parser α := fun bytes => do
  let ((), rest) ← expect id bytes
  sized p rest

def width : Parser Width
  | 127 :: rest => some (.w32, rest)
  | 126 :: rest => some (.w64, rest)
  | _ => none

def signature : Parser Signature := fun bytes => do
  let ((), rest) ← expect 96 bytes
  let (params, rest) ← vector 64 width rest
  let (results, rest) ← vector 1 width rest
  some (⟨params, results⟩, rest)

/-- Check the local budget BEFORE expanding repeated local declarations. -/
def localGroups : Nat → Nat → Parser (List Width)
  | 0, _ => fun bytes => some ([], bytes)
  | n+1, budget => fun bytes => do
    let (count, rest) ← u32 bytes
    if count > budget then none else do
      let (w, rest) ← width rest
      let (tail, suffix) ← localGroups n (budget-count) rest
      some (List.replicate count w ++ tail, suffix)

/-- Fuel bounds syntactic decoding by byte count, not runtime execution. -/
def tokens : Nat → List UInt8 → Option (List WasmControl.Token)
  | 0, bytes => if bytes.isEmpty then some [] else none
  | n+1, bytes => if bytes.isEmpty then some [] else do
    let (ins, rest) ← WasmInstruction.decode bytes
    let tail ← tokens n rest
    some (ins :: tail)

def code : Parser Code := fun bytes => do
  let (n, rest) ← u32 bytes
  if n > 16449 then none else do
    let (locals, rest) ← localGroups n 16449 rest
    let all ← tokens rest.length rest
    let (11, 0) :: revBody := all.reverse | none
    let body := revBody.reverse
    if WasmControl.nested body [] then some (⟨locals, body⟩, []) else none

def exportEntry : Parser Export := fun bytes => do
  let (name, rest) ← vector 256 byte bytes
  if name.isEmpty || (String.fromUTF8? ⟨name.toArray⟩).isNone then none else do
    let ((), rest) ← expect 0 rest
    let (index, rest) ← u32 rest
    some (⟨name, index⟩, rest)

/-- Function section order defines function indices; type indices may be
repeated or permuted. Code/function count mismatches refuse, never truncate. -/
def link (types : List Signature) : List Nat → List Code → Option (List WasmCalls.Function)
  | [], [] => some []
  | index :: indices, body :: bodies => do
    let sig ← types[index]?
    let tail ← link types indices bodies
    some ({params := sig.params, results := sig.results, locals := body.locals, body := body.body} :: tail)
  | _, _ => none

/-- Explicit structural bounds, not the Go validator's stack/control typing. -/
def admissible (functions : List WasmCalls.Function) (exports : List Export) : Bool :=
  !functions.isEmpty &&
  functions.all (fun f => f.params.length + f.locals.length ≤ 16449) &&
  (functions.map (fun f => f.params.length + f.locals.length)).sum ≤ 65536 &&
  (functions.map (fun f => f.body.length + 1)).sum ≤ 262144 &&
  exports.all (fun e => e.index < functions.length) &&
  (exports.map Export.name).eraseDups.length == exports.length

structure Parts where
  types : List Signature
  indices : List Nat
  exports : List Export
  bodies : List Code
  deriving DecidableEq, Repr

/-- Decode exactly four complete sections; trailing bytes are refused. -/
def parseModule (bytes : List UInt8) : Option Parts := do
  if bytes.length > 1048576 then none else do
    let (magic, rest) ← take 8 bytes
    if magic ≠ [0,97,115,109,1,0,0,0] then none else do
      let (types, rest) ← parseSection 1 (vector 128 signature) rest
      if types.isEmpty then none else do
        let (indices, rest) ← parseSection 3 (vector 128 u32) rest
        let (exports, rest) ← parseSection 7 (vector 128 exportEntry) rest
        let (bodies, []) ← parseSection 10 (vector 128 (sized code)) rest | none
        some ⟨types, indices, exports, bodies⟩

/-- No import/start/global/memory effects exist in this closed profile. Linking
constructs the function table; invocation initializes each activation's locals. -/
def decode (bytes : List UInt8) : Option Module := do
  let parts ← parseModule bytes
  let functions ← link parts.types parts.indices parts.bodies
  if admissible functions parts.exports then some ⟨functions.toArray, parts.exports⟩ else none

/-- Decode and resolve an export before invoking. `none` is a structural/name
refusal, distinct from modeled execution errors, traps, and fuel exhaustion. -/
def invokeExport (bytes name : List UInt8) (fuel : Nat) (args : List Value) :
    Option (Except WasmCalls.Error State) := do
  let m ← decode bytes
  let e ← m.exports.find? (fun e => e.name == name)
  some (WasmCalls.invoke m.functions e.index fuel args)

theorem take_region {n bytes front suffix} (h : take n bytes = some (front, suffix)) :
    front.length = n ∧ front ++ suffix = bytes := by
  unfold take at h
  split at h
  · rename_i hn
    cases h
    simp [List.length_take, Nat.min_eq_left hn]
  · contradiction

/-- Successful length-delimited decoding consumed exactly the isolated region. -/
theorem sized_region {p : Parser α} {bytes value suffix}
    (h : sized p bytes = some (value, suffix)) :
    ∃ n rest front, u32 bytes = some (n, rest) ∧
      front.length = n ∧ front ++ suffix = rest ∧ p front = some (value, []) := by
  unfold sized at h
  cases hu : u32 bytes with
  | none => simp [hu] at h
  | some pair =>
    obtain ⟨n, rest⟩ := pair
    cases ht : take n rest with
    | none => simp [hu, ht] at h
    | some pair =>
      obtain ⟨front, tail⟩ := pair
      cases hp : p front with
      | none => simp [hu, ht, hp] at h
      | some pair =>
        obtain ⟨v, leftover⟩ := pair
        cases leftover with
        | cons a b => simp [hu, ht, hp] at h
        | nil =>
          simp [hu, ht, hp] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨n, rest, front, rfl, (take_region ht).1, (take_region ht).2, hp⟩

/-- Successful byte-budget decoding agrees with the proved instruction decoder
and consumes the entire body region, with no trailing bytes left unexamined. -/
theorem tokens_decodeMany {fuel bytes instructions}
    (h : tokens fuel bytes = some instructions) :
    WasmInstruction.decodeMany instructions.length bytes = some (instructions, []) := by
  induction fuel generalizing bytes instructions with
  | zero => cases bytes <;> simp_all [tokens, WasmInstruction.decodeMany]
  | succ fuel ih =>
    cases bytes with
    | nil => simp_all [tokens, WasmInstruction.decodeMany]
    | cons b bytes =>
      cases hd : WasmInstruction.decode (b :: bytes) with
      | none => simp [tokens, hd] at h
      | some pair =>
        obtain ⟨ins, rest⟩ := pair
        cases ht : tokens fuel rest with
        | none => simp [tokens, hd, ht] at h
        | some tail =>
          simp [tokens, hd, ht] at h
          subst instructions
          simp [WasmInstruction.decodeMany, hd, ih ht]

/-- Expanding local groups cannot exceed the checked remaining budget. -/
theorem localGroups_budget {count budget bytes locals suffix}
    (h : localGroups count budget bytes = some (locals, suffix)) : locals.length ≤ budget := by
  induction count generalizing budget bytes locals suffix with
  | zero => simp [localGroups] at h; obtain ⟨rfl, _⟩ := h; simp
  | succ count ih =>
    cases hn : u32 bytes with
    | none => simp [localGroups, hn] at h
    | some pair =>
      obtain ⟨n, rest⟩ := pair
      by_cases hb : n > budget
      · simp [localGroups, hn, hb] at h
      · cases hw : width rest with
        | none => simp [localGroups, hn, hb, hw] at h
        | some pair =>
          obtain ⟨w, rest'⟩ := pair
          cases ht : localGroups count (budget-n) rest' with
          | none => simp [localGroups, hn, hb, hw, ht] at h
          | some pair =>
            obtain ⟨tail, suffix'⟩ := pair
            simp [localGroups, hn, hb, hw, ht] at h
            obtain ⟨rfl, rfl⟩ := h
            have hi := ih ht
            simp only [List.length_append, List.length_replicate]
            omega

/-- Successful linking preserves both function and code vector lengths. -/
theorem link_lengths {types indices bodies functions}
    (h : link types indices bodies = some functions) :
    functions.length = indices.length ∧ functions.length = bodies.length := by
  induction indices generalizing bodies functions with
  | nil => cases bodies <;> simp_all [link]
  | cons i indices ih =>
    cases bodies with
    | nil => simp [link] at h
    | cons b bodies =>
      cases hs : types[i]? with
      | none => simp [link, hs] at h
      | some sig =>
        cases ht : link types indices bodies with
        | none => simp [link, hs, ht] at h
        | some tail =>
          simp [link, hs, ht] at h
          subst functions
          simpa using ih ht

/-- Each linked function receives exactly the indexed type and corresponding
body/local declaration, independently of type-table order or duplication. -/
theorem link_member {types : List Signature} {indices : List Nat} {bodies : List Code}
    {functions : List WasmCalls.Function} {n : Nat} {f : WasmCalls.Function}
    (h : link types indices bodies = some functions) (hg : functions[n]? = some f) :
    ∃ (index : Nat) (body : Code) (sig : Signature), indices[n]? = some index ∧ bodies[n]? = some body ∧
      types[index]? = some sig ∧ f.params = sig.params ∧ f.results = sig.results ∧
      f.locals = body.locals ∧ f.body = body.body := by
  induction indices generalizing bodies functions n with
  | nil => cases bodies <;> simp_all [link]
  | cons index indices ih =>
    cases bodies with
    | nil => simp [link] at h
    | cons body bodies =>
      cases hs : types[index]? with
      | none => simp [link, hs] at h
      | some sig =>
        cases ht : link types indices bodies with
        | none => simp [link, hs, ht] at h
        | some tail =>
          simp [link, hs, ht] at h
          subst functions
          cases n with
          | zero =>
            simp at hg
            subst f
            exact ⟨index, body, sig, rfl, rfl, hs, rfl, rfl, rfl, rfl⟩
          | succ n => simpa using ih ht hg

theorem export_bounds {functions exports} (h : admissible functions exports = true)
    {e} (he : e ∈ exports) : e.index < functions.length := by
  simp only [admissible, Bool.and_eq_true] at h
  have hall := h.1.2
  exact of_decide_eq_true (List.all_eq_true.mp hall e he)

/-- Every decoded module is linked from its own binary metadata, with all
structural admission conditions checked before the table is exposed. -/
theorem decode_linked {bytes m} (h : decode bytes = some m) :
    ∃ parts functions, parseModule bytes = some parts ∧
      link parts.types parts.indices parts.bodies = some functions ∧
      m = ⟨functions.toArray, parts.exports⟩ ∧ admissible functions parts.exports = true := by
  cases hp : parseModule bytes with
  | none => simp [decode, hp] at h
  | some parts =>
    cases hl : link parts.types parts.indices parts.bodies with
    | none => simp [decode, hp, hl] at h
    | some fs =>
      cases ha : admissible fs parts.exports with
      | false => simp [decode, hp, hl, ha] at h
      | true =>
        simp [decode, hp, hl, ha] at h
        exact ⟨parts, fs, rfl, hl, h.symm, ha⟩

/-- A decoded export always resolves inside the linked function table. -/
theorem decoded_export_bounds {bytes m e} (h : decode bytes = some m)
    (he : e ∈ m.exports) : e.index < m.functions.size := by
  obtain ⟨parts, fs, _, _, rfl, ha⟩ := decode_linked h
  simpa using export_bounds ha he

theorem invoke_decoded {bytes m name e} (hd : decode bytes = some m)
    (he : m.exports.find? (fun e => e.name == name) = some e) (fuel : Nat) (args : List Value) :
    invokeExport bytes name fuel args = some (WasmCalls.invoke m.functions e.index fuel args) := by
  simp [invokeExport, hd, he]

end Oak.WasmModule
