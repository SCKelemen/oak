import Oak.WasmCoreModule

/-! Restricted binary grammar at the same pinned Core 3.0 source as the module
rules. Raw bytes, length/count fields, sections and every suffix are retained.
No grammar constructor tests the executable loader or an admission predicate. -/
set_option autoImplicit false
namespace Oak.WasmCoreBinary
open Oak.BitwiseFunction
open Oak.BitwiseModule
abbrev Bytes := List UInt8

/-- Direct transcription of pinned `BuN`: unsigned natural values, explicit
byte subtraction in continuation limbs, and the remaining-bit-width bound. -/
inductive Unsigned : Nat → Bytes → Nat → Prop where
  | terminal {width : Nat} (byte : UInt8) :
      byte.toNat < 128 → byte.toNat < 2^width → Unsigned width [byte] byte.toNat
  | continuation {width : Nat} (byte : UInt8) {rest : Bytes} {value : Nat} :
      128 ≤ byte.toNat → 7 < width → Unsigned (width-7) rest value →
      Unsigned width (byte::rest) (128*value + (byte.toNat-128))

theorem leb_to_unsigned {width : Nat} {bytes : Bytes} {value : Int}
    (h : WasmLEB.Encoding width false bytes value) : Unsigned width bytes value.toNat := by
  generalize hs : false = signed at h
  induction h with
  | @terminal width signed byte positive stop range =>
    subst signed
    have bound : byte.toNat < 2^width := by
      have r : (byte.toNat : Int) < 2^width := by
        simpa [WasmLEB.inRange, WasmLEB.terminalValue] using range
      have castpow : (2^width : Int) = ((2^width : Nat) : Int) := by simp
      rw [castpow] at r
      exact Int.ofNat_lt.mp r
    simpa [WasmLEB.terminalValue] using Unsigned.terminal byte stop bound
  | @continuation width signed byte bytes value budget more tail ih =>
    subst signed
    have nonneg : 0 ≤ value := by
      have range := tail.range
      simp only [WasmLEB.inRange, Bool.false_eq_true, ↓reduceIte] at range
      exact range.1
    have limit := UInt8.toNat_lt byte
    have limb : byte.toNat % 128 = byte.toNat - 128 := by omega
    have eq : (((byte.toNat % 128 : Nat) : Int) + 128 * value).toNat =
        128 * value.toNat + (byte.toNat - 128) := by omega
    rw [eq]
    exact .continuation byte more budget (ih rfl)

def U32 (bytes : Bytes) (n : Nat) : Prop := Unsigned 32 bytes n

inductive Section (id : UInt8) : Bytes → Bytes → Prop where
  | intro (lengthBytes payload : Bytes) : U32 lengthBytes payload.length →
      Section id (id :: (lengthBytes ++ payload)) payload

inductive TypePayload : Bytes → Prop where
  | intro (count parameters results : Bytes) :
      U32 count 1 → U32 parameters 2 → U32 results 1 →
      TypePayload (count ++ [96] ++ parameters ++ [127,127] ++ results ++ [127])

inductive FunctionPayload : Bytes → Prop where
  | intro (count index : Bytes) : U32 count 1 → U32 index 0 →
      FunctionPayload (count ++ index)

/-- The ASCII branch of the normative UTF-8 string relation. Code points are
actual unsigned values below 128, so decoding is identity on this name subset. -/
inductive UTF8Name : Bytes → List Nat → Prop where
  | nil : UTF8Name [] []
  | ascii (byte : UInt8) {bytes : Bytes} {chars : List Nat} :
      byte.toNat < 128 → UTF8Name bytes chars → UTF8Name (byte::bytes) (byte.toNat::chars)

theorem ascii_name (name : Bytes) (h : ∀ b ∈ name, b.toNat < 128) :
    UTF8Name name (name.map UInt8.toNat) := by
  induction name with
  | nil => exact .nil
  | cons b bs ih =>
    exact .ascii b (h b (by simp)) (ih (by intro x hx; exact h x (by simp [hx])))

theorem name_representation_injective {left right : Bytes}
    (h : left.map UInt8.toNat = right.map UInt8.toNat) : left = right :=
  (List.map_inj_right (fun _ _ eq => UInt8.toNat_inj.mp eq)).mp h

inductive ExportPayload (name : Bytes) : Bytes → Prop where
  | intro (count lengthBytes index : Bytes) :
      U32 count 1 → U32 lengthBytes name.length → U32 index 0 →
      UTF8Name name (name.map UInt8.toNat) →
      ExportPayload name (count ++ lengthBytes ++ name ++ [0] ++ index)

/-- Binstr productions are independent of the Oak assembler/decoder. -/
inductive Instruction : Bytes → Oak.WasmCoreBitwiseProjection.Instr → Prop where
  | localGet (indexBytes : Bytes) (index : Nat) : U32 indexBytes index →
      Instruction (32 :: indexBytes) (.localGet index)
  | and : Instruction [113] (.binary .and)
  | or : Instruction [114] (.binary .or)
  | xor : Instruction [115] (.binary .xor)

/-- Bexpr: a sequence of independently decoded instructions, terminated by
0x0B. The delimiter contributes no instruction to the abstract expression. -/
inductive Expression : Bytes → List Oak.WasmCoreBitwiseProjection.Instr → Prop where
  | end : Expression [11] []
  | cons {first rest : Bytes} {i : Oak.WasmCoreBitwiseProjection.Instr}
      {is : List Oak.WasmCoreBitwiseProjection.Instr} :
      Instruction first i → Expression rest is → Expression (first ++ rest) (i :: is)

private theorem u32_zero : U32 [0] 0 :=
  .terminal _ (by decide) (by decide)
private theorem u32_one : U32 [1] 1 :=
  .terminal _ (by decide) (by decide)

theorem bitwise_expression (op : Op) :
    Expression (functionBytes op) (Oak.WasmCoreBitwiseProjection.body op) := by
  cases op
  · have h := Expression.cons (.localGet [0] 0 u32_zero) (.cons (.localGet [1] 1 u32_one) (.cons .and .end))
    exact h
  · have h := Expression.cons (.localGet [0] 0 u32_zero) (.cons (.localGet [1] 1 u32_one) (.cons .or .end))
    exact h
  · have h := Expression.cons (.localGet [0] 0 u32_zero) (.cons (.localGet [1] 1 u32_one) (.cons .xor .end))
    exact h


inductive CodePayload (op : Op) : Bytes → Prop where
  | intro (count lengthBytes locals : Bytes) :
      U32 count 1 → U32 locals 0 →
      U32 lengthBytes (locals ++ functionBytes op).length →
      Expression (functionBytes op) (Oak.WasmCoreBitwiseProjection.body op) →
      CodePayload op (count ++ lengthBytes ++ locals ++ functionBytes op)

/-- Bmodule's optional absent sections reduce to epsilon. Both the function
section and code section contain exactly one entry. All fields and final bytes
are consumed; source-name equality is not supplied by an unrelated claim. -/
inductive BinaryModule : Bytes → Oak.WasmCoreModule.Module → Prop where
  | intro (name : Bytes) (op : Op) (ts fs es cs tp fp ep cp : Bytes) :
      Section 1 ts tp → TypePayload tp →
      Section 3 fs fp → FunctionPayload fp →
      Section 7 es ep → ExportPayload name ep →
      Section 10 cs cp → CodePayload op cp →
      BinaryModule ([0,97,115,109,1,0,0,0] ++ ts ++ fs ++ es ++ cs)
        (Oak.WasmCoreModule.module name op)

private theorem byte_sound {n : UInt8} {bytes rest : Bytes}
    (h : expectByte n bytes = some rest) : bytes = n :: rest := by
  cases bytes with
  | nil => simp [expectByte] at h
  | cons a bs =>
    simp only [expectByte] at h
    split at h
    · simp_all
    · simp_all

private theorem nat_sound {bytes rest : Bytes} {n : Nat}
    (h : readNat bytes = some (n,rest)) :
    ∃ front, bytes = front ++ rest ∧ U32 front n := by
  simp only [readNat, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨v,tail⟩, decode, h⟩ := h
  split at h
  next positive =>
    cases h
    obtain ⟨front, eq, grammar⟩ := WasmLEB.decode_sound decode
    exact ⟨front, eq, leb_to_unsigned grammar⟩
  next => simp at h

private theorem expected_nat_sound {n : Nat} {bytes rest : Bytes}
    (h : expectNat n bytes = some rest) :
    ∃ front, bytes = front ++ rest ∧ U32 front n := by
  simp only [expectNat, bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨value,tail⟩, read, h⟩ := h
  split at h
  next eq =>
    dsimp at eq
    cases h
    subst value
    exact nat_sound read
  next => simp at h

private theorem take_sound {n : Nat} {bytes front rest : Bytes}
    (h : takeBytes n bytes = some (front,rest)) :
    front.length = n ∧ bytes = front ++ rest := by
  simp only [takeBytes] at h
  split at h
  next bound => cases h; exact ⟨by simp [bound], (List.take_append_drop n bytes).symm⟩
  next => simp at h

private theorem section_sound {id : UInt8} {bytes payload rest : Bytes}
    (h : readSection id bytes = some (payload,rest)) :
    ∃ encodedSection, bytes = encodedSection ++ rest ∧ Section id encodedSection payload := by
  simp only [readSection, bind, Option.bind_eq_some_iff] at h
  obtain ⟨afterId, hid, ⟨⟨n,afterLength⟩, hn, ht⟩⟩ := h
  obtain ⟨lengthBytes, hnbytes, hnenc⟩ := nat_sound hn
  dsimp at ht
  obtain ⟨length, hparts⟩ := take_sound ht
  refine ⟨id :: (lengthBytes ++ payload), ?_, ?_⟩
  · rw [byte_sound hid, hnbytes, hparts]; simp [List.append_assoc]
  · exact .intro _ _ (length ▸ hnenc)

private theorem finished_sound {bytes : Bytes} (h : finished bytes = some ()) : bytes = [] := by
  simp only [finished] at h
  split at h <;> simp_all

theorem loaded_binary {entry bytes : Bytes} {loaded : Loaded} {op : Op}
    (h : load entry bytes = some loaded) (code : loaded.code = functionBytes op) :
    loaded.exportName = entry ∧ BinaryModule bytes (Oak.WasmCoreModule.module entry op) := by
  unfold load at h
  split at h
  next => simp at h
  next valid =>
    simp only [bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨header, afterHeader⟩, hheader, h⟩ := h
    dsimp at h
    split at h
    next => simp at h
    next headerEq =>
      have headerEq : header = [0,97,115,109,1,0,0,0] := by simpa using headerEq
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨⟨types, afterTypes⟩, htypes, h⟩ := h
      dsimp at h
      obtain ⟨t1, ht1, t2, ht2, t3, ht3, t4, ht4, t5, ht5, t6, ht6, t7, ht7, ⟨⟩, htend, h⟩ := h
      obtain ⟨⟨functions, afterFunctions⟩, hfunctions, h⟩ := h
      dsimp at h
      obtain ⟨f1, hf1, f2, hf2, ⟨⟩, hfend, h⟩ := h
      obtain ⟨⟨exports, afterExports⟩, hexports, h⟩ := h
      dsimp at h
      obtain ⟨e1, he1, ⟨nameLength,e2⟩, he2, ⟨name,e3⟩, he3, h⟩ := h
      dsimp at h
      split at h
      next => simp at h
      next nameEq =>
        have nameEq : name = entry := by simpa using nameEq
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨e4, he4, e5, he5, ⟨⟩, heend, ⟨codeSection,afterCode⟩, hcsection, h⟩ := h
        dsimp at h
        obtain ⟨⟨⟩, hfinal, c1, hc1, ⟨bodyLength,c2⟩, hc2, ⟨rawBody,c3⟩, hc3, h⟩ := h
        dsimp at h
        obtain ⟨⟨⟩, hcend, rawCode, hlocals, h⟩ := h
        cases h
        dsimp at code
        subst rawCode
        constructor
        · exact nameEq
        · subst name
          dsimp at he3 hc3
          obtain ⟨_, hheaderBytes⟩ := take_sound hheader
          obtain ⟨ts, hts, tsGrammar⟩ := section_sound htypes
          obtain ⟨fs, hfs, fsGrammar⟩ := section_sound hfunctions
          obtain ⟨es, hes, esGrammar⟩ := section_sound hexports
          obtain ⟨cs, hcs, csGrammar⟩ := section_sound hcsection
          obtain ⟨typeCount, htc, gtc⟩ := expected_nat_sound ht1
          obtain ⟨paramCount, hpc, gpc⟩ := expected_nat_sound ht3
          obtain ⟨resultCount, hrc, grc⟩ := expected_nat_sound ht6
          have typeGrammar : TypePayload types := by
            rw [htc, byte_sound ht2, hpc, byte_sound ht4, byte_sound ht5,
              hrc, byte_sound ht7, finished_sound htend]
            simpa [List.append_assoc] using TypePayload.intro typeCount paramCount resultCount gtc gpc grc
          obtain ⟨funcCount, hfc, gfc⟩ := expected_nat_sound hf1
          obtain ⟨funcIndex, hfi, gfi⟩ := expected_nat_sound hf2
          have funcGrammar : FunctionPayload functions := by
            rw [hfc, hfi, finished_sound hfend]
            simpa using FunctionPayload.intro funcCount funcIndex gfc gfi
          obtain ⟨exportCount, hec, gec⟩ := expected_nat_sound he1
          obtain ⟨nameLengthBytes, hen, gen⟩ := nat_sound he2
          obtain ⟨nameLengthEq, hnameBytes⟩ := take_sound he3
          obtain ⟨exportIndex, hei, gei⟩ := expected_nat_sound he5
          have ascii : ∀ b ∈ entry, b.toNat < 128 := by
            have h : entry.all (fun b => b.toNat < 128) = true := by
              apply Classical.byContradiction
              intro hn
              exact valid (Or.inr (Or.inr hn))
            simpa using h
          have exportGrammar : ExportPayload entry exports := by
            rw [hec, hen, hnameBytes, byte_sound he4, hei, finished_sound heend]
            simpa [List.append_assoc] using ExportPayload.intro exportCount nameLengthBytes
              exportIndex gec (nameLengthEq ▸ gen) gei (ascii_name entry ascii)
          obtain ⟨codeCount, hcc, gcc⟩ := expected_nat_sound hc1
          obtain ⟨bodyLengthBytes, hbl, gbl⟩ := nat_sound hc2
          obtain ⟨bodyLengthEq, hbodyBytes⟩ := take_sound hc3
          obtain ⟨localCount, hlc, glc⟩ := expected_nat_sound hlocals
          have codeGrammar : CodePayload op codeSection := by
            have size : bodyLength = (localCount ++ functionBytes op).length := by
              rw [hlc] at bodyLengthEq
              exact bodyLengthEq.symm
            rw [hcc, hbl, hbodyBytes, hlc, finished_sound hcend]
            simpa [List.append_assoc] using CodePayload.intro codeCount bodyLengthBytes
              localCount gcc glc (size ▸ gbl) (bitwise_expression op)
          have bytesEq : bytes = [0,97,115,109,1,0,0,0] ++ ts ++ fs ++ es ++ cs := by
            rw [hheaderBytes, headerEq, hts, hfs, hes, hcs, finished_sound hfinal]
            simp [List.append_assoc]
          rw [bytesEq]
          exact .intro entry op ts fs es cs types functions exports codeSection
            tsGrammar typeGrammar fsGrammar funcGrammar esGrammar exportGrammar csGrammar codeGrammar

/-- Admission of arbitrary actual module bytes implies a grammar derivation,
including all section/entry byte lengths. This is not a fixture-only theorem. -/
theorem admitted_binary {entry bytes : Bytes} {op : Op}
    (accepted : acceptsModule .wasm .wasmLocals [32,32] 32 op entry bytes = true) :
    BinaryModule bytes (Oak.WasmCoreModule.module entry op) := by
  cases h : load entry bytes with
  | none => simp [acceptsModule, h] at accepted
  | some loaded =>
    have bodyAccepted : accepts .wasm .wasmLocals [32,32] 32 op loaded.code = true := by
      simpa [acceptsModule, h] using accepted
    have exactCode := (accepts_iff _ _ _ _ _ _).mp bodyAccepted
    exact (loaded_binary h exactCode.2.2.2.2).2

end Oak.WasmCoreBinary
