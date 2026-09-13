/-! # The derived binary codec (`71-codecs.md` §22)

A fixed-width integer is `w` bytes, little-endian (byte `k` is bits
`8k..8k+7`) or big-endian (byte `k` is bits `8(w-1-k)..`); a record is the
concatenation of its fields' bytes in declaration order. Decoding reads
each field back at the offset the fields before it occupy. Reading what
was written returns the value reduced to its width (`fromLE_toLE`,
`fromBE_toBE`), a big-endian encoding is the little-endian one reversed
(`toBE_eq_reverse_toLE`), and a record decodes to its fields
(`decodeFields_encodeFields`). -/

namespace Oak.BinaryCodec

/-- The `w` little-endian bytes of `v`. -/
def toLE : Nat → Nat → List Nat
  | 0, _ => []
  | w + 1, v => (v % 256) :: toLE w (v / 256)

/-- The value of little-endian bytes. -/
def fromLE : List Nat → Nat
  | [] => 0
  | b :: rest => b + 256 * fromLE rest

def toBE (w v : Nat) : List Nat := (toLE w v).reverse
def fromBE (bytes : List Nat) : Nat := fromLE bytes.reverse

theorem toLE_length (w v : Nat) : (toLE w v).length = w := by
  induction w generalizing v with
  | zero => rfl
  | succ w ih => simp [toLE, ih]

theorem toBE_length (w v : Nat) : (toBE w v).length = w := by
  simp [toBE, toLE_length]

theorem toLE_bytes_lt (w v : Nat) : ∀ b ∈ toLE w v, b < 256 := by
  induction w generalizing v with
  | zero => intro b h; simp [toLE] at h
  | succ w ih =>
    intro b h
    simp only [toLE, List.mem_cons] at h
    rcases h with h | h
    · subst h; exact Nat.mod_lt _ (by decide)
    · exact ih _ b h

/-- Reading the written bytes gives the value modulo `256^w`. -/
theorem fromLE_toLE (w v : Nat) : fromLE (toLE w v) = v % 256 ^ w := by
  induction w generalizing v with
  | zero => simp [toLE, fromLE, Nat.mod_one]
  | succ w ih =>
    simp only [toLE, fromLE, ih]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ w) 256, Nat.mod_mul]

theorem fromBE_toBE (w v : Nat) : fromBE (toBE w v) = v % 256 ^ w := by
  simp [fromBE, toBE, fromLE_toLE]

/-- A value within its width round-trips exactly. -/
theorem fromLE_toLE_of_lt (w v : Nat) (h : v < 256 ^ w) : fromLE (toLE w v) = v := by
  rw [fromLE_toLE, Nat.mod_eq_of_lt h]

theorem fromBE_toBE_of_lt (w v : Nat) (h : v < 256 ^ w) : fromBE (toBE w v) = v := by
  rw [fromBE_toBE, Nat.mod_eq_of_lt h]

/-- Big-endian is little-endian reversed: the same bytes, the other order. -/
theorem toBE_eq_reverse_toLE (w v : Nat) : toBE w v = (toLE w v).reverse := rfl

/-- One field of a layout: its width, its endianness, its value. -/
structure Field where
  width : Nat
  big : Bool
  value : Nat

def Field.bytes (f : Field) : List Nat := if f.big then toBE f.width f.value else toLE f.width f.value
def Field.read (f : Field) (bytes : List Nat) : Nat := if f.big then fromBE bytes else fromLE bytes

theorem Field.bytes_length (f : Field) : f.bytes.length = f.width := by
  unfold Field.bytes; split <;> simp [toBE_length, toLE_length]

theorem Field.read_bytes (f : Field) : f.read f.bytes = f.value % 256 ^ f.width := by
  unfold Field.read Field.bytes
  split <;> simp [fromBE_toBE, fromLE_toLE]

/-- A record's bytes: its fields' bytes in order. -/
def encodeFields (fs : List Field) : List Nat := (fs.map Field.bytes).flatten

/-- The record's size is the sum of its fields' widths. -/
def layoutSize (fs : List Field) : Nat := (fs.map Field.width).sum

theorem encodeFields_length (fs : List Field) : (encodeFields fs).length = layoutSize fs := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    simp only [encodeFields, layoutSize, List.map_cons, List.flatten_cons, List.length_append, List.sum_cons] at ih ⊢
    rw [Field.bytes_length, ih]

/-- Decoding reads each field at the offset the fields before it occupy:
    the first `width` bytes are this field's, the rest the others'. -/
def decodeFields : List Field → List Nat → List Nat
  | [], _ => []
  | f :: rest, bytes => f.read (bytes.take f.width) :: decodeFields rest (bytes.drop f.width)

theorem take_of_length (l1 l2 : List Nat) (n : Nat) (h : l1.length = n) : (l1 ++ l2).take n = l1 := by
  subst h; exact List.take_left

theorem drop_of_length (l1 l2 : List Nat) (n : Nat) (h : l1.length = n) : (l1 ++ l2).drop n = l2 := by
  subst h; exact List.drop_left

/-- Decoding the encoding of a record gives every field's value at its
    width. -/
theorem decodeFields_encodeFields (fs : List Field) :
    decodeFields fs (encodeFields fs) = fs.map (fun f => f.value % 256 ^ f.width) := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    simp only [encodeFields, decodeFields, List.map_cons, List.flatten_cons]
    rw [take_of_length _ _ _ (Field.bytes_length f), drop_of_length _ _ _ (Field.bytes_length f), Field.read_bytes]
    exact congrArg _ ih

/-- Fields within their widths decode to themselves. -/
theorem decodeFields_encodeFields_exact (fs : List Field) (h : ∀ f ∈ fs, f.value < 256 ^ f.width) :
    decodeFields fs (encodeFields fs) = fs.map Field.value := by
  rw [decodeFields_encodeFields]
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨Nat.mod_eq_of_lt (h f (List.mem_cons_self ..)), ih (fun g hg => h g (List.mem_cons_of_mem _ hg))⟩

/-- A Bool byte is valid when it is 0 or 1; decoding reads it as `≠ 0`,
    so a valid byte decodes to the Bool that wrote it. -/
def boolByte (b : Bool) : Nat := if b then 1 else 0

theorem boolByte_le_one (b : Bool) : boolByte b ≤ 1 := by cases b <;> simp [boolByte]

theorem bool_round_trip (b : Bool) : (boolByte b ≠ 0) = b := by cases b <;> simp [boolByte]

end Oak.BinaryCodec

/-! ## Presence fields and byte runs

An `Option[T]` field is one presence byte followed by `T`'s bytes — zeros
when absent — so the layout keeps its size; a `View[u8, R]` field with a
byte count is the run itself. An `Item` is one of the three shapes with its
value; a record is the concatenation of its items' bytes, and decoding the
encoding returns every item's value (`decodeItems_encodeItems`). -/

namespace Oak.BinaryCodec

inductive Item where
  | int (width : Nat) (big : Bool) (value : Nat)
  | opt (width : Nat) (big : Bool) (value : Option Nat)
  | run (count : Nat) (bytes : List Nat) (h : bytes.length = count)

inductive Value where
  | int (v : Nat)
  | opt (v : Option Nat)
  | run (bytes : List Nat)
  deriving DecidableEq

def intBytes (w : Nat) (big : Bool) (v : Nat) : List Nat := if big then toBE w v else toLE w v
def intRead (w : Nat) (big : Bool) (bytes : List Nat) : Nat := if big then fromBE bytes else fromLE bytes

theorem intBytes_length (w : Nat) (big : Bool) (v : Nat) : (intBytes w big v).length = w := by
  unfold intBytes; split <;> simp [toBE_length, toLE_length]

theorem intRead_intBytes (w : Nat) (big : Bool) (v : Nat) : intRead w big (intBytes w big v) = v % 256 ^ w := by
  unfold intRead intBytes; split <;> simp [fromBE_toBE, fromLE_toLE]

def Item.size : Item → Nat
  | .int w _ _ => w
  | .opt w _ _ => w + 1
  | .run n _ _ => n

def Item.bytes : Item → List Nat
  | .int w big v => intBytes w big v
  | .opt w big none => 0 :: List.replicate w 0
  | .opt w big (some v) => 1 :: intBytes w big v
  | .run _ bs _ => bs

/-- The value an item's bytes denote, reduced to the width. -/
def Item.reduced : Item → Value
  | .int w _ v => .int (v % 256 ^ w)
  | .opt w _ none => .opt none
  | .opt w _ (some v) => .opt (some (v % 256 ^ w))
  | .run _ bs _ => .run bs

/-- Reading an item's shape from bytes: the presence byte decides the
    option, the run is the bytes themselves. -/
def Item.read : Item → List Nat → Value
  | .int w big _, bytes => .int (intRead w big bytes)
  | .opt w big _, bytes => .opt (if bytes.headD 0 = 0 then none else some (intRead w big bytes.tail))
  | .run _ _ _, bytes => .run bytes

theorem Item.bytes_length (it : Item) : it.bytes.length = it.size := by
  cases it with
  | int w big v => simp [Item.bytes, Item.size, intBytes_length]
  | opt w big v =>
    cases v with
    | none => simp [Item.bytes, Item.size, List.length_replicate]
    | some v => simp [Item.bytes, Item.size, intBytes_length]
  | run n bs h => simp [Item.bytes, Item.size, h]

theorem Item.read_bytes (it : Item) : it.read it.bytes = it.reduced := by
  cases it with
  | int w big v => simp [Item.read, Item.bytes, Item.reduced, intRead_intBytes]
  | opt w big v =>
    cases v with
    | none => simp [Item.read, Item.bytes, Item.reduced]
    | some v => simp [Item.read, Item.bytes, Item.reduced, intRead_intBytes]
  | run n bs h => simp [Item.read, Item.bytes, Item.reduced]

def encodeItems (items : List Item) : List Nat := (items.map Item.bytes).flatten

def decodeItems : List Item → List Nat → List Value
  | [], _ => []
  | it :: rest, bytes => it.read (bytes.take it.size) :: decodeItems rest (bytes.drop it.size)

theorem encodeItems_length (items : List Item) : (encodeItems items).length = (items.map Item.size).sum := by
  induction items with
  | nil => rfl
  | cons it rest ih =>
    simp only [encodeItems, List.map_cons, List.flatten_cons, List.length_append, List.sum_cons] at ih ⊢
    rw [Item.bytes_length, ih]

/-- Decoding the encoding of a layout returns every item's value: integers
    at their width, presence and payload of every option, every byte run. -/
theorem decodeItems_encodeItems (items : List Item) :
    decodeItems items (encodeItems items) = items.map Item.reduced := by
  induction items with
  | nil => rfl
  | cons it rest ih =>
    simp only [encodeItems, decodeItems, List.map_cons, List.flatten_cons]
    rw [take_of_length _ _ _ (Item.bytes_length it), drop_of_length _ _ _ (Item.bytes_length it), Item.read_bytes]
    exact congrArg _ ih

/-- An absent option's payload bytes are zeros: nothing of the value leaks
    into the layout. -/
theorem opt_none_payload (w : Nat) (big : Bool) : (Item.opt w big none).bytes = 0 :: List.replicate w 0 := rfl

end Oak.BinaryCodec
