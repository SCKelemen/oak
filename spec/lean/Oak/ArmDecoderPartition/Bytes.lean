import Init
namespace Oak.ArmDecoderPartition
abbrev Bytes := List UInt8

def rawBytes (chunks : List String) : Bytes :=
  chunks.flatMap (fun s => s.toUTF8.data.toList)

theorem rawBytes_length (chunks : List String) :
    (rawBytes chunks).length = (chunks.map String.utf8ByteSize).sum := by
  induction chunks with
  | nil => rfl
  | cons s ss ih =>
    simp only [rawBytes, List.flatMap_cons, List.length_append,
      Array.length_toList, List.map_cons, List.sum_cons] at *
    rw [ih]
    rfl

/-- Fixed little-endian octets from an independently copied natural literal. -/
def unpack : Nat → Nat → Bytes
  | 0, _ => []
  | n+1, v => UInt8.ofNat (v % 256) :: unpack n (v / 256)

theorem unpack_length (n v : Nat) : (unpack n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp only [unpack, List.length_cons, ih]

def unpackBlocks (width : Nat) (values : List Nat) : Bytes :=
  values.flatMap (unpack width)

theorem unpackBlocks_length (width : Nat) (values : List Nat) :
    (unpackBlocks width values).length = values.length * width := by
  induction values with
  | nil => simp [unpackBlocks]
  | cons v vs ih =>
    simp only [unpackBlocks, List.flatMap_cons, List.length_append,
      unpack_length, List.length_cons] at *
    rw [ih, Nat.add_mul, Nat.one_mul, Nat.add_comm]

structure SizedBytes where
  bytes : Bytes
  size : Nat
  sized : bytes.length = size

theorem sizedBytes_length (blocks : List SizedBytes) :
    (blocks.flatMap SizedBytes.bytes).length = (blocks.map SizedBytes.size).sum := by
  induction blocks with
  | nil => rfl
  | cons b bs ih => simp only [List.flatMap_cons, List.length_append, b.sized,
      List.map_cons, List.sum_cons, ih]

/-- Ordered, exhaustive cuts. The final tail is never discarded. -/
def cutBytes (sizes : List Nat) (xs : Bytes) : List Bytes :=
  match sizes with
  | [] => [xs]
  | n :: ns => xs.take n :: cutBytes ns (xs.drop n)

theorem cutBytes_cover (sizes : List Nat) (xs : Bytes) :
    (cutBytes sizes xs).flatten = xs := by
  induction sizes generalizing xs with
  | nil => simp [cutBytes]
  | cons n ns ih => simp only [cutBytes, List.flatten_cons, ih, List.take_append_drop]
end Oak.ArmDecoderPartition
