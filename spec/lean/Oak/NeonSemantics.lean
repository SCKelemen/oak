import Oak.Simd
import Oak.Intrinsics

/-! # The NEON lane functions and the portable operations they realize

Model for `docs/spec/94-assembler.md` §8 (the vector increment) and
`docs/spec/93-simd.md` §1.4: the verifier (`asm/verify_vector.go`) reads
each NEON instruction the native backend emits (`nativegen/simd.go`) as a
function of its lanes, and lowers each `simd.*` call of the Oak body
through `Oak.Simd`'s definitions. This file states those lane functions
over `Nat` lanes, exactly as the verifier applies them, and proves that
each is the `Oak.Simd` operation the lowering uses it for:

- `add`/`sub .16b` are `addWrap`/wrapping subtraction lane by lane;
- `uqsub` is `subSat` (natural subtraction already saturates);
- `cmeq` is `eqMask`;
- `umin`/`umax` are the lane minimum and maximum;
- `ushr #n` is `shr n`;
- `tbl` with one table register is `tbl` (an index at or beyond sixteen
  selects zero);
- `ext #(16 - n)` is `prev n`;
- `umaxv` over the bytes of a mask is nonzero exactly when `anyLane` holds,
  and `umaxv` over `cmeq #0` of the lanes is zero exactly when `allLanes`
  holds;
- the `sshr #7`, `and` with the lane bits, `addv` per half, `orr` of the
  halves sequence is `movemask 8`.

What this file does not do: ground the lane functions in Arm's own
specification. That is the Sail step (`spec/sail/`), which today covers
the scalar primitives only (`docs/notes/proof-chain-audit-2026-09.md`). -/

namespace Oak.Neon

open Oak.Simd

/-! ## The lane functions (asm/verify_vector.go, `laneBinary` and friends) -/

/-- `add vD.T, vN.T, vM.T`: wrapping addition at the lane width. -/
def add (bits x y : Nat) : Nat := (x + y) % 2 ^ bits

/-- `sub vD.T, vN.T, vM.T`: wrapping subtraction at the lane width. -/
def sub (bits x y : Nat) : Nat := (x + (2 ^ bits - y % 2 ^ bits)) % 2 ^ bits

/-- `uqsub`: x - y when y < x, else 0 (the verifier's `ite(hi x y, x - y, 0)`). -/
def uqsub (x y : Nat) : Nat := if y < x then x - y else 0

/-- `umin`: the verifier's `ite(lo x y, x, y)`. -/
def umin (x y : Nat) : Nat := if x < y then x else y

/-- `umax`: the verifier's `ite(hi x y, x, y)`. -/
def umax (x y : Nat) : Nat := if y < x then x else y

/-- `cmeq`: all ones on equal lanes, zero otherwise. -/
def cmeq (bits x y : Nat) : Nat := if x = y then allOnes bits else 0

/-- `ushr #n`: logical shift right of the lane. -/
def ushr (n x : Nat) : Nat := x >>> n

/-- `tbl vD.16b, {vT.16b}, vI.16b`, one lane: the table entry at the index,
zero when the index is at or beyond the table (NEON's rule; the verifier's
sixteen-way select `laneTable`). -/
def tbl (table : List Nat) (j : Nat) : Nat :=
  if h : j < table.length ∧ j < 16 then table[j] else 0

/-- `ext vD.16b, vN.16b, vM.16b, #n`: the bytes of `low ++ high` from
position `n`, as many as `low` has (the verifier's `laneExtract`). -/
def ext (n : Nat) (low high : List Nat) : List Nat :=
  ((low ++ high).drop n).take low.length

/-- `umaxv bD, vN.16b`: the unsigned maximum over the lanes (the verifier's
left fold `laneReduce "umaxv"`). -/
def umaxv (lanes : List Nat) : Nat := lanes.foldl max 0

/-- `addv bD, vN.8b`: the wrapping sum over the lanes at the lane width. -/
def addv (bits : Nat) (lanes : List Nat) : Nat := lanes.foldl (fun acc x => (acc + x) % 2 ^ bits) 0

/-- `cnt vD.T, vN.T`: the population count of the lane's bits
(`Oak.Intrinsics.popcount`, the verifier's `cnt` term). -/
def cnt (bits x : Nat) : Nat := Oak.Intrinsics.popcount ((List.range bits).map (Nat.testBit x))

/-- `sshr vD.16b, vN.16b, #7` on a byte: all ones when the top bit is set,
zero otherwise (the arithmetic shift of an 8-bit lane by seven). -/
def sshr7 (x : Nat) : Nat := if topBit 8 x = 1 then 255 else 0

/-! ## Lane-wise: the binary operations -/

theorem add_eq_addWrap (bits : Nat) (a b : Vec) :
    List.zipWith (add bits) a b = addWrap bits a b := rfl

theorem uqsub_eq_sub (x y : Nat) : uqsub x y = x - y := by
  unfold uqsub
  split <;> omega

/-- `uqsub` lane by lane is `subSat`. -/
theorem uqsub_eq_subSat (a b : Vec) : List.zipWith uqsub a b = subSat a b := by
  unfold subSat
  congr 1
  funext x y
  exact uqsub_eq_sub x y

/-- `cmeq` lane by lane is `eqMask`. -/
theorem cmeq_eq_eqMask (bits : Nat) (a b : Vec) :
    List.zipWith (cmeq bits) a b = eqMask bits a b := rfl

theorem umin_eq_min (x y : Nat) : umin x y = min x y := by
  unfold umin
  split <;> omega

theorem umax_eq_max (x y : Nat) : umax x y = max x y := by
  unfold umax
  split <;> omega

/-- `ushr #n` lane by lane is `shr n`. -/
theorem ushr_eq_shr (n : Nat) (v : Vec) : v.map (ushr n) = shr n v := rfl

/-! ## The table lookup and the cross-block shift -/

/-- `tbl` over the index lanes is `Simd.tbl`. -/
theorem tbl_eq_tbl (table idx : Vec) : idx.map (tbl table) = Simd.tbl table idx := rfl

/-- `ext #(16 - n)` of a sixteen-byte `prev` and the current block is
`prev n`: the sixteen bytes ending `n` before the end of `prev ++ cur`. -/
theorem ext_eq_prev (n : Nat) (prevBlock cur : Vec) (hp : prevBlock.length = 16) :
    ext (16 - n) prevBlock cur = prev n prevBlock cur := by
  simp [ext, prev, hp]

/-! ## The reductions: `any` and `all` -/

theorem foldl_max_ne_zero (acc : Nat) (v : List Nat) :
    v.foldl max acc ≠ 0 ↔ acc ≠ 0 ∨ v.any (fun lane => lane ≠ 0) = true := by
  induction v generalizing acc with
  | nil => simp
  | cons x rest ih =>
    rw [List.foldl_cons, ih (max acc x)]
    simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq]
    have hmax : max acc x ≠ 0 ↔ acc ≠ 0 ∨ x ≠ 0 := by omega
    rw [hmax, or_assoc]

/-- `umaxv` over a mask is nonzero exactly when some lane is: the `any`
lowering (`umaxv bD, vN.16b; umov; cmp #0; cset ne`). -/
theorem umaxv_ne_zero_iff (v : Vec) : umaxv v ≠ 0 ↔ anyLane v = true := by
  unfold umaxv anyLane
  rw [foldl_max_ne_zero]
  simp

/-- `cmeq #0` then `umaxv` is zero exactly when every lane is nonzero: the
`all` lowering (`cmeq vD.T, vN.T, #0; umaxv; umov; cmp #0; cset eq`). -/
theorem umaxv_cmeq_zero_iff (bits : Nat) (hbits : 0 < bits) (v : Vec) :
    umaxv (v.map (fun x => cmeq bits x 0)) = 0 ↔ allLanes v = true := by
  have hones : allOnes bits ≠ 0 := by
    unfold allOnes
    have : 1 < 2 ^ bits := Nat.one_lt_two_pow (by omega)
    omega
  have key : anyLane (v.map (fun x => cmeq bits x 0)) = true ↔ ¬ allLanes v = true := by
    unfold anyLane allLanes
    simp only [List.any_map, List.any_eq_true, List.all_eq_true, Function.comp,
      decide_eq_true_eq, cmeq]
    constructor
    · rintro ⟨x, hx, hne⟩ hall
      have := hall x hx
      simp [this] at hne
    · intro hnot
      apply Classical.byContradiction
      intro hno
      apply hnot
      intro x hx hzero
      apply hno
      exact ⟨x, hx, by simp [hzero, hones]⟩
  have hne : umaxv (v.map (fun x => cmeq bits x 0)) ≠ 0 ↔ ¬ allLanes v = true :=
    (umaxv_ne_zero_iff _).trans key
  constructor
  · intro hz
    exact Classical.byContradiction (fun hall => hne.mpr hall hz)
  · intro hall
    exact Classical.byContradiction (fun hz => hne.mp hz hall)

/-! ## `movemask` over bytes

The native lowering (`nativegen/simd.go` `simdMovemask`): `sshr #7` makes
each byte all ones or zero, an `and` with the lane bits `1, 2, 4, …, 128`
per half keeps one bit per lane, `addv` sums each half's eight bytes, and
the halves are combined as low and high byte (`lsl #8`, `orr`). -/

/-- The lane bits of one half. -/
def laneBitsOfHalf : List Nat := [1, 2, 4, 8, 16, 32, 64, 128]

/-- One half's mask: the summed `and`s of the shifted bytes with the lane bits. -/
def maskHalf (lanes : List Nat) : Nat :=
  addv 8 (List.zipWith (fun x bit => sshr7 x &&& bit) lanes laneBitsOfHalf)

/-- The full sequence over sixteen bytes: the low half's mask in the low
byte, the high half's shifted up by eight, combined with `orr`. -/
def movemaskBytes (v : List Nat) : Nat :=
  maskHalf (v.take 8) ||| (maskHalf (v.drop 8) <<< 8)

/-- `255 &&& 2^k = 2^k` below eight: the shifted byte keeps its lane bit. -/
theorem and_255_pow (k : Nat) (hk : k < 8) : 255 &&& 2 ^ k = 2 ^ k := by
  match k, hk with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide
  | 3, _ => decide
  | 4, _ => decide
  | 5, _ => decide
  | 6, _ => decide
  | 7, _ => decide
  | _ + 8, hk => omega

theorem sshr7_and_bit (x k : Nat) (hk : k < 8) : sshr7 x &&& 2 ^ k = topBit 8 x * 2 ^ k := by
  have hbit : topBit 8 x ≤ 1 := topBit_le_one 8 x
  by_cases h : topBit 8 x = 1
  · rw [sshr7, if_pos h, h, Nat.one_mul]
    exact and_255_pow k hk
  · have h0 : topBit 8 x = 0 := by omega
    rw [sshr7, if_neg h, h0, Nat.zero_mul, Nat.zero_and]

/-- `movemask` over an appended vector: the second part's mask shifted up
by the first part's lane count. -/
theorem movemask_append (bits : Nat) (a b : Vec) :
    movemask bits (a ++ b) = movemask bits a + 2 ^ a.length * movemask bits b := by
  induction a with
  | nil => simp [movemask]
  | cons x rest ih =>
    simp only [List.cons_append, movemask, List.length_cons, ih, Nat.pow_succ]
    simp only [Nat.mul_add, Nat.add_assoc]
    rw [Nat.mul_left_comm 2 (2 ^ rest.length), Nat.mul_assoc (2 ^ rest.length) 2]

/-- A list of eight elements, spelled out. -/
theorem exists_eight (l : List Nat) (h : l.length = 8) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7, l = [x0, x1, x2, x3, x4, x5, x6, x7] := by
  rcases l with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, _ | ⟨x4, _ | ⟨x5, _ | ⟨x6, _ | ⟨x7, _ | ⟨x8, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals (simp only [List.length_cons, List.length_nil] at h)
  all_goals (try omega)
  exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩

/-- One half: the summed masked bytes are `movemask 8` of the eight lanes
(the sum stays below 256, so the wrapping `addv` is the plain sum). -/
theorem maskHalf_eq_movemask (lanes : List Nat) (h : lanes.length = 8) :
    maskHalf lanes = movemask 8 lanes := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, rfl⟩ := exists_eight lanes h
  have h0 : sshr7 x0 &&& 1 = topBit 8 x0 * 1 := sshr7_and_bit x0 0 (by omega)
  have h1 : sshr7 x1 &&& 2 = topBit 8 x1 * 2 := sshr7_and_bit x1 1 (by omega)
  have h2 : sshr7 x2 &&& 4 = topBit 8 x2 * 4 := sshr7_and_bit x2 2 (by omega)
  have h3 : sshr7 x3 &&& 8 = topBit 8 x3 * 8 := sshr7_and_bit x3 3 (by omega)
  have h4 : sshr7 x4 &&& 16 = topBit 8 x4 * 16 := sshr7_and_bit x4 4 (by omega)
  have h5 : sshr7 x5 &&& 32 = topBit 8 x5 * 32 := sshr7_and_bit x5 5 (by omega)
  have h6 : sshr7 x6 &&& 64 = topBit 8 x6 * 64 := sshr7_and_bit x6 6 (by omega)
  have h7 : sshr7 x7 &&& 128 = topBit 8 x7 * 128 := sshr7_and_bit x7 7 (by omega)
  have t0 := topBit_le_one 8 x0
  have t1 := topBit_le_one 8 x1
  have t2 := topBit_le_one 8 x2
  have t3 := topBit_le_one 8 x3
  have t4 := topBit_le_one 8 x4
  have t5 := topBit_le_one 8 x5
  have t6 := topBit_le_one 8 x6
  have t7 := topBit_le_one 8 x7
  simp only [maskHalf, laneBitsOfHalf, List.zipWith_cons_cons, List.zipWith_nil_right, addv,
    List.foldl_cons, List.foldl_nil, movemask]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]
  omega

/-- The sequence over sixteen bytes is `movemask 8` (`Oak.Simd.movemask`). -/
theorem movemaskBytes_eq_movemask (v : Vec) (h : v.length = 16) :
    movemaskBytes v = movemask 8 v := by
  have hlow : (v.take 8).length = 8 := by simp [List.length_take, h]
  have hhigh : (v.drop 8).length = 8 := by simp [List.length_drop, h]
  have hbound : movemask 8 (v.take 8) < 2 ^ 8 := by
    have := movemask_lt 8 (v.take 8)
    rwa [hlow] at this
  have hcat : movemask 8 v = movemask 8 (v.take 8) + 2 ^ 8 * movemask 8 (v.drop 8) := by
    have := movemask_append 8 (v.take 8) (v.drop 8)
    rwa [List.take_append_drop, hlow] at this
  unfold movemaskBytes
  rw [maskHalf_eq_movemask _ hlow, maskHalf_eq_movemask _ hhigh, hcat, Nat.shiftLeft_eq,
    Nat.mul_comm (movemask 8 (v.drop 8)) (2 ^ 8), Nat.or_comm,
    ← Nat.two_pow_add_eq_or_of_lt hbound, Nat.add_comm]

end Oak.Neon
