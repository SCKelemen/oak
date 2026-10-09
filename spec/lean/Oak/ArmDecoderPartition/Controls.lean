import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Controls

def checkFile (source pre : Bytes) (clauses : List Bytes) : Bool :=
  source == pre ++ separatedBytes id clauses

theorem checkFile_sound {source pre : Bytes} {clauses : List Bytes}
    (h : checkFile source pre clauses = true) :
    source = pre ++ separatedBytes id clauses := by
  simpa [checkFile] using h

def pre : Bytes := [80,10]
def a : Bytes := [65,10]
def b : Bytes := [66,10]
def c : Bytes := [67,10]
def original : Bytes := [80,10,65,10,10,66,10,10,67,10]

theorem accepts_complete : checkFile original pre [a,b,c] = true := by rfl
theorem rejects_removed : checkFile original pre [a,c] = false := by rfl
theorem rejects_duplicate : checkFile original pre [a,b,b,c] = false := by rfl
theorem rejects_reordered : checkFile original pre [b,a,c] = false := by rfl
theorem rejects_missing_newline :
    checkFile [80,10,65,10,66,10,10,67,10] pre [a,b,c] = false := by rfl
theorem rejects_injected_separator :
    checkFile [80,10,65,10,10,88,66,10,10,67,10] pre [a,b,c] = false := by rfl
theorem rejects_early_prefix : checkFile original [80] [a,b,c] = false := by rfl
theorem rejects_late_prefix : checkFile original [80,10,65] [a,b,c] = false := by rfl
theorem rejects_extra_suffix : checkFile (original ++ [0]) pre [a,b,c] = false := by rfl
theorem rejects_wrong_independent_octet :
    checkFile [81,10,65,10,10,66,10,10,67,10] pre [a,b,c] = false := by rfl

/-- Exhaustive cuts retain the final tail even if the size list omits it. -/
theorem cuts_keep_tail : cutBytes [2] [1,2,3,4] = [[1,2],[3,4]] := by rfl
theorem rejects_gap_cells : ([1,2,3,4] : Bytes) != ([1,2] ++ [4]) := by decide +kernel
theorem rejects_overlap_cells : ([1,2,3,4] : Bytes) != ([1,2] ++ [2,3,4]) := by decide +kernel

def left : Bytes := [100,101,99,111] -- deco
def right : Bytes := [100,101,54,52] -- de64

theorem cross_page_marker : (scan left (scan right)).2 = 1 := by rfl
theorem isolated_page_counts_lose_marker : (scan left).2 + (scan right).2 = 0 := by rfl
theorem cross_page_marker_exact : occurrences (left ++ right) = 1 := by rfl
theorem missing_marker_byte : occurrences [100,101,99,111,100,54,52] = 0 := by rfl

theorem declaration_newline_crossing :
    (scan [10] (scan ([118,97,108,32] ++ left) (scan (right ++ [32,58,32,10])))).2 = 1 := by rfl

def anchoredLine : Bytes := rawBytes ["\nval decode64 : bits(32) -> unit\n"]
theorem anchored_line_across_pages :
    ([10] ++ rawBytes ["val deco"] ++ rawBytes ["de64 : bits(32) -> unit"] ++ [10] : Bytes) =
      anchoredLine := by rfl
theorem rejects_missing_anchor_newline :
    rawBytes ["val decode64 : bits(32) -> unit\n"] != anchoredLine := by decide +kernel
theorem rejects_missing_line_end :
    rawBytes ["\nval decode64 : bits(32) -> unit"] != anchoredLine := by decide +kernel

theorem unpack_little_endian : unpack 2 16961 = [65,66] := by rfl
theorem wrong_packed_byte : unpack 2 16960 != ([65,66] : Bytes) := by decide +kernel

end Oak.ArmDecoderPartition.Controls
