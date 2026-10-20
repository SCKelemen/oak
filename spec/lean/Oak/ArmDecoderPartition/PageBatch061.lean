import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch030

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell499712 : Cell := ⟨Source.page488.take 324, 324, by simp only [List.length_take, List.length_drop, Source.size488] <;> rfl⟩
theorem gap500036 : (Source.page488.drop 324).take 1 = [10] := by rfl
def cell500037 : Cell := ⟨(Source.page488.drop 325).take 459, 459, by simp only [List.length_take, List.length_drop, Source.size488] <;> rfl⟩
theorem gap500496 : (Source.page488.drop 784).take 1 = [10] := by rfl
def cell500497 : Cell := ⟨(Source.page488.drop 785), 239, by simp only [List.length_take, List.length_drop, Source.size488] <;> rfl⟩
def coveredPage488 : Page := ⟨Source.page488, [cell499712, lf, cell500037, lf, cell500497], by
  have h := (cutBytes_cover [324, 1, 459, 1] Source.page488).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap500036, gap500496] at h
  exact h⟩
def cell500736 : Cell := ⟨Source.page489.take 196, 196, by simp only [List.length_take, List.length_drop, Source.size489] <;> rfl⟩
theorem gap500932 : (Source.page489.drop 196).take 1 = [10] := by rfl
def cell500933 : Cell := ⟨(Source.page489.drop 197).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size489] <;> rfl⟩
theorem gap501359 : (Source.page489.drop 623).take 1 = [10] := by rfl
def cell501360 : Cell := ⟨(Source.page489.drop 624), 400, by simp only [List.length_take, List.length_drop, Source.size489] <;> rfl⟩
def coveredPage489 : Page := ⟨Source.page489, [cell500736, lf, cell500933, lf, cell501360], by
  have h := (cutBytes_cover [196, 1, 426, 1] Source.page489).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap500932, gap501359] at h
  exact h⟩
def cell501760 : Cell := ⟨Source.page490.take 30, 30, by simp only [List.length_take, List.length_drop, Source.size490] <;> rfl⟩
theorem gap501790 : (Source.page490.drop 30).take 1 = [10] := by rfl
def cell501791 : Cell := ⟨(Source.page490.drop 31).take 530, 530, by simp only [List.length_take, List.length_drop, Source.size490] <;> rfl⟩
theorem gap502321 : (Source.page490.drop 561).take 1 = [10] := by rfl
def cell502322 : Cell := ⟨(Source.page490.drop 562), 462, by simp only [List.length_take, List.length_drop, Source.size490] <;> rfl⟩
def coveredPage490 : Page := ⟨Source.page490, [cell501760, lf, cell501791, lf, cell502322], by
  have h := (cutBytes_cover [30, 1, 530, 1] Source.page490).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap501790, gap502321] at h
  exact h⟩
def cell502784 : Cell := ⟨Source.page491.take 34, 34, by simp only [List.length_take, List.length_drop, Source.size491] <;> rfl⟩
theorem gap502818 : (Source.page491.drop 34).take 1 = [10] := by rfl
def cell502819 : Cell := ⟨(Source.page491.drop 35).take 436, 436, by simp only [List.length_take, List.length_drop, Source.size491] <;> rfl⟩
theorem gap503255 : (Source.page491.drop 471).take 1 = [10] := by rfl
def cell503256 : Cell := ⟨(Source.page491.drop 472).take 516, 516, by simp only [List.length_take, List.length_drop, Source.size491] <;> rfl⟩
theorem gap503772 : (Source.page491.drop 988).take 1 = [10] := by rfl
def cell503773 : Cell := ⟨(Source.page491.drop 989), 35, by simp only [List.length_take, List.length_drop, Source.size491] <;> rfl⟩
def coveredPage491 : Page := ⟨Source.page491, [cell502784, lf, cell502819, lf, cell503256, lf, cell503773], by
  have h := (cutBytes_cover [34, 1, 436, 1, 516, 1] Source.page491).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap502818, gap503255, gap503772] at h
  exact h⟩
def cell503808 : Cell := ⟨Source.page492.take 472, 472, by simp only [List.length_take, List.length_drop, Source.size492] <;> rfl⟩
theorem gap504280 : (Source.page492.drop 472).take 1 = [10] := by rfl
def cell504281 : Cell := ⟨(Source.page492.drop 473).take 453, 453, by simp only [List.length_take, List.length_drop, Source.size492] <;> rfl⟩
theorem gap504734 : (Source.page492.drop 926).take 1 = [10] := by rfl
def cell504735 : Cell := ⟨(Source.page492.drop 927), 97, by simp only [List.length_take, List.length_drop, Source.size492] <;> rfl⟩
def coveredPage492 : Page := ⟨Source.page492, [cell503808, lf, cell504281, lf, cell504735], by
  have h := (cutBytes_cover [472, 1, 453, 1] Source.page492).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap504280, gap504734] at h
  exact h⟩
def cell504832 : Cell := ⟨Source.page493.take 441, 441, by simp only [List.length_take, List.length_drop, Source.size493] <;> rfl⟩
theorem gap505273 : (Source.page493.drop 441).take 1 = [10] := by rfl
def cell505274 : Cell := ⟨(Source.page493.drop 442).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size493] <;> rfl⟩
theorem gap505700 : (Source.page493.drop 868).take 1 = [10] := by rfl
def cell505701 : Cell := ⟨(Source.page493.drop 869), 155, by simp only [List.length_take, List.length_drop, Source.size493] <;> rfl⟩
def coveredPage493 : Page := ⟨Source.page493, [cell504832, lf, cell505274, lf, cell505701], by
  have h := (cutBytes_cover [441, 1, 426, 1] Source.page493).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap505273, gap505700] at h
  exact h⟩
def cell505856 : Cell := ⟨Source.page494.take 336, 336, by simp only [List.length_take, List.length_drop, Source.size494] <;> rfl⟩
theorem gap506192 : (Source.page494.drop 336).take 1 = [10] := by rfl
def cell506193 : Cell := ⟨(Source.page494.drop 337).take 465, 465, by simp only [List.length_take, List.length_drop, Source.size494] <;> rfl⟩
theorem gap506658 : (Source.page494.drop 802).take 1 = [10] := by rfl
def cell506659 : Cell := ⟨(Source.page494.drop 803), 221, by simp only [List.length_take, List.length_drop, Source.size494] <;> rfl⟩
def coveredPage494 : Page := ⟨Source.page494, [cell505856, lf, cell506193, lf, cell506659], by
  have h := (cutBytes_cover [336, 1, 465, 1] Source.page494).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap506192, gap506658] at h
  exact h⟩
def cell506880 : Cell := ⟨Source.page495.take 182, 182, by simp only [List.length_take, List.length_drop, Source.size495] <;> rfl⟩
theorem gap507062 : (Source.page495.drop 182).take 1 = [10] := by rfl
def cell507063 : Cell := ⟨(Source.page495.drop 183).take 322, 322, by simp only [List.length_take, List.length_drop, Source.size495] <;> rfl⟩
theorem gap507385 : (Source.page495.drop 505).take 1 = [10] := by rfl
def cell507386 : Cell := ⟨(Source.page495.drop 506).take 516, 516, by simp only [List.length_take, List.length_drop, Source.size495] <;> rfl⟩
theorem gap507902 : (Source.page495.drop 1022).take 1 = [10] := by rfl
def cell507903 : Cell := ⟨(Source.page495.drop 1023), 1, by simp only [List.length_take, List.length_drop, Source.size495] <;> rfl⟩
def coveredPage495 : Page := ⟨Source.page495, [cell506880, lf, cell507063, lf, cell507386, lf, cell507903], by
  have h := (cutBytes_cover [182, 1, 322, 1, 516, 1] Source.page495).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap507062, gap507385, gap507902] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
