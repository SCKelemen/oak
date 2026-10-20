import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch029

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell483328 : Cell := ⟨Source.page472.take 452, 452, by simp only [List.length_take, List.length_drop, Source.size472] <;> rfl⟩
theorem gap483780 : (Source.page472.drop 452).take 1 = [10] := by rfl
def cell483781 : Cell := ⟨(Source.page472.drop 453).take 456, 456, by simp only [List.length_take, List.length_drop, Source.size472] <;> rfl⟩
theorem gap484237 : (Source.page472.drop 909).take 1 = [10] := by rfl
def cell484238 : Cell := ⟨(Source.page472.drop 910), 114, by simp only [List.length_take, List.length_drop, Source.size472] <;> rfl⟩
def coveredPage472 : Page := ⟨Source.page472, [cell483328, lf, cell483781, lf, cell484238], by
  have h := (cutBytes_cover [452, 1, 456, 1] Source.page472).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap483780, gap484237] at h
  exact h⟩
def cell484352 : Cell := ⟨Source.page473.take 219, 219, by simp only [List.length_take, List.length_drop, Source.size473] <;> rfl⟩
theorem gap484571 : (Source.page473.drop 219).take 1 = [10] := by rfl
def cell484572 : Cell := ⟨(Source.page473.drop 220).take 447, 447, by simp only [List.length_take, List.length_drop, Source.size473] <;> rfl⟩
theorem gap485019 : (Source.page473.drop 667).take 1 = [10] := by rfl
def cell485020 : Cell := ⟨(Source.page473.drop 668), 356, by simp only [List.length_take, List.length_drop, Source.size473] <;> rfl⟩
def coveredPage473 : Page := ⟨Source.page473, [cell484352, lf, cell484572, lf, cell485020], by
  have h := (cutBytes_cover [219, 1, 447, 1] Source.page473).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap484571, gap485019] at h
  exact h⟩
def cell485376 : Cell := ⟨Source.page474.take 92, 92, by simp only [List.length_take, List.length_drop, Source.size474] <;> rfl⟩
theorem gap485468 : (Source.page474.drop 92).take 1 = [10] := by rfl
def cell485469 : Cell := ⟨(Source.page474.drop 93).take 443, 443, by simp only [List.length_take, List.length_drop, Source.size474] <;> rfl⟩
theorem gap485912 : (Source.page474.drop 536).take 1 = [10] := by rfl
def cell485913 : Cell := ⟨(Source.page474.drop 537).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size474] <;> rfl⟩
theorem gap486339 : (Source.page474.drop 963).take 1 = [10] := by rfl
def cell486340 : Cell := ⟨(Source.page474.drop 964), 60, by simp only [List.length_take, List.length_drop, Source.size474] <;> rfl⟩
def coveredPage474 : Page := ⟨Source.page474, [cell485376, lf, cell485469, lf, cell485913, lf, cell486340], by
  have h := (cutBytes_cover [92, 1, 443, 1, 426, 1] Source.page474).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap485468, gap485912, gap486339] at h
  exact h⟩
def cell486400 : Cell := ⟨Source.page475.take 395, 395, by simp only [List.length_take, List.length_drop, Source.size475] <;> rfl⟩
theorem gap486795 : (Source.page475.drop 395).take 1 = [10] := by rfl
def cell486796 : Cell := ⟨(Source.page475.drop 396).take 414, 414, by simp only [List.length_take, List.length_drop, Source.size475] <;> rfl⟩
theorem gap487210 : (Source.page475.drop 810).take 1 = [10] := by rfl
def cell487211 : Cell := ⟨(Source.page475.drop 811), 213, by simp only [List.length_take, List.length_drop, Source.size475] <;> rfl⟩
def coveredPage475 : Page := ⟨Source.page475, [cell486400, lf, cell486796, lf, cell487211], by
  have h := (cutBytes_cover [395, 1, 414, 1] Source.page475).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap486795, gap487210] at h
  exact h⟩
def cell487424 : Cell := ⟨Source.page476.take 258, 258, by simp only [List.length_take, List.length_drop, Source.size476] <;> rfl⟩
theorem gap487682 : (Source.page476.drop 258).take 1 = [10] := by rfl
def cell487683 : Cell := ⟨(Source.page476.drop 259).take 465, 465, by simp only [List.length_take, List.length_drop, Source.size476] <;> rfl⟩
theorem gap488148 : (Source.page476.drop 724).take 1 = [10] := by rfl
def cell488149 : Cell := ⟨(Source.page476.drop 725), 299, by simp only [List.length_take, List.length_drop, Source.size476] <;> rfl⟩
def coveredPage476 : Page := ⟨Source.page476, [cell487424, lf, cell487683, lf, cell488149], by
  have h := (cutBytes_cover [258, 1, 465, 1] Source.page476).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap487682, gap488148] at h
  exact h⟩
def cell488448 : Cell := ⟨Source.page477.take 168, 168, by simp only [List.length_take, List.length_drop, Source.size477] <;> rfl⟩
theorem gap488616 : (Source.page477.drop 168).take 1 = [10] := by rfl
def cell488617 : Cell := ⟨(Source.page477.drop 169).take 411, 411, by simp only [List.length_take, List.length_drop, Source.size477] <;> rfl⟩
theorem gap489028 : (Source.page477.drop 580).take 1 = [10] := by rfl
def cell489029 : Cell := ⟨(Source.page477.drop 581), 443, by simp only [List.length_take, List.length_drop, Source.size477] <;> rfl⟩
def coveredPage477 : Page := ⟨Source.page477, [cell488448, lf, cell488617, lf, cell489029], by
  have h := (cutBytes_cover [168, 1, 411, 1] Source.page477).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap488616, gap489028] at h
  exact h⟩
def cell489472 : Cell := ⟨Source.page478.take 70, 70, by simp only [List.length_take, List.length_drop, Source.size478] <;> rfl⟩
theorem gap489542 : (Source.page478.drop 70).take 1 = [10] := by rfl
def cell489543 : Cell := ⟨(Source.page478.drop 71).take 532, 532, by simp only [List.length_take, List.length_drop, Source.size478] <;> rfl⟩
theorem gap490075 : (Source.page478.drop 603).take 1 = [10] := by rfl
def cell490076 : Cell := ⟨(Source.page478.drop 604), 420, by simp only [List.length_take, List.length_drop, Source.size478] <;> rfl⟩
def coveredPage478 : Page := ⟨Source.page478, [cell489472, lf, cell489543, lf, cell490076], by
  have h := (cutBytes_cover [70, 1, 532, 1] Source.page478).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap489542, gap490075] at h
  exact h⟩
def cell490496 : Cell := ⟨Source.page479.take 20, 20, by simp only [List.length_take, List.length_drop, Source.size479] <;> rfl⟩
theorem gap490516 : (Source.page479.drop 20).take 1 = [10] := by rfl
def cell490517 : Cell := ⟨(Source.page479.drop 21).take 228, 228, by simp only [List.length_take, List.length_drop, Source.size479] <;> rfl⟩
theorem gap490745 : (Source.page479.drop 249).take 1 = [10] := by rfl
def cell490746 : Cell := ⟨(Source.page479.drop 250).take 545, 545, by simp only [List.length_take, List.length_drop, Source.size479] <;> rfl⟩
theorem gap491291 : (Source.page479.drop 795).take 1 = [10] := by rfl
def cell491292 : Cell := ⟨(Source.page479.drop 796), 228, by simp only [List.length_take, List.length_drop, Source.size479] <;> rfl⟩
def coveredPage479 : Page := ⟨Source.page479, [cell490496, lf, cell490517, lf, cell490746, lf, cell491292], by
  have h := (cutBytes_cover [20, 1, 228, 1, 545, 1] Source.page479).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap490516, gap490745, gap491291] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
