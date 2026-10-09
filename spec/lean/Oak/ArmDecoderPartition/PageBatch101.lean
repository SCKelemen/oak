import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch050

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell827392 : Cell := ⟨Source.page808.take 34, 34, by simp only [List.length_take, List.length_drop, Source.size808] <;> rfl⟩
theorem gap827426 : (Source.page808.drop 34).take 1 = [10] := by rfl
def cell827427 : Cell := ⟨(Source.page808.drop 35).take 504, 504, by simp only [List.length_take, List.length_drop, Source.size808] <;> rfl⟩
theorem gap827931 : (Source.page808.drop 539).take 1 = [10] := by rfl
def cell827932 : Cell := ⟨(Source.page808.drop 540).take 459, 459, by simp only [List.length_take, List.length_drop, Source.size808] <;> rfl⟩
theorem gap828391 : (Source.page808.drop 999).take 1 = [10] := by rfl
def cell828392 : Cell := ⟨(Source.page808.drop 1000), 24, by simp only [List.length_take, List.length_drop, Source.size808] <;> rfl⟩
def coveredPage808 : Page := ⟨Source.page808, [cell827392, lf, cell827427, lf, cell827932, lf, cell828392], by
  have h := (cutBytes_cover [34, 1, 504, 1, 459, 1] Source.page808).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap827426, gap827931, gap828391] at h
  exact h⟩
def cell828416 : Cell := ⟨Source.page809.take 453, 453, by simp only [List.length_take, List.length_drop, Source.size809] <;> rfl⟩
theorem gap828869 : (Source.page809.drop 453).take 1 = [10] := by rfl
def cell828870 : Cell := ⟨(Source.page809.drop 454).take 369, 369, by simp only [List.length_take, List.length_drop, Source.size809] <;> rfl⟩
theorem gap829239 : (Source.page809.drop 823).take 1 = [10] := by rfl
def cell829240 : Cell := ⟨(Source.page809.drop 824), 200, by simp only [List.length_take, List.length_drop, Source.size809] <;> rfl⟩
def coveredPage809 : Page := ⟨Source.page809, [cell828416, lf, cell828870, lf, cell829240], by
  have h := (cutBytes_cover [453, 1, 369, 1] Source.page809).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap828869, gap829239] at h
  exact h⟩
def cell829440 : Cell := ⟨Source.page810.take 203, 203, by simp only [List.length_take, List.length_drop, Source.size810] <;> rfl⟩
theorem gap829643 : (Source.page810.drop 203).take 1 = [10] := by rfl
def cell829644 : Cell := ⟨(Source.page810.drop 204).take 432, 432, by simp only [List.length_take, List.length_drop, Source.size810] <;> rfl⟩
theorem gap830076 : (Source.page810.drop 636).take 1 = [10] := by rfl
def cell830077 : Cell := ⟨(Source.page810.drop 637).take 324, 324, by simp only [List.length_take, List.length_drop, Source.size810] <;> rfl⟩
theorem gap830401 : (Source.page810.drop 961).take 1 = [10] := by rfl
def cell830402 : Cell := ⟨(Source.page810.drop 962), 62, by simp only [List.length_take, List.length_drop, Source.size810] <;> rfl⟩
def coveredPage810 : Page := ⟨Source.page810, [cell829440, lf, cell829644, lf, cell830077, lf, cell830402], by
  have h := (cutBytes_cover [203, 1, 432, 1, 324, 1] Source.page810).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap829643, gap830076, gap830401] at h
  exact h⟩
def cell830464 : Cell := ⟨Source.page811.take 397, 397, by simp only [List.length_take, List.length_drop, Source.size811] <;> rfl⟩
theorem gap830861 : (Source.page811.drop 397).take 1 = [10] := by rfl
def cell830862 : Cell := ⟨(Source.page811.drop 398).take 517, 517, by simp only [List.length_take, List.length_drop, Source.size811] <;> rfl⟩
theorem gap831379 : (Source.page811.drop 915).take 1 = [10] := by rfl
def cell831380 : Cell := ⟨(Source.page811.drop 916), 108, by simp only [List.length_take, List.length_drop, Source.size811] <;> rfl⟩
def coveredPage811 : Page := ⟨Source.page811, [cell830464, lf, cell830862, lf, cell831380], by
  have h := (cutBytes_cover [397, 1, 517, 1] Source.page811).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap830861, gap831379] at h
  exact h⟩
def cell831488 : Cell := ⟨Source.page812.take 445, 445, by simp only [List.length_take, List.length_drop, Source.size812] <;> rfl⟩
theorem gap831933 : (Source.page812.drop 445).take 1 = [10] := by rfl
def cell831934 : Cell := ⟨(Source.page812.drop 446).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size812] <;> rfl⟩
theorem gap832405 : (Source.page812.drop 917).take 1 = [10] := by rfl
def cell832406 : Cell := ⟨(Source.page812.drop 918), 106, by simp only [List.length_take, List.length_drop, Source.size812] <;> rfl⟩
def coveredPage812 : Page := ⟨Source.page812, [cell831488, lf, cell831934, lf, cell832406], by
  have h := (cutBytes_cover [445, 1, 471, 1] Source.page812).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap831933, gap832405] at h
  exact h⟩
def cell832512 : Cell := ⟨Source.page813.take 307, 307, by simp only [List.length_take, List.length_drop, Source.size813] <;> rfl⟩
theorem gap832819 : (Source.page813.drop 307).take 1 = [10] := by rfl
def cell832820 : Cell := ⟨(Source.page813.drop 308), 554, by simp only [List.length_take, List.length_drop, Source.size813] <;> rfl⟩
def coveredPage813 : Page := ⟨Source.page813, [cell832512, lf, cell832820], by
  have h := (cutBytes_cover [307, 1] Source.page813).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap832819] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
