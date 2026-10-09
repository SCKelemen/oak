import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch047

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell770048 : Cell := ⟨Source.page752.take 208, 208, by simp only [List.length_take, List.length_drop, Source.size752] <;> rfl⟩
theorem gap770256 : (Source.page752.drop 208).take 1 = [10] := by rfl
def cell770257 : Cell := ⟨(Source.page752.drop 209).take 441, 441, by simp only [List.length_take, List.length_drop, Source.size752] <;> rfl⟩
theorem gap770698 : (Source.page752.drop 650).take 1 = [10] := by rfl
def cell770699 : Cell := ⟨(Source.page752.drop 651).take 334, 334, by simp only [List.length_take, List.length_drop, Source.size752] <;> rfl⟩
theorem gap771033 : (Source.page752.drop 985).take 1 = [10] := by rfl
def cell771034 : Cell := ⟨(Source.page752.drop 986), 38, by simp only [List.length_take, List.length_drop, Source.size752] <;> rfl⟩
def coveredPage752 : Page := ⟨Source.page752, [cell770048, lf, cell770257, lf, cell770699, lf, cell771034], by
  have h := (cutBytes_cover [208, 1, 441, 1, 334, 1] Source.page752).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap770256, gap770698, gap771033] at h
  exact h⟩
def cell771072 : Cell := ⟨Source.page753.take 396, 396, by simp only [List.length_take, List.length_drop, Source.size753] <;> rfl⟩
theorem gap771468 : (Source.page753.drop 396).take 1 = [10] := by rfl
def cell771469 : Cell := ⟨(Source.page753.drop 397).take 407, 407, by simp only [List.length_take, List.length_drop, Source.size753] <;> rfl⟩
theorem gap771876 : (Source.page753.drop 804).take 1 = [10] := by rfl
def cell771877 : Cell := ⟨(Source.page753.drop 805), 219, by simp only [List.length_take, List.length_drop, Source.size753] <;> rfl⟩
def coveredPage753 : Page := ⟨Source.page753, [cell771072, lf, cell771469, lf, cell771877], by
  have h := (cutBytes_cover [396, 1, 407, 1] Source.page753).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap771468, gap771876] at h
  exact h⟩
def cell772096 : Cell := ⟨Source.page754.take 335, 335, by simp only [List.length_take, List.length_drop, Source.size754] <;> rfl⟩
theorem gap772431 : (Source.page754.drop 335).take 1 = [10] := by rfl
def cell772432 : Cell := ⟨(Source.page754.drop 336).take 474, 474, by simp only [List.length_take, List.length_drop, Source.size754] <;> rfl⟩
theorem gap772906 : (Source.page754.drop 810).take 1 = [10] := by rfl
def cell772907 : Cell := ⟨(Source.page754.drop 811), 213, by simp only [List.length_take, List.length_drop, Source.size754] <;> rfl⟩
def coveredPage754 : Page := ⟨Source.page754, [cell772096, lf, cell772432, lf, cell772907], by
  have h := (cutBytes_cover [335, 1, 474, 1] Source.page754).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap772431, gap772906] at h
  exact h⟩
def cell773120 : Cell := ⟨Source.page755.take 156, 156, by simp only [List.length_take, List.length_drop, Source.size755] <;> rfl⟩
theorem gap773276 : (Source.page755.drop 156).take 1 = [10] := by rfl
def cell773277 : Cell := ⟨(Source.page755.drop 157).take 497, 497, by simp only [List.length_take, List.length_drop, Source.size755] <;> rfl⟩
theorem gap773774 : (Source.page755.drop 654).take 1 = [10] := by rfl
def cell773775 : Cell := ⟨(Source.page755.drop 655), 369, by simp only [List.length_take, List.length_drop, Source.size755] <;> rfl⟩
def coveredPage755 : Page := ⟨Source.page755, [cell773120, lf, cell773277, lf, cell773775], by
  have h := (cutBytes_cover [156, 1, 497, 1] Source.page755).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap773276, gap773774] at h
  exact h⟩
def cell774144 : Cell := ⟨Source.page756.take 144, 144, by simp only [List.length_take, List.length_drop, Source.size756] <;> rfl⟩
theorem gap774288 : (Source.page756.drop 144).take 1 = [10] := by rfl
def cell774289 : Cell := ⟨(Source.page756.drop 145).take 572, 572, by simp only [List.length_take, List.length_drop, Source.size756] <;> rfl⟩
theorem gap774861 : (Source.page756.drop 717).take 1 = [10] := by rfl
def cell774862 : Cell := ⟨(Source.page756.drop 718), 306, by simp only [List.length_take, List.length_drop, Source.size756] <;> rfl⟩
def coveredPage756 : Page := ⟨Source.page756, [cell774144, lf, cell774289, lf, cell774862], by
  have h := (cutBytes_cover [144, 1, 572, 1] Source.page756).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap774288, gap774861] at h
  exact h⟩
def cell775168 : Cell := ⟨Source.page757.take 178, 178, by simp only [List.length_take, List.length_drop, Source.size757] <;> rfl⟩
theorem gap775346 : (Source.page757.drop 178).take 1 = [10] := by rfl
def cell775347 : Cell := ⟨(Source.page757.drop 179).take 465, 465, by simp only [List.length_take, List.length_drop, Source.size757] <;> rfl⟩
theorem gap775812 : (Source.page757.drop 644).take 1 = [10] := by rfl
def cell775813 : Cell := ⟨(Source.page757.drop 645), 379, by simp only [List.length_take, List.length_drop, Source.size757] <;> rfl⟩
def coveredPage757 : Page := ⟨Source.page757, [cell775168, lf, cell775347, lf, cell775813], by
  have h := (cutBytes_cover [178, 1, 465, 1] Source.page757).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap775346, gap775812] at h
  exact h⟩
def cell776192 : Cell := ⟨Source.page758.take 117, 117, by simp only [List.length_take, List.length_drop, Source.size758] <;> rfl⟩
theorem gap776309 : (Source.page758.drop 117).take 1 = [10] := by rfl
def cell776310 : Cell := ⟨(Source.page758.drop 118).take 621, 621, by simp only [List.length_take, List.length_drop, Source.size758] <;> rfl⟩
theorem gap776931 : (Source.page758.drop 739).take 1 = [10] := by rfl
def cell776932 : Cell := ⟨(Source.page758.drop 740), 284, by simp only [List.length_take, List.length_drop, Source.size758] <;> rfl⟩
def coveredPage758 : Page := ⟨Source.page758, [cell776192, lf, cell776310, lf, cell776932], by
  have h := (cutBytes_cover [117, 1, 621, 1] Source.page758).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap776309, gap776931] at h
  exact h⟩
def cell777216 : Cell := ⟨Source.page759.take 78, 78, by simp only [List.length_take, List.length_drop, Source.size759] <;> rfl⟩
theorem gap777294 : (Source.page759.drop 78).take 1 = [10] := by rfl
def cell777295 : Cell := ⟨(Source.page759.drop 79).take 502, 502, by simp only [List.length_take, List.length_drop, Source.size759] <;> rfl⟩
theorem gap777797 : (Source.page759.drop 581).take 1 = [10] := by rfl
def cell777798 : Cell := ⟨(Source.page759.drop 582), 442, by simp only [List.length_take, List.length_drop, Source.size759] <;> rfl⟩
def coveredPage759 : Page := ⟨Source.page759, [cell777216, lf, cell777295, lf, cell777798], by
  have h := (cutBytes_cover [78, 1, 502, 1] Source.page759).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap777294, gap777797] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
