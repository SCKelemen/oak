import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch042

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell688128 : Cell := ⟨Source.page672.take 78, 78, by simp only [List.length_take, List.length_drop, Source.size672] <;> rfl⟩
theorem gap688206 : (Source.page672.drop 78).take 1 = [10] := by rfl
def cell688207 : Cell := ⟨(Source.page672.drop 79).take 474, 474, by simp only [List.length_take, List.length_drop, Source.size672] <;> rfl⟩
theorem gap688681 : (Source.page672.drop 553).take 1 = [10] := by rfl
def cell688682 : Cell := ⟨(Source.page672.drop 554), 470, by simp only [List.length_take, List.length_drop, Source.size672] <;> rfl⟩
def coveredPage672 : Page := ⟨Source.page672, [cell688128, lf, cell688207, lf, cell688682], by
  have h := (cutBytes_cover [78, 1, 474, 1] Source.page672).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap688206, gap688681] at h
  exact h⟩
def cell689152 : Cell := ⟨Source.page673.take 8, 8, by simp only [List.length_take, List.length_drop, Source.size673] <;> rfl⟩
theorem gap689160 : (Source.page673.drop 8).take 1 = [10] := by rfl
def cell689161 : Cell := ⟨(Source.page673.drop 9).take 425, 425, by simp only [List.length_take, List.length_drop, Source.size673] <;> rfl⟩
theorem gap689586 : (Source.page673.drop 434).take 1 = [10] := by rfl
def cell689587 : Cell := ⟨(Source.page673.drop 435).take 440, 440, by simp only [List.length_take, List.length_drop, Source.size673] <;> rfl⟩
theorem gap690027 : (Source.page673.drop 875).take 1 = [10] := by rfl
def cell690028 : Cell := ⟨(Source.page673.drop 876), 148, by simp only [List.length_take, List.length_drop, Source.size673] <;> rfl⟩
def coveredPage673 : Page := ⟨Source.page673, [cell689152, lf, cell689161, lf, cell689587, lf, cell690028], by
  have h := (cutBytes_cover [8, 1, 425, 1, 440, 1] Source.page673).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap689160, gap689586, gap690027] at h
  exact h⟩
def cell690176 : Cell := ⟨Source.page674.take 351, 351, by simp only [List.length_take, List.length_drop, Source.size674] <;> rfl⟩
theorem gap690527 : (Source.page674.drop 351).take 1 = [10] := by rfl
def cell690528 : Cell := ⟨(Source.page674.drop 352).take 462, 462, by simp only [List.length_take, List.length_drop, Source.size674] <;> rfl⟩
theorem gap690990 : (Source.page674.drop 814).take 1 = [10] := by rfl
def cell690991 : Cell := ⟨(Source.page674.drop 815), 209, by simp only [List.length_take, List.length_drop, Source.size674] <;> rfl⟩
def coveredPage674 : Page := ⟨Source.page674, [cell690176, lf, cell690528, lf, cell690991], by
  have h := (cutBytes_cover [351, 1, 462, 1] Source.page674).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap690527, gap690990] at h
  exact h⟩
def cell691200 : Cell := ⟨Source.page675.take 323, 323, by simp only [List.length_take, List.length_drop, Source.size675] <;> rfl⟩
theorem gap691523 : (Source.page675.drop 323).take 1 = [10] := by rfl
def cell691524 : Cell := ⟨(Source.page675.drop 324).take 369, 369, by simp only [List.length_take, List.length_drop, Source.size675] <;> rfl⟩
theorem gap691893 : (Source.page675.drop 693).take 1 = [10] := by rfl
def cell691894 : Cell := ⟨(Source.page675.drop 694), 330, by simp only [List.length_take, List.length_drop, Source.size675] <;> rfl⟩
def coveredPage675 : Page := ⟨Source.page675, [cell691200, lf, cell691524, lf, cell691894], by
  have h := (cutBytes_cover [323, 1, 369, 1] Source.page675).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap691523, gap691893] at h
  exact h⟩
def cell692224 : Cell := ⟨Source.page676.take 40, 40, by simp only [List.length_take, List.length_drop, Source.size676] <;> rfl⟩
theorem gap692264 : (Source.page676.drop 40).take 1 = [10] := by rfl
def cell692265 : Cell := ⟨(Source.page676.drop 41).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size676] <;> rfl⟩
theorem gap692772 : (Source.page676.drop 548).take 1 = [10] := by rfl
def cell692773 : Cell := ⟨(Source.page676.drop 549), 475, by simp only [List.length_take, List.length_drop, Source.size676] <;> rfl⟩
def coveredPage676 : Page := ⟨Source.page676, [cell692224, lf, cell692265, lf, cell692773], by
  have h := (cutBytes_cover [40, 1, 507, 1] Source.page676).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap692264, gap692772] at h
  exact h⟩
def cell693248 : Cell := ⟨Source.page677.take 70, 70, by simp only [List.length_take, List.length_drop, Source.size677] <;> rfl⟩
theorem gap693318 : (Source.page677.drop 70).take 1 = [10] := by rfl
def cell693319 : Cell := ⟨(Source.page677.drop 71).take 514, 514, by simp only [List.length_take, List.length_drop, Source.size677] <;> rfl⟩
theorem gap693833 : (Source.page677.drop 585).take 1 = [10] := by rfl
def cell693834 : Cell := ⟨(Source.page677.drop 586), 438, by simp only [List.length_take, List.length_drop, Source.size677] <;> rfl⟩
def coveredPage677 : Page := ⟨Source.page677, [cell693248, lf, cell693319, lf, cell693834], by
  have h := (cutBytes_cover [70, 1, 514, 1] Source.page677).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap693318, gap693833] at h
  exact h⟩
def cell694272 : Cell := ⟨Source.page678.take 10, 10, by simp only [List.length_take, List.length_drop, Source.size678] <;> rfl⟩
theorem gap694282 : (Source.page678.drop 10).take 1 = [10] := by rfl
def cell694283 : Cell := ⟨(Source.page678.drop 11).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size678] <;> rfl⟩
theorem gap694763 : (Source.page678.drop 491).take 1 = [10] := by rfl
def cell694764 : Cell := ⟨(Source.page678.drop 492), 532, by simp only [List.length_take, List.length_drop, Source.size678] <;> rfl⟩
def coveredPage678 : Page := ⟨Source.page678, [cell694272, lf, cell694283, lf, cell694764], by
  have h := (cutBytes_cover [10, 1, 480, 1] Source.page678).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap694282, gap694763] at h
  exact h⟩
def cell695296 : Cell := ⟨Source.page679.take 24, 24, by simp only [List.length_take, List.length_drop, Source.size679] <;> rfl⟩
theorem gap695320 : (Source.page679.drop 24).take 1 = [10] := by rfl
def cell695321 : Cell := ⟨(Source.page679.drop 25).take 433, 433, by simp only [List.length_take, List.length_drop, Source.size679] <;> rfl⟩
theorem gap695754 : (Source.page679.drop 458).take 1 = [10] := by rfl
def cell695755 : Cell := ⟨(Source.page679.drop 459).take 423, 423, by simp only [List.length_take, List.length_drop, Source.size679] <;> rfl⟩
theorem gap696178 : (Source.page679.drop 882).take 1 = [10] := by rfl
def cell696179 : Cell := ⟨(Source.page679.drop 883), 141, by simp only [List.length_take, List.length_drop, Source.size679] <;> rfl⟩
def coveredPage679 : Page := ⟨Source.page679, [cell695296, lf, cell695321, lf, cell695755, lf, cell696179], by
  have h := (cutBytes_cover [24, 1, 433, 1, 423, 1] Source.page679).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap695320, gap695754, gap696178] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
