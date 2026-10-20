import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch032

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell524288 : Cell := ⟨Source.page512.take 37, 37, by simp only [List.length_take, List.length_drop, Source.size512] <;> rfl⟩
theorem gap524325 : (Source.page512.drop 37).take 1 = [10] := by rfl
def cell524326 : Cell := ⟨(Source.page512.drop 38).take 492, 492, by simp only [List.length_take, List.length_drop, Source.size512] <;> rfl⟩
theorem gap524818 : (Source.page512.drop 530).take 1 = [10] := by rfl
def cell524819 : Cell := ⟨(Source.page512.drop 531), 493, by simp only [List.length_take, List.length_drop, Source.size512] <;> rfl⟩
def coveredPage512 : Page := ⟨Source.page512, [cell524288, lf, cell524326, lf, cell524819], by
  have h := (cutBytes_cover [37, 1, 492, 1] Source.page512).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap524325, gap524818] at h
  exact h⟩
def cell525312 : Cell := ⟨Source.page513.take 43, 43, by simp only [List.length_take, List.length_drop, Source.size513] <;> rfl⟩
theorem gap525355 : (Source.page513.drop 43).take 1 = [10] := by rfl
def cell525356 : Cell := ⟨(Source.page513.drop 44).take 323, 323, by simp only [List.length_take, List.length_drop, Source.size513] <;> rfl⟩
theorem gap525679 : (Source.page513.drop 367).take 1 = [10] := by rfl
def cell525680 : Cell := ⟨(Source.page513.drop 368).take 522, 522, by simp only [List.length_take, List.length_drop, Source.size513] <;> rfl⟩
theorem gap526202 : (Source.page513.drop 890).take 1 = [10] := by rfl
def cell526203 : Cell := ⟨(Source.page513.drop 891), 133, by simp only [List.length_take, List.length_drop, Source.size513] <;> rfl⟩
def coveredPage513 : Page := ⟨Source.page513, [cell525312, lf, cell525356, lf, cell525680, lf, cell526203], by
  have h := (cutBytes_cover [43, 1, 323, 1, 522, 1] Source.page513).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap525355, gap525679, gap526202] at h
  exact h⟩
def cell526336 : Cell := ⟨Source.page514.take 363, 363, by simp only [List.length_take, List.length_drop, Source.size514] <;> rfl⟩
theorem gap526699 : (Source.page514.drop 363).take 1 = [10] := by rfl
def cell526700 : Cell := ⟨(Source.page514.drop 364).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size514] <;> rfl⟩
theorem gap527171 : (Source.page514.drop 835).take 1 = [10] := by rfl
def cell527172 : Cell := ⟨(Source.page514.drop 836), 188, by simp only [List.length_take, List.length_drop, Source.size514] <;> rfl⟩
def coveredPage514 : Page := ⟨Source.page514, [cell526336, lf, cell526700, lf, cell527172], by
  have h := (cutBytes_cover [363, 1, 471, 1] Source.page514).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap526699, gap527171] at h
  exact h⟩
def cell527360 : Cell := ⟨Source.page515.take 209, 209, by simp only [List.length_take, List.length_drop, Source.size515] <;> rfl⟩
theorem gap527569 : (Source.page515.drop 209).take 1 = [10] := by rfl
def cell527570 : Cell := ⟨(Source.page515.drop 210).take 381, 381, by simp only [List.length_take, List.length_drop, Source.size515] <;> rfl⟩
theorem gap527951 : (Source.page515.drop 591).take 1 = [10] := by rfl
def cell527952 : Cell := ⟨(Source.page515.drop 592), 432, by simp only [List.length_take, List.length_drop, Source.size515] <;> rfl⟩
def coveredPage515 : Page := ⟨Source.page515, [cell527360, lf, cell527570, lf, cell527952], by
  have h := (cutBytes_cover [209, 1, 381, 1] Source.page515).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap527569, gap527951] at h
  exact h⟩
def cell528384 : Cell := ⟨Source.page516.take 60, 60, by simp only [List.length_take, List.length_drop, Source.size516] <;> rfl⟩
theorem gap528444 : (Source.page516.drop 60).take 1 = [10] := by rfl
def cell528445 : Cell := ⟨(Source.page516.drop 61).take 494, 494, by simp only [List.length_take, List.length_drop, Source.size516] <;> rfl⟩
theorem gap528939 : (Source.page516.drop 555).take 1 = [10] := by rfl
def cell528940 : Cell := ⟨(Source.page516.drop 556), 468, by simp only [List.length_take, List.length_drop, Source.size516] <;> rfl⟩
def coveredPage516 : Page := ⟨Source.page516, [cell528384, lf, cell528445, lf, cell528940], by
  have h := (cutBytes_cover [60, 1, 494, 1] Source.page516).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap528444, gap528939] at h
  exact h⟩
def cell529408 : Cell := ⟨Source.page517.take 60, 60, by simp only [List.length_take, List.length_drop, Source.size517] <;> rfl⟩
theorem gap529468 : (Source.page517.drop 60).take 1 = [10] := by rfl
def cell529469 : Cell := ⟨(Source.page517.drop 61).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size517] <;> rfl⟩
theorem gap529949 : (Source.page517.drop 541).take 1 = [10] := by rfl
def cell529950 : Cell := ⟨(Source.page517.drop 542).take 299, 299, by simp only [List.length_take, List.length_drop, Source.size517] <;> rfl⟩
theorem gap530249 : (Source.page517.drop 841).take 1 = [10] := by rfl
def cell530250 : Cell := ⟨(Source.page517.drop 842), 182, by simp only [List.length_take, List.length_drop, Source.size517] <;> rfl⟩
def coveredPage517 : Page := ⟨Source.page517, [cell529408, lf, cell529469, lf, cell529950, lf, cell530250], by
  have h := (cutBytes_cover [60, 1, 480, 1, 299, 1] Source.page517).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap529468, gap529949, gap530249] at h
  exact h⟩
def cell530432 : Cell := ⟨Source.page518.take 244, 244, by simp only [List.length_take, List.length_drop, Source.size518] <;> rfl⟩
theorem gap530676 : (Source.page518.drop 244).take 1 = [10] := by rfl
def cell530677 : Cell := ⟨(Source.page518.drop 245).take 447, 447, by simp only [List.length_take, List.length_drop, Source.size518] <;> rfl⟩
theorem gap531124 : (Source.page518.drop 692).take 1 = [10] := by rfl
def cell531125 : Cell := ⟨(Source.page518.drop 693), 331, by simp only [List.length_take, List.length_drop, Source.size518] <;> rfl⟩
def coveredPage518 : Page := ⟨Source.page518, [cell530432, lf, cell530677, lf, cell531125], by
  have h := (cutBytes_cover [244, 1, 447, 1] Source.page518).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap530676, gap531124] at h
  exact h⟩
def cell531456 : Cell := ⟨Source.page519.take 206, 206, by simp only [List.length_take, List.length_drop, Source.size519] <;> rfl⟩
theorem gap531662 : (Source.page519.drop 206).take 1 = [10] := by rfl
def cell531663 : Cell := ⟨(Source.page519.drop 207).take 421, 421, by simp only [List.length_take, List.length_drop, Source.size519] <;> rfl⟩
theorem gap532084 : (Source.page519.drop 628).take 1 = [10] := by rfl
def cell532085 : Cell := ⟨(Source.page519.drop 629), 395, by simp only [List.length_take, List.length_drop, Source.size519] <;> rfl⟩
def coveredPage519 : Page := ⟨Source.page519, [cell531456, lf, cell531663, lf, cell532085], by
  have h := (cutBytes_cover [206, 1, 421, 1] Source.page519).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap531662, gap532084] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
