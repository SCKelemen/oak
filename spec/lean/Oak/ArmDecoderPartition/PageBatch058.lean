import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch029

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell475136 : Cell := ⟨Source.page464.take 452, 452, by simp only [List.length_take, List.length_drop, Source.size464] <;> rfl⟩
theorem gap475588 : (Source.page464.drop 452).take 1 = [10] := by rfl
def cell475589 : Cell := ⟨(Source.page464.drop 453).take 514, 514, by simp only [List.length_take, List.length_drop, Source.size464] <;> rfl⟩
theorem gap476103 : (Source.page464.drop 967).take 1 = [10] := by rfl
def cell476104 : Cell := ⟨(Source.page464.drop 968), 56, by simp only [List.length_take, List.length_drop, Source.size464] <;> rfl⟩
def coveredPage464 : Page := ⟨Source.page464, [cell475136, lf, cell475589, lf, cell476104], by
  have h := (cutBytes_cover [452, 1, 514, 1] Source.page464).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap475588, gap476103] at h
  exact h⟩
def cell476160 : Cell := ⟨Source.page465.take 476, 476, by simp only [List.length_take, List.length_drop, Source.size465] <;> rfl⟩
theorem gap476636 : (Source.page465.drop 476).take 1 = [10] := by rfl
def cell476637 : Cell := ⟨(Source.page465.drop 477).take 400, 400, by simp only [List.length_take, List.length_drop, Source.size465] <;> rfl⟩
theorem gap477037 : (Source.page465.drop 877).take 1 = [10] := by rfl
def cell477038 : Cell := ⟨(Source.page465.drop 878), 146, by simp only [List.length_take, List.length_drop, Source.size465] <;> rfl⟩
def coveredPage465 : Page := ⟨Source.page465, [cell476160, lf, cell476637, lf, cell477038], by
  have h := (cutBytes_cover [476, 1, 400, 1] Source.page465).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap476636, gap477037] at h
  exact h⟩
def cell477184 : Cell := ⟨Source.page466.take 351, 351, by simp only [List.length_take, List.length_drop, Source.size466] <;> rfl⟩
theorem gap477535 : (Source.page466.drop 351).take 1 = [10] := by rfl
def cell477536 : Cell := ⟨(Source.page466.drop 352).take 420, 420, by simp only [List.length_take, List.length_drop, Source.size466] <;> rfl⟩
theorem gap477956 : (Source.page466.drop 772).take 1 = [10] := by rfl
def cell477957 : Cell := ⟨(Source.page466.drop 773), 251, by simp only [List.length_take, List.length_drop, Source.size466] <;> rfl⟩
def coveredPage466 : Page := ⟨Source.page466, [cell477184, lf, cell477536, lf, cell477957], by
  have h := (cutBytes_cover [351, 1, 420, 1] Source.page466).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap477535, gap477956] at h
  exact h⟩
def cell478208 : Cell := ⟨Source.page467.take 200, 200, by simp only [List.length_take, List.length_drop, Source.size467] <;> rfl⟩
theorem gap478408 : (Source.page467.drop 200).take 1 = [10] := by rfl
def cell478409 : Cell := ⟨(Source.page467.drop 201).take 446, 446, by simp only [List.length_take, List.length_drop, Source.size467] <;> rfl⟩
theorem gap478855 : (Source.page467.drop 647).take 1 = [10] := by rfl
def cell478856 : Cell := ⟨(Source.page467.drop 648), 376, by simp only [List.length_take, List.length_drop, Source.size467] <;> rfl⟩
def coveredPage467 : Page := ⟨Source.page467, [cell478208, lf, cell478409, lf, cell478856], by
  have h := (cutBytes_cover [200, 1, 446, 1] Source.page467).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap478408, gap478855] at h
  exact h⟩
def cell479232 : Cell := ⟨Source.page468.take 95, 95, by simp only [List.length_take, List.length_drop, Source.size468] <;> rfl⟩
theorem gap479327 : (Source.page468.drop 95).take 1 = [10] := by rfl
def cell479328 : Cell := ⟨(Source.page468.drop 96).take 462, 462, by simp only [List.length_take, List.length_drop, Source.size468] <;> rfl⟩
theorem gap479790 : (Source.page468.drop 558).take 1 = [10] := by rfl
def cell479791 : Cell := ⟨(Source.page468.drop 559), 465, by simp only [List.length_take, List.length_drop, Source.size468] <;> rfl⟩
def coveredPage468 : Page := ⟨Source.page468, [cell479232, lf, cell479328, lf, cell479791], by
  have h := (cutBytes_cover [95, 1, 462, 1] Source.page468).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap479327, gap479790] at h
  exact h⟩
def cell480256 : Cell := ⟨Source.page469.take 36, 36, by simp only [List.length_take, List.length_drop, Source.size469] <;> rfl⟩
theorem gap480292 : (Source.page469.drop 36).take 1 = [10] := by rfl
def cell480293 : Cell := ⟨(Source.page469.drop 37).take 313, 313, by simp only [List.length_take, List.length_drop, Source.size469] <;> rfl⟩
theorem gap480606 : (Source.page469.drop 350).take 1 = [10] := by rfl
def cell480607 : Cell := ⟨(Source.page469.drop 351).take 360, 360, by simp only [List.length_take, List.length_drop, Source.size469] <;> rfl⟩
theorem gap480967 : (Source.page469.drop 711).take 1 = [10] := by rfl
def cell480968 : Cell := ⟨(Source.page469.drop 712), 312, by simp only [List.length_take, List.length_drop, Source.size469] <;> rfl⟩
def coveredPage469 : Page := ⟨Source.page469, [cell480256, lf, cell480293, lf, cell480607, lf, cell480968], by
  have h := (cutBytes_cover [36, 1, 313, 1, 360, 1] Source.page469).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap480292, gap480606, gap480967] at h
  exact h⟩
def cell481280 : Cell := ⟨Source.page470.take 175, 175, by simp only [List.length_take, List.length_drop, Source.size470] <;> rfl⟩
theorem gap481455 : (Source.page470.drop 175).take 1 = [10] := by rfl
def cell481456 : Cell := ⟨(Source.page470.drop 176).take 372, 372, by simp only [List.length_take, List.length_drop, Source.size470] <;> rfl⟩
theorem gap481828 : (Source.page470.drop 548).take 1 = [10] := by rfl
def cell481829 : Cell := ⟨(Source.page470.drop 549).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size470] <;> rfl⟩
theorem gap482255 : (Source.page470.drop 975).take 1 = [10] := by rfl
def cell482256 : Cell := ⟨(Source.page470.drop 976), 48, by simp only [List.length_take, List.length_drop, Source.size470] <;> rfl⟩
def coveredPage470 : Page := ⟨Source.page470, [cell481280, lf, cell481456, lf, cell481829, lf, cell482256], by
  have h := (cutBytes_cover [175, 1, 372, 1, 426, 1] Source.page470).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap481455, gap481828, gap482255] at h
  exact h⟩
def cell482304 : Cell := ⟨Source.page471.take 441, 441, by simp only [List.length_take, List.length_drop, Source.size471] <;> rfl⟩
theorem gap482745 : (Source.page471.drop 441).take 1 = [10] := by rfl
def cell482746 : Cell := ⟨(Source.page471.drop 442).take 546, 546, by simp only [List.length_take, List.length_drop, Source.size471] <;> rfl⟩
theorem gap483292 : (Source.page471.drop 988).take 1 = [10] := by rfl
def cell483293 : Cell := ⟨(Source.page471.drop 989), 35, by simp only [List.length_take, List.length_drop, Source.size471] <;> rfl⟩
def coveredPage471 : Page := ⟨Source.page471, [cell482304, lf, cell482746, lf, cell483293], by
  have h := (cutBytes_cover [441, 1, 546, 1] Source.page471).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap482745, gap483292] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
