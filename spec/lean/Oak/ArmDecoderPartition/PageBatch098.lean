import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch049

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell802816 : Cell := ⟨Source.page784.take 348, 348, by simp only [List.length_take, List.length_drop, Source.size784] <;> rfl⟩
theorem gap803164 : (Source.page784.drop 348).take 1 = [10] := by rfl
def cell803165 : Cell := ⟨(Source.page784.drop 349).take 483, 483, by simp only [List.length_take, List.length_drop, Source.size784] <;> rfl⟩
theorem gap803648 : (Source.page784.drop 832).take 1 = [10] := by rfl
def cell803649 : Cell := ⟨(Source.page784.drop 833), 191, by simp only [List.length_take, List.length_drop, Source.size784] <;> rfl⟩
def coveredPage784 : Page := ⟨Source.page784, [cell802816, lf, cell803165, lf, cell803649], by
  have h := (cutBytes_cover [348, 1, 483, 1] Source.page784).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap803164, gap803648] at h
  exact h⟩
def cell803840 : Cell := ⟨Source.page785.take 249, 249, by simp only [List.length_take, List.length_drop, Source.size785] <;> rfl⟩
theorem gap804089 : (Source.page785.drop 249).take 1 = [10] := by rfl
def cell804090 : Cell := ⟨(Source.page785.drop 250).take 465, 465, by simp only [List.length_take, List.length_drop, Source.size785] <;> rfl⟩
theorem gap804555 : (Source.page785.drop 715).take 1 = [10] := by rfl
def cell804556 : Cell := ⟨(Source.page785.drop 716), 308, by simp only [List.length_take, List.length_drop, Source.size785] <;> rfl⟩
def coveredPage785 : Page := ⟨Source.page785, [cell803840, lf, cell804090, lf, cell804556], by
  have h := (cutBytes_cover [249, 1, 465, 1] Source.page785).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap804089, gap804555] at h
  exact h⟩
def cell804864 : Cell := ⟨Source.page786.take 166, 166, by simp only [List.length_take, List.length_drop, Source.size786] <;> rfl⟩
theorem gap805030 : (Source.page786.drop 166).take 1 = [10] := by rfl
def cell805031 : Cell := ⟨(Source.page786.drop 167).take 447, 447, by simp only [List.length_take, List.length_drop, Source.size786] <;> rfl⟩
theorem gap805478 : (Source.page786.drop 614).take 1 = [10] := by rfl
def cell805479 : Cell := ⟨(Source.page786.drop 615), 409, by simp only [List.length_take, List.length_drop, Source.size786] <;> rfl⟩
def coveredPage786 : Page := ⟨Source.page786, [cell804864, lf, cell805031, lf, cell805479], by
  have h := (cutBytes_cover [166, 1, 447, 1] Source.page786).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap805030, gap805478] at h
  exact h⟩
def cell805888 : Cell := ⟨Source.page787.take 44, 44, by simp only [List.length_take, List.length_drop, Source.size787] <;> rfl⟩
theorem gap805932 : (Source.page787.drop 44).take 1 = [10] := by rfl
def cell805933 : Cell := ⟨(Source.page787.drop 45).take 614, 614, by simp only [List.length_take, List.length_drop, Source.size787] <;> rfl⟩
theorem gap806547 : (Source.page787.drop 659).take 1 = [10] := by rfl
def cell806548 : Cell := ⟨(Source.page787.drop 660), 364, by simp only [List.length_take, List.length_drop, Source.size787] <;> rfl⟩
def coveredPage787 : Page := ⟨Source.page787, [cell805888, lf, cell805933, lf, cell806548], by
  have h := (cutBytes_cover [44, 1, 614, 1] Source.page787).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap805932, gap806547] at h
  exact h⟩
def cell806912 : Cell := ⟨Source.page788.take 119, 119, by simp only [List.length_take, List.length_drop, Source.size788] <;> rfl⟩
theorem gap807031 : (Source.page788.drop 119).take 1 = [10] := by rfl
def cell807032 : Cell := ⟨(Source.page788.drop 120).take 522, 522, by simp only [List.length_take, List.length_drop, Source.size788] <;> rfl⟩
theorem gap807554 : (Source.page788.drop 642).take 1 = [10] := by rfl
def cell807555 : Cell := ⟨(Source.page788.drop 643).take 330, 330, by simp only [List.length_take, List.length_drop, Source.size788] <;> rfl⟩
theorem gap807885 : (Source.page788.drop 973).take 1 = [10] := by rfl
def cell807886 : Cell := ⟨(Source.page788.drop 974), 50, by simp only [List.length_take, List.length_drop, Source.size788] <;> rfl⟩
def coveredPage788 : Page := ⟨Source.page788, [cell806912, lf, cell807032, lf, cell807555, lf, cell807886], by
  have h := (cutBytes_cover [119, 1, 522, 1, 330, 1] Source.page788).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap807031, gap807554, gap807885] at h
  exact h⟩
def cell807936 : Cell := ⟨Source.page789.take 464, 464, by simp only [List.length_take, List.length_drop, Source.size789] <;> rfl⟩
theorem gap808400 : (Source.page789.drop 464).take 1 = [10] := by rfl
def cell808401 : Cell := ⟨(Source.page789.drop 465).take 376, 376, by simp only [List.length_take, List.length_drop, Source.size789] <;> rfl⟩
theorem gap808777 : (Source.page789.drop 841).take 1 = [10] := by rfl
def cell808778 : Cell := ⟨(Source.page789.drop 842), 182, by simp only [List.length_take, List.length_drop, Source.size789] <;> rfl⟩
def coveredPage789 : Page := ⟨Source.page789, [cell807936, lf, cell808401, lf, cell808778], by
  have h := (cutBytes_cover [464, 1, 376, 1] Source.page789).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap808400, gap808777] at h
  exact h⟩
def cell808960 : Cell := ⟨Source.page790.take 354, 354, by simp only [List.length_take, List.length_drop, Source.size790] <;> rfl⟩
theorem gap809314 : (Source.page790.drop 354).take 1 = [10] := by rfl
def cell809315 : Cell := ⟨(Source.page790.drop 355).take 536, 536, by simp only [List.length_take, List.length_drop, Source.size790] <;> rfl⟩
theorem gap809851 : (Source.page790.drop 891).take 1 = [10] := by rfl
def cell809852 : Cell := ⟨(Source.page790.drop 892), 132, by simp only [List.length_take, List.length_drop, Source.size790] <;> rfl⟩
def coveredPage790 : Page := ⟨Source.page790, [cell808960, lf, cell809315, lf, cell809852], by
  have h := (cutBytes_cover [354, 1, 536, 1] Source.page790).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap809314, gap809851] at h
  exact h⟩
def cell809984 : Cell := ⟨Source.page791.take 412, 412, by simp only [List.length_take, List.length_drop, Source.size791] <;> rfl⟩
theorem gap810396 : (Source.page791.drop 412).take 1 = [10] := by rfl
def cell810397 : Cell := ⟨(Source.page791.drop 413).take 532, 532, by simp only [List.length_take, List.length_drop, Source.size791] <;> rfl⟩
theorem gap810929 : (Source.page791.drop 945).take 1 = [10] := by rfl
def cell810930 : Cell := ⟨(Source.page791.drop 946), 78, by simp only [List.length_take, List.length_drop, Source.size791] <;> rfl⟩
def coveredPage791 : Page := ⟨Source.page791, [cell809984, lf, cell810397, lf, cell810930], by
  have h := (cutBytes_cover [412, 1, 532, 1] Source.page791).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap810396, gap810929] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
