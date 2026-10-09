import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch035

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell581632 : Cell := ⟨Source.page568.take 216, 216, by simp only [List.length_take, List.length_drop, Source.size568] <;> rfl⟩
theorem gap581848 : (Source.page568.drop 216).take 1 = [10] := by rfl
def cell581849 : Cell := ⟨(Source.page568.drop 217).take 435, 435, by simp only [List.length_take, List.length_drop, Source.size568] <;> rfl⟩
theorem gap582284 : (Source.page568.drop 652).take 1 = [10] := by rfl
def cell582285 : Cell := ⟨(Source.page568.drop 653), 371, by simp only [List.length_take, List.length_drop, Source.size568] <;> rfl⟩
def coveredPage568 : Page := ⟨Source.page568, [cell581632, lf, cell581849, lf, cell582285], by
  have h := (cutBytes_cover [216, 1, 435, 1] Source.page568).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap581848, gap582284] at h
  exact h⟩
def cell582656 : Cell := ⟨Source.page569.take 130, 130, by simp only [List.length_take, List.length_drop, Source.size569] <;> rfl⟩
theorem gap582786 : (Source.page569.drop 130).take 1 = [10] := by rfl
def cell582787 : Cell := ⟨(Source.page569.drop 131).take 458, 458, by simp only [List.length_take, List.length_drop, Source.size569] <;> rfl⟩
theorem gap583245 : (Source.page569.drop 589).take 1 = [10] := by rfl
def cell583246 : Cell := ⟨(Source.page569.drop 590), 434, by simp only [List.length_take, List.length_drop, Source.size569] <;> rfl⟩
def coveredPage569 : Page := ⟨Source.page569, [cell582656, lf, cell582787, lf, cell583246], by
  have h := (cutBytes_cover [130, 1, 458, 1] Source.page569).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap582786, gap583245] at h
  exact h⟩
def cell583680 : Cell := ⟨Source.page570.take 70, 70, by simp only [List.length_take, List.length_drop, Source.size570] <;> rfl⟩
theorem gap583750 : (Source.page570.drop 70).take 1 = [10] := by rfl
def cell583751 : Cell := ⟨(Source.page570.drop 71).take 434, 434, by simp only [List.length_take, List.length_drop, Source.size570] <;> rfl⟩
theorem gap584185 : (Source.page570.drop 505).take 1 = [10] := by rfl
def cell584186 : Cell := ⟨(Source.page570.drop 506).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size570] <;> rfl⟩
theorem gap584687 : (Source.page570.drop 1007).take 1 = [10] := by rfl
def cell584688 : Cell := ⟨(Source.page570.drop 1008), 16, by simp only [List.length_take, List.length_drop, Source.size570] <;> rfl⟩
def coveredPage570 : Page := ⟨Source.page570, [cell583680, lf, cell583751, lf, cell584186, lf, cell584688], by
  have h := (cutBytes_cover [70, 1, 434, 1, 501, 1] Source.page570).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap583750, gap584185, gap584687] at h
  exact h⟩
def cell584704 : Cell := ⟨Source.page571.take 592, 592, by simp only [List.length_take, List.length_drop, Source.size571] <;> rfl⟩
theorem gap585296 : (Source.page571.drop 592).take 1 = [10] := by rfl
def cell585297 : Cell := ⟨(Source.page571.drop 593), 431, by simp only [List.length_take, List.length_drop, Source.size571] <;> rfl⟩
def coveredPage571 : Page := ⟨Source.page571, [cell584704, lf, cell585297], by
  have h := (cutBytes_cover [592, 1] Source.page571).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap585296] at h
  exact h⟩
def cell585728 : Cell := ⟨Source.page572.take 82, 82, by simp only [List.length_take, List.length_drop, Source.size572] <;> rfl⟩
theorem gap585810 : (Source.page572.drop 82).take 1 = [10] := by rfl
def cell585811 : Cell := ⟨(Source.page572.drop 83).take 484, 484, by simp only [List.length_take, List.length_drop, Source.size572] <;> rfl⟩
theorem gap586295 : (Source.page572.drop 567).take 1 = [10] := by rfl
def cell586296 : Cell := ⟨(Source.page572.drop 568), 456, by simp only [List.length_take, List.length_drop, Source.size572] <;> rfl⟩
def coveredPage572 : Page := ⟨Source.page572, [cell585728, lf, cell585811, lf, cell586296], by
  have h := (cutBytes_cover [82, 1, 484, 1] Source.page572).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap585810, gap586295] at h
  exact h⟩
def cell586752 : Cell := ⟨Source.page573.take 40, 40, by simp only [List.length_take, List.length_drop, Source.size573] <;> rfl⟩
theorem gap586792 : (Source.page573.drop 40).take 1 = [10] := by rfl
def cell586793 : Cell := ⟨(Source.page573.drop 41).take 516, 516, by simp only [List.length_take, List.length_drop, Source.size573] <;> rfl⟩
theorem gap587309 : (Source.page573.drop 557).take 1 = [10] := by rfl
def cell587310 : Cell := ⟨(Source.page573.drop 558).take 423, 423, by simp only [List.length_take, List.length_drop, Source.size573] <;> rfl⟩
theorem gap587733 : (Source.page573.drop 981).take 1 = [10] := by rfl
def cell587734 : Cell := ⟨(Source.page573.drop 982), 42, by simp only [List.length_take, List.length_drop, Source.size573] <;> rfl⟩
def coveredPage573 : Page := ⟨Source.page573, [cell586752, lf, cell586793, lf, cell587310, lf, cell587734], by
  have h := (cutBytes_cover [40, 1, 516, 1, 423, 1] Source.page573).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap586792, gap587309, gap587733] at h
  exact h⟩
def cell587776 : Cell := ⟨Source.page574.take 565, 565, by simp only [List.length_take, List.length_drop, Source.size574] <;> rfl⟩
theorem gap588341 : (Source.page574.drop 565).take 1 = [10] := by rfl
def cell588342 : Cell := ⟨(Source.page574.drop 566), 458, by simp only [List.length_take, List.length_drop, Source.size574] <;> rfl⟩
def coveredPage574 : Page := ⟨Source.page574, [cell587776, lf, cell588342], by
  have h := (cutBytes_cover [565, 1] Source.page574).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap588341] at h
  exact h⟩
def cell588800 : Cell := ⟨Source.page575.take 43, 43, by simp only [List.length_take, List.length_drop, Source.size575] <;> rfl⟩
theorem gap588843 : (Source.page575.drop 43).take 1 = [10] := by rfl
def cell588844 : Cell := ⟨(Source.page575.drop 44).take 420, 420, by simp only [List.length_take, List.length_drop, Source.size575] <;> rfl⟩
theorem gap589264 : (Source.page575.drop 464).take 1 = [10] := by rfl
def cell589265 : Cell := ⟨(Source.page575.drop 465).take 487, 487, by simp only [List.length_take, List.length_drop, Source.size575] <;> rfl⟩
theorem gap589752 : (Source.page575.drop 952).take 1 = [10] := by rfl
def cell589753 : Cell := ⟨(Source.page575.drop 953), 71, by simp only [List.length_take, List.length_drop, Source.size575] <;> rfl⟩
def coveredPage575 : Page := ⟨Source.page575, [cell588800, lf, cell588844, lf, cell589265, lf, cell589753], by
  have h := (cutBytes_cover [43, 1, 420, 1, 487, 1] Source.page575).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap588843, gap589264, gap589752] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
