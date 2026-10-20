import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch034

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell557056 : Cell := ⟨Source.page544.take 83, 83, by simp only [List.length_take, List.length_drop, Source.size544] <;> rfl⟩
theorem gap557139 : (Source.page544.drop 83).take 1 = [10] := by rfl
def cell557140 : Cell := ⟨(Source.page544.drop 84).take 407, 407, by simp only [List.length_take, List.length_drop, Source.size544] <;> rfl⟩
theorem gap557547 : (Source.page544.drop 491).take 1 = [10] := by rfl
def cell557548 : Cell := ⟨(Source.page544.drop 492).take 474, 474, by simp only [List.length_take, List.length_drop, Source.size544] <;> rfl⟩
theorem gap558022 : (Source.page544.drop 966).take 1 = [10] := by rfl
def cell558023 : Cell := ⟨(Source.page544.drop 967), 57, by simp only [List.length_take, List.length_drop, Source.size544] <;> rfl⟩
def coveredPage544 : Page := ⟨Source.page544, [cell557056, lf, cell557140, lf, cell557548, lf, cell558023], by
  have h := (cutBytes_cover [83, 1, 407, 1, 474, 1] Source.page544).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap557139, gap557547, gap558022] at h
  exact h⟩
def cell558080 : Cell := ⟨Source.page545.take 489, 489, by simp only [List.length_take, List.length_drop, Source.size545] <;> rfl⟩
theorem gap558569 : (Source.page545.drop 489).take 1 = [10] := by rfl
def cell558570 : Cell := ⟨(Source.page545.drop 490).take 472, 472, by simp only [List.length_take, List.length_drop, Source.size545] <;> rfl⟩
theorem gap559042 : (Source.page545.drop 962).take 1 = [10] := by rfl
def cell559043 : Cell := ⟨(Source.page545.drop 963), 61, by simp only [List.length_take, List.length_drop, Source.size545] <;> rfl⟩
def coveredPage545 : Page := ⟨Source.page545, [cell558080, lf, cell558570, lf, cell559043], by
  have h := (cutBytes_cover [489, 1, 472, 1] Source.page545).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap558569, gap559042] at h
  exact h⟩
def cell559104 : Cell := ⟨Source.page546.take 347, 347, by simp only [List.length_take, List.length_drop, Source.size546] <;> rfl⟩
theorem gap559451 : (Source.page546.drop 347).take 1 = [10] := by rfl
def cell559452 : Cell := ⟨(Source.page546.drop 348).take 478, 478, by simp only [List.length_take, List.length_drop, Source.size546] <;> rfl⟩
theorem gap559930 : (Source.page546.drop 826).take 1 = [10] := by rfl
def cell559931 : Cell := ⟨(Source.page546.drop 827), 197, by simp only [List.length_take, List.length_drop, Source.size546] <;> rfl⟩
def coveredPage546 : Page := ⟨Source.page546, [cell559104, lf, cell559452, lf, cell559931], by
  have h := (cutBytes_cover [347, 1, 478, 1] Source.page546).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap559451, gap559930] at h
  exact h⟩
def cell560128 : Cell := ⟨Source.page547.take 229, 229, by simp only [List.length_take, List.length_drop, Source.size547] <;> rfl⟩
theorem gap560357 : (Source.page547.drop 229).take 1 = [10] := by rfl
def cell560358 : Cell := ⟨(Source.page547.drop 230).take 457, 457, by simp only [List.length_take, List.length_drop, Source.size547] <;> rfl⟩
theorem gap560815 : (Source.page547.drop 687).take 1 = [10] := by rfl
def cell560816 : Cell := ⟨(Source.page547.drop 688), 336, by simp only [List.length_take, List.length_drop, Source.size547] <;> rfl⟩
def coveredPage547 : Page := ⟨Source.page547, [cell560128, lf, cell560358, lf, cell560816], by
  have h := (cutBytes_cover [229, 1, 457, 1] Source.page547).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap560357, gap560815] at h
  exact h⟩
def cell561152 : Cell := ⟨Source.page548.take 200, 200, by simp only [List.length_take, List.length_drop, Source.size548] <;> rfl⟩
theorem gap561352 : (Source.page548.drop 200).take 1 = [10] := by rfl
def cell561353 : Cell := ⟨(Source.page548.drop 201).take 201, 201, by simp only [List.length_take, List.length_drop, Source.size548] <;> rfl⟩
theorem gap561554 : (Source.page548.drop 402).take 1 = [10] := by rfl
def cell561555 : Cell := ⟨(Source.page548.drop 403).take 423, 423, by simp only [List.length_take, List.length_drop, Source.size548] <;> rfl⟩
theorem gap561978 : (Source.page548.drop 826).take 1 = [10] := by rfl
def cell561979 : Cell := ⟨(Source.page548.drop 827), 197, by simp only [List.length_take, List.length_drop, Source.size548] <;> rfl⟩
def coveredPage548 : Page := ⟨Source.page548, [cell561152, lf, cell561353, lf, cell561555, lf, cell561979], by
  have h := (cutBytes_cover [200, 1, 201, 1, 423, 1] Source.page548).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap561352, gap561554, gap561978] at h
  exact h⟩
def cell562176 : Cell := ⟨Source.page549.take 268, 268, by simp only [List.length_take, List.length_drop, Source.size549] <;> rfl⟩
theorem gap562444 : (Source.page549.drop 268).take 1 = [10] := by rfl
def cell562445 : Cell := ⟨(Source.page549.drop 269).take 519, 519, by simp only [List.length_take, List.length_drop, Source.size549] <;> rfl⟩
theorem gap562964 : (Source.page549.drop 788).take 1 = [10] := by rfl
def cell562965 : Cell := ⟨(Source.page549.drop 789), 235, by simp only [List.length_take, List.length_drop, Source.size549] <;> rfl⟩
def coveredPage549 : Page := ⟨Source.page549, [cell562176, lf, cell562445, lf, cell562965], by
  have h := (cutBytes_cover [268, 1, 519, 1] Source.page549).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap562444, gap562964] at h
  exact h⟩
def cell563200 : Cell := ⟨Source.page550.take 323, 323, by simp only [List.length_take, List.length_drop, Source.size550] <;> rfl⟩
theorem gap563523 : (Source.page550.drop 323).take 1 = [10] := by rfl
def cell563524 : Cell := ⟨(Source.page550.drop 324).take 572, 572, by simp only [List.length_take, List.length_drop, Source.size550] <;> rfl⟩
theorem gap564096 : (Source.page550.drop 896).take 1 = [10] := by rfl
def cell564097 : Cell := ⟨(Source.page550.drop 897), 127, by simp only [List.length_take, List.length_drop, Source.size550] <;> rfl⟩
def coveredPage550 : Page := ⟨Source.page550, [cell563200, lf, cell563524, lf, cell564097], by
  have h := (cutBytes_cover [323, 1, 572, 1] Source.page550).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap563523, gap564096] at h
  exact h⟩
def cell564224 : Cell := ⟨Source.page551.take 293, 293, by simp only [List.length_take, List.length_drop, Source.size551] <;> rfl⟩
theorem gap564517 : (Source.page551.drop 293).take 1 = [10] := by rfl
def cell564518 : Cell := ⟨(Source.page551.drop 294).take 462, 462, by simp only [List.length_take, List.length_drop, Source.size551] <;> rfl⟩
theorem gap564980 : (Source.page551.drop 756).take 1 = [10] := by rfl
def cell564981 : Cell := ⟨(Source.page551.drop 757), 267, by simp only [List.length_take, List.length_drop, Source.size551] <;> rfl⟩
def coveredPage551 : Page := ⟨Source.page551, [cell564224, lf, cell564518, lf, cell564981], by
  have h := (cutBytes_cover [293, 1, 462, 1] Source.page551).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap564517, gap564980] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
