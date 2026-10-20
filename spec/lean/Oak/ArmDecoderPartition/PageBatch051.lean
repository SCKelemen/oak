import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch025

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell417792 : Cell := ⟨Source.page408.take 288, 288, by simp only [List.length_take, List.length_drop, Source.size408] <;> rfl⟩
theorem gap418080 : (Source.page408.drop 288).take 1 = [10] := by rfl
def cell418081 : Cell := ⟨(Source.page408.drop 289).take 457, 457, by simp only [List.length_take, List.length_drop, Source.size408] <;> rfl⟩
theorem gap418538 : (Source.page408.drop 746).take 1 = [10] := by rfl
def cell418539 : Cell := ⟨(Source.page408.drop 747), 277, by simp only [List.length_take, List.length_drop, Source.size408] <;> rfl⟩
def coveredPage408 : Page := ⟨Source.page408, [cell417792, lf, cell418081, lf, cell418539], by
  have h := (cutBytes_cover [288, 1, 457, 1] Source.page408).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap418080, gap418538] at h
  exact h⟩
def cell418816 : Cell := ⟨Source.page409.take 236, 236, by simp only [List.length_take, List.length_drop, Source.size409] <;> rfl⟩
theorem gap419052 : (Source.page409.drop 236).take 1 = [10] := by rfl
def cell419053 : Cell := ⟨(Source.page409.drop 237).take 398, 398, by simp only [List.length_take, List.length_drop, Source.size409] <;> rfl⟩
theorem gap419451 : (Source.page409.drop 635).take 1 = [10] := by rfl
def cell419452 : Cell := ⟨(Source.page409.drop 636), 388, by simp only [List.length_take, List.length_drop, Source.size409] <;> rfl⟩
def coveredPage409 : Page := ⟨Source.page409, [cell418816, lf, cell419053, lf, cell419452], by
  have h := (cutBytes_cover [236, 1, 398, 1] Source.page409).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap419052, gap419451] at h
  exact h⟩
def cell419840 : Cell := ⟨Source.page410.take 45, 45, by simp only [List.length_take, List.length_drop, Source.size410] <;> rfl⟩
theorem gap419885 : (Source.page410.drop 45).take 1 = [10] := by rfl
def cell419886 : Cell := ⟨(Source.page410.drop 46).take 546, 546, by simp only [List.length_take, List.length_drop, Source.size410] <;> rfl⟩
theorem gap420432 : (Source.page410.drop 592).take 1 = [10] := by rfl
def cell420433 : Cell := ⟨(Source.page410.drop 593), 431, by simp only [List.length_take, List.length_drop, Source.size410] <;> rfl⟩
def coveredPage410 : Page := ⟨Source.page410, [cell419840, lf, cell419886, lf, cell420433], by
  have h := (cutBytes_cover [45, 1, 546, 1] Source.page410).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap419885, gap420432] at h
  exact h⟩
def cell420864 : Cell := ⟨Source.page411.take 20, 20, by simp only [List.length_take, List.length_drop, Source.size411] <;> rfl⟩
theorem gap420884 : (Source.page411.drop 20).take 1 = [10] := by rfl
def cell420885 : Cell := ⟨(Source.page411.drop 21).take 494, 494, by simp only [List.length_take, List.length_drop, Source.size411] <;> rfl⟩
theorem gap421379 : (Source.page411.drop 515).take 1 = [10] := by rfl
def cell421380 : Cell := ⟨(Source.page411.drop 516).take 441, 441, by simp only [List.length_take, List.length_drop, Source.size411] <;> rfl⟩
theorem gap421821 : (Source.page411.drop 957).take 1 = [10] := by rfl
def cell421822 : Cell := ⟨(Source.page411.drop 958), 66, by simp only [List.length_take, List.length_drop, Source.size411] <;> rfl⟩
def coveredPage411 : Page := ⟨Source.page411, [cell420864, lf, cell420885, lf, cell421380, lf, cell421822], by
  have h := (cutBytes_cover [20, 1, 494, 1, 441, 1] Source.page411).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap420884, gap421379, gap421821] at h
  exact h⟩
def cell421888 : Cell := ⟨Source.page412.take 450, 450, by simp only [List.length_take, List.length_drop, Source.size412] <;> rfl⟩
theorem gap422338 : (Source.page412.drop 450).take 1 = [10] := by rfl
def cell422339 : Cell := ⟨(Source.page412.drop 451).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size412] <;> rfl⟩
theorem gap422765 : (Source.page412.drop 877).take 1 = [10] := by rfl
def cell422766 : Cell := ⟨(Source.page412.drop 878), 146, by simp only [List.length_take, List.length_drop, Source.size412] <;> rfl⟩
def coveredPage412 : Page := ⟨Source.page412, [cell421888, lf, cell422339, lf, cell422766], by
  have h := (cutBytes_cover [450, 1, 426, 1] Source.page412).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap422338, gap422765] at h
  exact h⟩
def cell422912 : Cell := ⟨Source.page413.take 321, 321, by simp only [List.length_take, List.length_drop, Source.size413] <;> rfl⟩
theorem gap423233 : (Source.page413.drop 321).take 1 = [10] := by rfl
def cell423234 : Cell := ⟨(Source.page413.drop 322).take 556, 556, by simp only [List.length_take, List.length_drop, Source.size413] <;> rfl⟩
theorem gap423790 : (Source.page413.drop 878).take 1 = [10] := by rfl
def cell423791 : Cell := ⟨(Source.page413.drop 879), 145, by simp only [List.length_take, List.length_drop, Source.size413] <;> rfl⟩
def coveredPage413 : Page := ⟨Source.page413, [cell422912, lf, cell423234, lf, cell423791], by
  have h := (cutBytes_cover [321, 1, 556, 1] Source.page413).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap423233, gap423790] at h
  exact h⟩
def cell423936 : Cell := ⟨Source.page414.take 339, 339, by simp only [List.length_take, List.length_drop, Source.size414] <;> rfl⟩
theorem gap424275 : (Source.page414.drop 339).take 1 = [10] := by rfl
def cell424276 : Cell := ⟨(Source.page414.drop 340).take 522, 522, by simp only [List.length_take, List.length_drop, Source.size414] <;> rfl⟩
theorem gap424798 : (Source.page414.drop 862).take 1 = [10] := by rfl
def cell424799 : Cell := ⟨(Source.page414.drop 863), 161, by simp only [List.length_take, List.length_drop, Source.size414] <;> rfl⟩
def coveredPage414 : Page := ⟨Source.page414, [cell423936, lf, cell424276, lf, cell424799], by
  have h := (cutBytes_cover [339, 1, 522, 1] Source.page414).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap424275, gap424798] at h
  exact h⟩
def cell424960 : Cell := ⟨Source.page415.take 403, 403, by simp only [List.length_take, List.length_drop, Source.size415] <;> rfl⟩
theorem gap425363 : (Source.page415.drop 403).take 1 = [10] := by rfl
def cell425364 : Cell := ⟨(Source.page415.drop 404).take 536, 536, by simp only [List.length_take, List.length_drop, Source.size415] <;> rfl⟩
theorem gap425900 : (Source.page415.drop 940).take 1 = [10] := by rfl
def cell425901 : Cell := ⟨(Source.page415.drop 941), 83, by simp only [List.length_take, List.length_drop, Source.size415] <;> rfl⟩
def coveredPage415 : Page := ⟨Source.page415, [cell424960, lf, cell425364, lf, cell425901], by
  have h := (cutBytes_cover [403, 1, 536, 1] Source.page415).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap425363, gap425900] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
