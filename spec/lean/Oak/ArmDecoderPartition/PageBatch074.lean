import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch037

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell606208 : Cell := ⟨Source.page592.take 74, 74, by simp only [List.length_take, List.length_drop, Source.size592] <;> rfl⟩
theorem gap606282 : (Source.page592.drop 74).take 1 = [10] := by rfl
def cell606283 : Cell := ⟨(Source.page592.drop 75).take 564, 564, by simp only [List.length_take, List.length_drop, Source.size592] <;> rfl⟩
theorem gap606847 : (Source.page592.drop 639).take 1 = [10] := by rfl
def cell606848 : Cell := ⟨(Source.page592.drop 640), 384, by simp only [List.length_take, List.length_drop, Source.size592] <;> rfl⟩
def coveredPage592 : Page := ⟨Source.page592, [cell606208, lf, cell606283, lf, cell606848], by
  have h := (cutBytes_cover [74, 1, 564, 1] Source.page592).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap606282, gap606847] at h
  exact h⟩
def cell607232 : Cell := ⟨Source.page593.take 217, 217, by simp only [List.length_take, List.length_drop, Source.size593] <;> rfl⟩
theorem gap607449 : (Source.page593.drop 217).take 1 = [10] := by rfl
def cell607450 : Cell := ⟨(Source.page593.drop 218).take 500, 500, by simp only [List.length_take, List.length_drop, Source.size593] <;> rfl⟩
theorem gap607950 : (Source.page593.drop 718).take 1 = [10] := by rfl
def cell607951 : Cell := ⟨(Source.page593.drop 719), 305, by simp only [List.length_take, List.length_drop, Source.size593] <;> rfl⟩
def coveredPage593 : Page := ⟨Source.page593, [cell607232, lf, cell607450, lf, cell607951], by
  have h := (cutBytes_cover [217, 1, 500, 1] Source.page593).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap607449, gap607950] at h
  exact h⟩
def cell608256 : Cell := ⟨Source.page594.take 241, 241, by simp only [List.length_take, List.length_drop, Source.size594] <;> rfl⟩
theorem gap608497 : (Source.page594.drop 241).take 1 = [10] := by rfl
def cell608498 : Cell := ⟨(Source.page594.drop 242).take 532, 532, by simp only [List.length_take, List.length_drop, Source.size594] <;> rfl⟩
theorem gap609030 : (Source.page594.drop 774).take 1 = [10] := by rfl
def cell609031 : Cell := ⟨(Source.page594.drop 775), 249, by simp only [List.length_take, List.length_drop, Source.size594] <;> rfl⟩
def coveredPage594 : Page := ⟨Source.page594, [cell608256, lf, cell608498, lf, cell609031], by
  have h := (cutBytes_cover [241, 1, 532, 1] Source.page594).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap608497, gap609030] at h
  exact h⟩
def cell609280 : Cell := ⟨Source.page595.take 142, 142, by simp only [List.length_take, List.length_drop, Source.size595] <;> rfl⟩
theorem gap609422 : (Source.page595.drop 142).take 1 = [10] := by rfl
def cell609423 : Cell := ⟨(Source.page595.drop 143).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size595] <;> rfl⟩
theorem gap609849 : (Source.page595.drop 569).take 1 = [10] := by rfl
def cell609850 : Cell := ⟨(Source.page595.drop 570), 454, by simp only [List.length_take, List.length_drop, Source.size595] <;> rfl⟩
def coveredPage595 : Page := ⟨Source.page595, [cell609280, lf, cell609423, lf, cell609850], by
  have h := (cutBytes_cover [142, 1, 426, 1] Source.page595).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap609422, gap609849] at h
  exact h⟩
def cell610304 : Cell := ⟨Source.page596.take 104, 104, by simp only [List.length_take, List.length_drop, Source.size596] <;> rfl⟩
theorem gap610408 : (Source.page596.drop 104).take 1 = [10] := by rfl
def cell610409 : Cell := ⟨(Source.page596.drop 105).take 455, 455, by simp only [List.length_take, List.length_drop, Source.size596] <;> rfl⟩
theorem gap610864 : (Source.page596.drop 560).take 1 = [10] := by rfl
def cell610865 : Cell := ⟨(Source.page596.drop 561).take 408, 408, by simp only [List.length_take, List.length_drop, Source.size596] <;> rfl⟩
theorem gap611273 : (Source.page596.drop 969).take 1 = [10] := by rfl
def cell611274 : Cell := ⟨(Source.page596.drop 970), 54, by simp only [List.length_take, List.length_drop, Source.size596] <;> rfl⟩
def coveredPage596 : Page := ⟨Source.page596, [cell610304, lf, cell610409, lf, cell610865, lf, cell611274], by
  have h := (cutBytes_cover [104, 1, 455, 1, 408, 1] Source.page596).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap610408, gap610864, gap611273] at h
  exact h⟩
def cell611328 : Cell := ⟨Source.page597.take 521, 521, by simp only [List.length_take, List.length_drop, Source.size597] <;> rfl⟩
theorem gap611849 : (Source.page597.drop 521).take 1 = [10] := by rfl
def cell611850 : Cell := ⟨(Source.page597.drop 522).take 498, 498, by simp only [List.length_take, List.length_drop, Source.size597] <;> rfl⟩
theorem gap612348 : (Source.page597.drop 1020).take 1 = [10] := by rfl
def cell612349 : Cell := ⟨(Source.page597.drop 1021), 3, by simp only [List.length_take, List.length_drop, Source.size597] <;> rfl⟩
def coveredPage597 : Page := ⟨Source.page597, [cell611328, lf, cell611850, lf, cell612349], by
  have h := (cutBytes_cover [521, 1, 498, 1] Source.page597).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap611849, gap612348] at h
  exact h⟩
def cell612352 : Cell := ⟨Source.page598.take 609, 609, by simp only [List.length_take, List.length_drop, Source.size598] <;> rfl⟩
theorem gap612961 : (Source.page598.drop 609).take 1 = [10] := by rfl
def cell612962 : Cell := ⟨(Source.page598.drop 610), 414, by simp only [List.length_take, List.length_drop, Source.size598] <;> rfl⟩
def coveredPage598 : Page := ⟨Source.page598, [cell612352, lf, cell612962], by
  have h := (cutBytes_cover [609, 1] Source.page598).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap612961] at h
  exact h⟩
def cell613376 : Cell := ⟨Source.page599.take 103, 103, by simp only [List.length_take, List.length_drop, Source.size599] <;> rfl⟩
theorem gap613479 : (Source.page599.drop 103).take 1 = [10] := by rfl
def cell613480 : Cell := ⟨(Source.page599.drop 104).take 497, 497, by simp only [List.length_take, List.length_drop, Source.size599] <;> rfl⟩
theorem gap613977 : (Source.page599.drop 601).take 1 = [10] := by rfl
def cell613978 : Cell := ⟨(Source.page599.drop 602), 422, by simp only [List.length_take, List.length_drop, Source.size599] <;> rfl⟩
def coveredPage599 : Page := ⟨Source.page599, [cell613376, lf, cell613480, lf, cell613978], by
  have h := (cutBytes_cover [103, 1, 497, 1] Source.page599).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap613479, gap613977] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
