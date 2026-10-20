import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch042

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell696320 : Cell := ⟨Source.page680.take 333, 333, by simp only [List.length_take, List.length_drop, Source.size680] <;> rfl⟩
theorem gap696653 : (Source.page680.drop 333).take 1 = [10] := by rfl
def cell696654 : Cell := ⟨(Source.page680.drop 334).take 605, 605, by simp only [List.length_take, List.length_drop, Source.size680] <;> rfl⟩
theorem gap697259 : (Source.page680.drop 939).take 1 = [10] := by rfl
def cell697260 : Cell := ⟨(Source.page680.drop 940), 84, by simp only [List.length_take, List.length_drop, Source.size680] <;> rfl⟩
def coveredPage680 : Page := ⟨Source.page680, [cell696320, lf, cell696654, lf, cell697260], by
  have h := (cutBytes_cover [333, 1, 605, 1] Source.page680).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap696653, gap697259] at h
  exact h⟩
def cell697344 : Cell := ⟨Source.page681.take 378, 378, by simp only [List.length_take, List.length_drop, Source.size681] <;> rfl⟩
theorem gap697722 : (Source.page681.drop 378).take 1 = [10] := by rfl
def cell697723 : Cell := ⟨(Source.page681.drop 379).take 451, 451, by simp only [List.length_take, List.length_drop, Source.size681] <;> rfl⟩
theorem gap698174 : (Source.page681.drop 830).take 1 = [10] := by rfl
def cell698175 : Cell := ⟨(Source.page681.drop 831), 193, by simp only [List.length_take, List.length_drop, Source.size681] <;> rfl⟩
def coveredPage681 : Page := ⟨Source.page681, [cell697344, lf, cell697723, lf, cell698175], by
  have h := (cutBytes_cover [378, 1, 451, 1] Source.page681).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap697722, gap698174] at h
  exact h⟩
def cell698368 : Cell := ⟨Source.page682.take 136, 136, by simp only [List.length_take, List.length_drop, Source.size682] <;> rfl⟩
theorem gap698504 : (Source.page682.drop 136).take 1 = [10] := by rfl
def cell698505 : Cell := ⟨(Source.page682.drop 137).take 428, 428, by simp only [List.length_take, List.length_drop, Source.size682] <;> rfl⟩
theorem gap698933 : (Source.page682.drop 565).take 1 = [10] := by rfl
def cell698934 : Cell := ⟨(Source.page682.drop 566), 458, by simp only [List.length_take, List.length_drop, Source.size682] <;> rfl⟩
def coveredPage682 : Page := ⟨Source.page682, [cell698368, lf, cell698505, lf, cell698934], by
  have h := (cutBytes_cover [136, 1, 428, 1] Source.page682).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap698504, gap698933] at h
  exact h⟩
def cell699392 : Cell := ⟨Source.page683.take 22, 22, by simp only [List.length_take, List.length_drop, Source.size683] <;> rfl⟩
theorem gap699414 : (Source.page683.drop 22).take 1 = [10] := by rfl
def cell699415 : Cell := ⟨(Source.page683.drop 23).take 443, 443, by simp only [List.length_take, List.length_drop, Source.size683] <;> rfl⟩
theorem gap699858 : (Source.page683.drop 466).take 1 = [10] := by rfl
def cell699859 : Cell := ⟨(Source.page683.drop 467).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size683] <;> rfl⟩
theorem gap700339 : (Source.page683.drop 947).take 1 = [10] := by rfl
def cell700340 : Cell := ⟨(Source.page683.drop 948), 76, by simp only [List.length_take, List.length_drop, Source.size683] <;> rfl⟩
def coveredPage683 : Page := ⟨Source.page683, [cell699392, lf, cell699415, lf, cell699859, lf, cell700340], by
  have h := (cutBytes_cover [22, 1, 443, 1, 480, 1] Source.page683).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap699414, gap699858, gap700339] at h
  exact h⟩
def cell700416 : Cell := ⟨Source.page684.take 435, 435, by simp only [List.length_take, List.length_drop, Source.size684] <;> rfl⟩
theorem gap700851 : (Source.page684.drop 435).take 1 = [10] := by rfl
def cell700852 : Cell := ⟨(Source.page684.drop 436).take 554, 554, by simp only [List.length_take, List.length_drop, Source.size684] <;> rfl⟩
theorem gap701406 : (Source.page684.drop 990).take 1 = [10] := by rfl
def cell701407 : Cell := ⟨(Source.page684.drop 991), 33, by simp only [List.length_take, List.length_drop, Source.size684] <;> rfl⟩
def coveredPage684 : Page := ⟨Source.page684, [cell700416, lf, cell700852, lf, cell701407], by
  have h := (cutBytes_cover [435, 1, 554, 1] Source.page684).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap700851, gap701406] at h
  exact h⟩
def cell701440 : Cell := ⟨Source.page685.take 429, 429, by simp only [List.length_take, List.length_drop, Source.size685] <;> rfl⟩
theorem gap701869 : (Source.page685.drop 429).take 1 = [10] := by rfl
def cell701870 : Cell := ⟨(Source.page685.drop 430).take 477, 477, by simp only [List.length_take, List.length_drop, Source.size685] <;> rfl⟩
theorem gap702347 : (Source.page685.drop 907).take 1 = [10] := by rfl
def cell702348 : Cell := ⟨(Source.page685.drop 908), 116, by simp only [List.length_take, List.length_drop, Source.size685] <;> rfl⟩
def coveredPage685 : Page := ⟨Source.page685, [cell701440, lf, cell701870, lf, cell702348], by
  have h := (cutBytes_cover [429, 1, 477, 1] Source.page685).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap701869, gap702347] at h
  exact h⟩
def cell702464 : Cell := ⟨Source.page686.take 387, 387, by simp only [List.length_take, List.length_drop, Source.size686] <;> rfl⟩
theorem gap702851 : (Source.page686.drop 387).take 1 = [10] := by rfl
def cell702852 : Cell := ⟨(Source.page686.drop 388).take 503, 503, by simp only [List.length_take, List.length_drop, Source.size686] <;> rfl⟩
theorem gap703355 : (Source.page686.drop 891).take 1 = [10] := by rfl
def cell703356 : Cell := ⟨(Source.page686.drop 892), 132, by simp only [List.length_take, List.length_drop, Source.size686] <;> rfl⟩
def coveredPage686 : Page := ⟨Source.page686, [cell702464, lf, cell702852, lf, cell703356], by
  have h := (cutBytes_cover [387, 1, 503, 1] Source.page686).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap702851, gap703355] at h
  exact h⟩
def cell703488 : Cell := ⟨Source.page687.take 330, 330, by simp only [List.length_take, List.length_drop, Source.size687] <;> rfl⟩
theorem gap703818 : (Source.page687.drop 330).take 1 = [10] := by rfl
def cell703819 : Cell := ⟨(Source.page687.drop 331).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size687] <;> rfl⟩
theorem gap704326 : (Source.page687.drop 838).take 1 = [10] := by rfl
def cell704327 : Cell := ⟨(Source.page687.drop 839), 185, by simp only [List.length_take, List.length_drop, Source.size687] <;> rfl⟩
def coveredPage687 : Page := ⟨Source.page687, [cell703488, lf, cell703819, lf, cell704327], by
  have h := (cutBytes_cover [330, 1, 507, 1] Source.page687).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap703818, gap704326] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
