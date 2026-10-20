import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch036

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell589824 : Cell := ⟨Source.page576.take 475, 475, by simp only [List.length_take, List.length_drop, Source.size576] <;> rfl⟩
theorem gap590299 : (Source.page576.drop 475).take 1 = [10] := by rfl
def cell590300 : Cell := ⟨(Source.page576.drop 476).take 532, 532, by simp only [List.length_take, List.length_drop, Source.size576] <;> rfl⟩
theorem gap590832 : (Source.page576.drop 1008).take 1 = [10] := by rfl
def cell590833 : Cell := ⟨(Source.page576.drop 1009), 15, by simp only [List.length_take, List.length_drop, Source.size576] <;> rfl⟩
def coveredPage576 : Page := ⟨Source.page576, [cell589824, lf, cell590300, lf, cell590833], by
  have h := (cutBytes_cover [475, 1, 532, 1] Source.page576).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap590299, gap590832] at h
  exact h⟩
def cell590848 : Cell := ⟨Source.page577.take 481, 481, by simp only [List.length_take, List.length_drop, Source.size577] <;> rfl⟩
theorem gap591329 : (Source.page577.drop 481).take 1 = [10] := by rfl
def cell591330 : Cell := ⟨(Source.page577.drop 482).take 515, 515, by simp only [List.length_take, List.length_drop, Source.size577] <;> rfl⟩
theorem gap591845 : (Source.page577.drop 997).take 1 = [10] := by rfl
def cell591846 : Cell := ⟨(Source.page577.drop 998), 26, by simp only [List.length_take, List.length_drop, Source.size577] <;> rfl⟩
def coveredPage577 : Page := ⟨Source.page577, [cell590848, lf, cell591330, lf, cell591846], by
  have h := (cutBytes_cover [481, 1, 515, 1] Source.page577).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap591329, gap591845] at h
  exact h⟩
def cell591872 : Cell := ⟨Source.page578.take 475, 475, by simp only [List.length_take, List.length_drop, Source.size578] <;> rfl⟩
theorem gap592347 : (Source.page578.drop 475).take 1 = [10] := by rfl
def cell592348 : Cell := ⟨(Source.page578.drop 476).take 447, 447, by simp only [List.length_take, List.length_drop, Source.size578] <;> rfl⟩
theorem gap592795 : (Source.page578.drop 923).take 1 = [10] := by rfl
def cell592796 : Cell := ⟨(Source.page578.drop 924), 100, by simp only [List.length_take, List.length_drop, Source.size578] <;> rfl⟩
def coveredPage578 : Page := ⟨Source.page578, [cell591872, lf, cell592348, lf, cell592796], by
  have h := (cutBytes_cover [475, 1, 447, 1] Source.page578).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap592347, gap592795] at h
  exact h⟩
def cell592896 : Cell := ⟨Source.page579.take 395, 395, by simp only [List.length_take, List.length_drop, Source.size579] <;> rfl⟩
theorem gap593291 : (Source.page579.drop 395).take 1 = [10] := by rfl
def cell593292 : Cell := ⟨(Source.page579.drop 396).take 465, 465, by simp only [List.length_take, List.length_drop, Source.size579] <;> rfl⟩
theorem gap593757 : (Source.page579.drop 861).take 1 = [10] := by rfl
def cell593758 : Cell := ⟨(Source.page579.drop 862), 162, by simp only [List.length_take, List.length_drop, Source.size579] <;> rfl⟩
def coveredPage579 : Page := ⟨Source.page579, [cell592896, lf, cell593292, lf, cell593758], by
  have h := (cutBytes_cover [395, 1, 465, 1] Source.page579).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap593291, gap593757] at h
  exact h⟩
def cell593920 : Cell := ⟨Source.page580.take 309, 309, by simp only [List.length_take, List.length_drop, Source.size580] <;> rfl⟩
theorem gap594229 : (Source.page580.drop 309).take 1 = [10] := by rfl
def cell594230 : Cell := ⟨(Source.page580.drop 310).take 300, 300, by simp only [List.length_take, List.length_drop, Source.size580] <;> rfl⟩
theorem gap594530 : (Source.page580.drop 610).take 1 = [10] := by rfl
def cell594531 : Cell := ⟨(Source.page580.drop 611), 413, by simp only [List.length_take, List.length_drop, Source.size580] <;> rfl⟩
def coveredPage580 : Page := ⟨Source.page580, [cell593920, lf, cell594230, lf, cell594531], by
  have h := (cutBytes_cover [309, 1, 300, 1] Source.page580).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap594229, gap594530] at h
  exact h⟩
def cell594944 : Cell := ⟨Source.page581.take 191, 191, by simp only [List.length_take, List.length_drop, Source.size581] <;> rfl⟩
theorem gap595135 : (Source.page581.drop 191).take 1 = [10] := by rfl
def cell595136 : Cell := ⟨(Source.page581.drop 192).take 400, 400, by simp only [List.length_take, List.length_drop, Source.size581] <;> rfl⟩
theorem gap595536 : (Source.page581.drop 592).take 1 = [10] := by rfl
def cell595537 : Cell := ⟨(Source.page581.drop 593), 431, by simp only [List.length_take, List.length_drop, Source.size581] <;> rfl⟩
def coveredPage581 : Page := ⟨Source.page581, [cell594944, lf, cell595136, lf, cell595537], by
  have h := (cutBytes_cover [191, 1, 400, 1] Source.page581).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap595135, gap595536] at h
  exact h⟩
def cell595968 : Cell := ⟨Source.page582.take 71, 71, by simp only [List.length_take, List.length_drop, Source.size582] <;> rfl⟩
theorem gap596039 : (Source.page582.drop 71).take 1 = [10] := by rfl
def cell596040 : Cell := ⟨(Source.page582.drop 72).take 468, 468, by simp only [List.length_take, List.length_drop, Source.size582] <;> rfl⟩
theorem gap596508 : (Source.page582.drop 540).take 1 = [10] := by rfl
def cell596509 : Cell := ⟨(Source.page582.drop 541).take 419, 419, by simp only [List.length_take, List.length_drop, Source.size582] <;> rfl⟩
theorem gap596928 : (Source.page582.drop 960).take 1 = [10] := by rfl
def cell596929 : Cell := ⟨(Source.page582.drop 961), 63, by simp only [List.length_take, List.length_drop, Source.size582] <;> rfl⟩
def coveredPage582 : Page := ⟨Source.page582, [cell595968, lf, cell596040, lf, cell596509, lf, cell596929], by
  have h := (cutBytes_cover [71, 1, 468, 1, 419, 1] Source.page582).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap596039, gap596508, gap596928] at h
  exact h⟩
def cell596992 : Cell := ⟨Source.page583.take 407, 407, by simp only [List.length_take, List.length_drop, Source.size583] <;> rfl⟩
theorem gap597399 : (Source.page583.drop 407).take 1 = [10] := by rfl
def cell597400 : Cell := ⟨(Source.page583.drop 408).take 414, 414, by simp only [List.length_take, List.length_drop, Source.size583] <;> rfl⟩
theorem gap597814 : (Source.page583.drop 822).take 1 = [10] := by rfl
def cell597815 : Cell := ⟨(Source.page583.drop 823), 201, by simp only [List.length_take, List.length_drop, Source.size583] <;> rfl⟩
def coveredPage583 : Page := ⟨Source.page583, [cell596992, lf, cell597400, lf, cell597815], by
  have h := (cutBytes_cover [407, 1, 414, 1] Source.page583).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap597399, gap597814] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
