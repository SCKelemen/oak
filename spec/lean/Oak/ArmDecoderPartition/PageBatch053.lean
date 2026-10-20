import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch026

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell434176 : Cell := ⟨Source.page424.take 157, 157, by simp only [List.length_take, List.length_drop, Source.size424] <;> rfl⟩
theorem gap434333 : (Source.page424.drop 157).take 1 = [10] := by rfl
def cell434334 : Cell := ⟨(Source.page424.drop 158).take 545, 545, by simp only [List.length_take, List.length_drop, Source.size424] <;> rfl⟩
theorem gap434879 : (Source.page424.drop 703).take 1 = [10] := by rfl
def cell434880 : Cell := ⟨(Source.page424.drop 704), 320, by simp only [List.length_take, List.length_drop, Source.size424] <;> rfl⟩
def coveredPage424 : Page := ⟨Source.page424, [cell434176, lf, cell434334, lf, cell434880], by
  have h := (cutBytes_cover [157, 1, 545, 1] Source.page424).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap434333, gap434879] at h
  exact h⟩
def cell435200 : Cell := ⟨Source.page425.take 199, 199, by simp only [List.length_take, List.length_drop, Source.size425] <;> rfl⟩
theorem gap435399 : (Source.page425.drop 199).take 1 = [10] := by rfl
def cell435400 : Cell := ⟨(Source.page425.drop 200).take 513, 513, by simp only [List.length_take, List.length_drop, Source.size425] <;> rfl⟩
theorem gap435913 : (Source.page425.drop 713).take 1 = [10] := by rfl
def cell435914 : Cell := ⟨(Source.page425.drop 714), 310, by simp only [List.length_take, List.length_drop, Source.size425] <;> rfl⟩
def coveredPage425 : Page := ⟨Source.page425, [cell435200, lf, cell435400, lf, cell435914], by
  have h := (cutBytes_cover [199, 1, 513, 1] Source.page425).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap435399, gap435913] at h
  exact h⟩
def cell436224 : Cell := ⟨Source.page426.take 48, 48, by simp only [List.length_take, List.length_drop, Source.size426] <;> rfl⟩
theorem gap436272 : (Source.page426.drop 48).take 1 = [10] := by rfl
def cell436273 : Cell := ⟨(Source.page426.drop 49).take 474, 474, by simp only [List.length_take, List.length_drop, Source.size426] <;> rfl⟩
theorem gap436747 : (Source.page426.drop 523).take 1 = [10] := by rfl
def cell436748 : Cell := ⟨(Source.page426.drop 524).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size426] <;> rfl⟩
theorem gap437228 : (Source.page426.drop 1004).take 1 = [10] := by rfl
def cell437229 : Cell := ⟨(Source.page426.drop 1005), 19, by simp only [List.length_take, List.length_drop, Source.size426] <;> rfl⟩
def coveredPage426 : Page := ⟨Source.page426, [cell436224, lf, cell436273, lf, cell436748, lf, cell437229], by
  have h := (cutBytes_cover [48, 1, 474, 1, 480, 1] Source.page426).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap436272, gap436747, gap437228] at h
  exact h⟩
def cell437248 : Cell := ⟨Source.page427.take 350, 350, by simp only [List.length_take, List.length_drop, Source.size427] <;> rfl⟩
theorem gap437598 : (Source.page427.drop 350).take 1 = [10] := by rfl
def cell437599 : Cell := ⟨(Source.page427.drop 351).take 407, 407, by simp only [List.length_take, List.length_drop, Source.size427] <;> rfl⟩
theorem gap438006 : (Source.page427.drop 758).take 1 = [10] := by rfl
def cell438007 : Cell := ⟨(Source.page427.drop 759), 265, by simp only [List.length_take, List.length_drop, Source.size427] <;> rfl⟩
def coveredPage427 : Page := ⟨Source.page427, [cell437248, lf, cell437599, lf, cell438007], by
  have h := (cutBytes_cover [350, 1, 407, 1] Source.page427).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap437598, gap438006] at h
  exact h⟩
def cell438272 : Cell := ⟨Source.page428.take 289, 289, by simp only [List.length_take, List.length_drop, Source.size428] <;> rfl⟩
theorem gap438561 : (Source.page428.drop 289).take 1 = [10] := by rfl
def cell438562 : Cell := ⟨(Source.page428.drop 290).take 435, 435, by simp only [List.length_take, List.length_drop, Source.size428] <;> rfl⟩
theorem gap438997 : (Source.page428.drop 725).take 1 = [10] := by rfl
def cell438998 : Cell := ⟨(Source.page428.drop 726), 298, by simp only [List.length_take, List.length_drop, Source.size428] <;> rfl⟩
def coveredPage428 : Page := ⟨Source.page428, [cell438272, lf, cell438562, lf, cell438998], by
  have h := (cutBytes_cover [289, 1, 435, 1] Source.page428).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap438561, gap438997] at h
  exact h⟩
def cell439296 : Cell := ⟨Source.page429.take 109, 109, by simp only [List.length_take, List.length_drop, Source.size429] <;> rfl⟩
theorem gap439405 : (Source.page429.drop 109).take 1 = [10] := by rfl
def cell439406 : Cell := ⟨(Source.page429.drop 110).take 525, 525, by simp only [List.length_take, List.length_drop, Source.size429] <;> rfl⟩
theorem gap439931 : (Source.page429.drop 635).take 1 = [10] := by rfl
def cell439932 : Cell := ⟨(Source.page429.drop 636), 388, by simp only [List.length_take, List.length_drop, Source.size429] <;> rfl⟩
def coveredPage429 : Page := ⟨Source.page429, [cell439296, lf, cell439406, lf, cell439932], by
  have h := (cutBytes_cover [109, 1, 525, 1] Source.page429).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap439405, gap439931] at h
  exact h⟩
def cell440320 : Cell := ⟨Source.page430.take 40, 40, by simp only [List.length_take, List.length_drop, Source.size430] <;> rfl⟩
theorem gap440360 : (Source.page430.drop 40).take 1 = [10] := by rfl
def cell440361 : Cell := ⟨(Source.page430.drop 41).take 414, 414, by simp only [List.length_take, List.length_drop, Source.size430] <;> rfl⟩
theorem gap440775 : (Source.page430.drop 455).take 1 = [10] := by rfl
def cell440776 : Cell := ⟨(Source.page430.drop 456).take 394, 394, by simp only [List.length_take, List.length_drop, Source.size430] <;> rfl⟩
theorem gap441170 : (Source.page430.drop 850).take 1 = [10] := by rfl
def cell441171 : Cell := ⟨(Source.page430.drop 851), 173, by simp only [List.length_take, List.length_drop, Source.size430] <;> rfl⟩
def coveredPage430 : Page := ⟨Source.page430, [cell440320, lf, cell440361, lf, cell440776, lf, cell441171], by
  have h := (cutBytes_cover [40, 1, 414, 1, 394, 1] Source.page430).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap440360, gap440775, gap441170] at h
  exact h⟩
def cell441344 : Cell := ⟨Source.page431.take 119, 119, by simp only [List.length_take, List.length_drop, Source.size431] <;> rfl⟩
theorem gap441463 : (Source.page431.drop 119).take 1 = [10] := by rfl
def cell441464 : Cell := ⟨(Source.page431.drop 120).take 522, 522, by simp only [List.length_take, List.length_drop, Source.size431] <;> rfl⟩
theorem gap441986 : (Source.page431.drop 642).take 1 = [10] := by rfl
def cell441987 : Cell := ⟨(Source.page431.drop 643), 381, by simp only [List.length_take, List.length_drop, Source.size431] <;> rfl⟩
def coveredPage431 : Page := ⟨Source.page431, [cell441344, lf, cell441464, lf, cell441987], by
  have h := (cutBytes_cover [119, 1, 522, 1] Source.page431).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap441463, gap441986] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
