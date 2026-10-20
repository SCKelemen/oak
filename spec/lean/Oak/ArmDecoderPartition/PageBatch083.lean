import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch041

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell679936 : Cell := ⟨Source.page664.take 117, 117, by simp only [List.length_take, List.length_drop, Source.size664] <;> rfl⟩
theorem gap680053 : (Source.page664.drop 117).take 1 = [10] := by rfl
def cell680054 : Cell := ⟨(Source.page664.drop 118).take 397, 397, by simp only [List.length_take, List.length_drop, Source.size664] <;> rfl⟩
theorem gap680451 : (Source.page664.drop 515).take 1 = [10] := by rfl
def cell680452 : Cell := ⟨(Source.page664.drop 516), 508, by simp only [List.length_take, List.length_drop, Source.size664] <;> rfl⟩
def coveredPage664 : Page := ⟨Source.page664, [cell679936, lf, cell680054, lf, cell680452], by
  have h := (cutBytes_cover [117, 1, 397, 1] Source.page664).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap680053, gap680451] at h
  exact h⟩
def cell680960 : Cell := ⟨Source.page665.take 23, 23, by simp only [List.length_take, List.length_drop, Source.size665] <;> rfl⟩
theorem gap680983 : (Source.page665.drop 23).take 1 = [10] := by rfl
def cell680984 : Cell := ⟨(Source.page665.drop 24).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size665] <;> rfl⟩
theorem gap681455 : (Source.page665.drop 495).take 1 = [10] := by rfl
def cell681456 : Cell := ⟨(Source.page665.drop 496), 528, by simp only [List.length_take, List.length_drop, Source.size665] <;> rfl⟩
def coveredPage665 : Page := ⟨Source.page665, [cell680960, lf, cell680984, lf, cell681456], by
  have h := (cutBytes_cover [23, 1, 471, 1] Source.page665).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap680983, gap681455] at h
  exact h⟩
def cell681984 : Cell := ⟨Source.page666.take 18, 18, by simp only [List.length_take, List.length_drop, Source.size666] <;> rfl⟩
theorem gap682002 : (Source.page666.drop 18).take 1 = [10] := by rfl
def cell682003 : Cell := ⟨(Source.page666.drop 19).take 428, 428, by simp only [List.length_take, List.length_drop, Source.size666] <;> rfl⟩
theorem gap682431 : (Source.page666.drop 447).take 1 = [10] := by rfl
def cell682432 : Cell := ⟨(Source.page666.drop 448).take 425, 425, by simp only [List.length_take, List.length_drop, Source.size666] <;> rfl⟩
theorem gap682857 : (Source.page666.drop 873).take 1 = [10] := by rfl
def cell682858 : Cell := ⟨(Source.page666.drop 874), 150, by simp only [List.length_take, List.length_drop, Source.size666] <;> rfl⟩
def coveredPage666 : Page := ⟨Source.page666, [cell681984, lf, cell682003, lf, cell682432, lf, cell682858], by
  have h := (cutBytes_cover [18, 1, 428, 1, 425, 1] Source.page666).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap682002, gap682431, gap682857] at h
  exact h⟩
def cell683008 : Cell := ⟨Source.page667.take 366, 366, by simp only [List.length_take, List.length_drop, Source.size667] <;> rfl⟩
theorem gap683374 : (Source.page667.drop 366).take 1 = [10] := by rfl
def cell683375 : Cell := ⟨(Source.page667.drop 367).take 423, 423, by simp only [List.length_take, List.length_drop, Source.size667] <;> rfl⟩
theorem gap683798 : (Source.page667.drop 790).take 1 = [10] := by rfl
def cell683799 : Cell := ⟨(Source.page667.drop 791), 233, by simp only [List.length_take, List.length_drop, Source.size667] <;> rfl⟩
def coveredPage667 : Page := ⟨Source.page667, [cell683008, lf, cell683375, lf, cell683799], by
  have h := (cutBytes_cover [366, 1, 423, 1] Source.page667).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap683374, gap683798] at h
  exact h⟩
def cell684032 : Cell := ⟨Source.page668.take 229, 229, by simp only [List.length_take, List.length_drop, Source.size668] <;> rfl⟩
theorem gap684261 : (Source.page668.drop 229).take 1 = [10] := by rfl
def cell684262 : Cell := ⟨(Source.page668.drop 230).take 463, 463, by simp only [List.length_take, List.length_drop, Source.size668] <;> rfl⟩
theorem gap684725 : (Source.page668.drop 693).take 1 = [10] := by rfl
def cell684726 : Cell := ⟨(Source.page668.drop 694), 330, by simp only [List.length_take, List.length_drop, Source.size668] <;> rfl⟩
def coveredPage668 : Page := ⟨Source.page668, [cell684032, lf, cell684262, lf, cell684726], by
  have h := (cutBytes_cover [229, 1, 463, 1] Source.page668).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap684261, gap684725] at h
  exact h⟩
def cell685056 : Cell := ⟨Source.page669.take 124, 124, by simp only [List.length_take, List.length_drop, Source.size669] <;> rfl⟩
theorem gap685180 : (Source.page669.drop 124).take 1 = [10] := by rfl
def cell685181 : Cell := ⟨(Source.page669.drop 125).take 612, 612, by simp only [List.length_take, List.length_drop, Source.size669] <;> rfl⟩
theorem gap685793 : (Source.page669.drop 737).take 1 = [10] := by rfl
def cell685794 : Cell := ⟨(Source.page669.drop 738), 286, by simp only [List.length_take, List.length_drop, Source.size669] <;> rfl⟩
def coveredPage669 : Page := ⟨Source.page669, [cell685056, lf, cell685181, lf, cell685794], by
  have h := (cutBytes_cover [124, 1, 612, 1] Source.page669).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap685180, gap685793] at h
  exact h⟩
def cell686080 : Cell := ⟨Source.page670.take 224, 224, by simp only [List.length_take, List.length_drop, Source.size670] <;> rfl⟩
theorem gap686304 : (Source.page670.drop 224).take 1 = [10] := by rfl
def cell686305 : Cell := ⟨(Source.page670.drop 225).take 417, 417, by simp only [List.length_take, List.length_drop, Source.size670] <;> rfl⟩
theorem gap686722 : (Source.page670.drop 642).take 1 = [10] := by rfl
def cell686723 : Cell := ⟨(Source.page670.drop 643), 381, by simp only [List.length_take, List.length_drop, Source.size670] <;> rfl⟩
def coveredPage670 : Page := ⟨Source.page670, [cell686080, lf, cell686305, lf, cell686723], by
  have h := (cutBytes_cover [224, 1, 417, 1] Source.page670).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap686304, gap686722] at h
  exact h⟩
def cell687104 : Cell := ⟨Source.page671.take 83, 83, by simp only [List.length_take, List.length_drop, Source.size671] <;> rfl⟩
theorem gap687187 : (Source.page671.drop 83).take 1 = [10] := by rfl
def cell687188 : Cell := ⟨(Source.page671.drop 84).take 513, 513, by simp only [List.length_take, List.length_drop, Source.size671] <;> rfl⟩
theorem gap687701 : (Source.page671.drop 597).take 1 = [10] := by rfl
def cell687702 : Cell := ⟨(Source.page671.drop 598), 426, by simp only [List.length_take, List.length_drop, Source.size671] <;> rfl⟩
def coveredPage671 : Page := ⟨Source.page671, [cell687104, lf, cell687188, lf, cell687702], by
  have h := (cutBytes_cover [83, 1, 513, 1] Source.page671).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap687187, gap687701] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
