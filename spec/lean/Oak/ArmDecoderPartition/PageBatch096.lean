import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch048

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell786432 : Cell := ⟨Source.page768.take 408, 408, by simp only [List.length_take, List.length_drop, Source.size768] <;> rfl⟩
theorem gap786840 : (Source.page768.drop 408).take 1 = [10] := by rfl
def cell786841 : Cell := ⟨(Source.page768.drop 409).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size768] <;> rfl⟩
theorem gap787348 : (Source.page768.drop 916).take 1 = [10] := by rfl
def cell787349 : Cell := ⟨(Source.page768.drop 917), 107, by simp only [List.length_take, List.length_drop, Source.size768] <;> rfl⟩
def coveredPage768 : Page := ⟨Source.page768, [cell786432, lf, cell786841, lf, cell787349], by
  have h := (cutBytes_cover [408, 1, 507, 1] Source.page768).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap786840, gap787348] at h
  exact h⟩
def cell787456 : Cell := ⟨Source.page769.take 352, 352, by simp only [List.length_take, List.length_drop, Source.size769] <;> rfl⟩
theorem gap787808 : (Source.page769.drop 352).take 1 = [10] := by rfl
def cell787809 : Cell := ⟨(Source.page769.drop 353).take 499, 499, by simp only [List.length_take, List.length_drop, Source.size769] <;> rfl⟩
theorem gap788308 : (Source.page769.drop 852).take 1 = [10] := by rfl
def cell788309 : Cell := ⟨(Source.page769.drop 853), 171, by simp only [List.length_take, List.length_drop, Source.size769] <;> rfl⟩
def coveredPage769 : Page := ⟨Source.page769, [cell787456, lf, cell787809, lf, cell788309], by
  have h := (cutBytes_cover [352, 1, 499, 1] Source.page769).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap787808, gap788308] at h
  exact h⟩
def cell788480 : Cell := ⟨Source.page770.take 164, 164, by simp only [List.length_take, List.length_drop, Source.size770] <;> rfl⟩
theorem gap788644 : (Source.page770.drop 164).take 1 = [10] := by rfl
def cell788645 : Cell := ⟨(Source.page770.drop 165).take 423, 423, by simp only [List.length_take, List.length_drop, Source.size770] <;> rfl⟩
theorem gap789068 : (Source.page770.drop 588).take 1 = [10] := by rfl
def cell789069 : Cell := ⟨(Source.page770.drop 589).take 417, 417, by simp only [List.length_take, List.length_drop, Source.size770] <;> rfl⟩
theorem gap789486 : (Source.page770.drop 1006).take 1 = [10] := by rfl
def cell789487 : Cell := ⟨(Source.page770.drop 1007), 17, by simp only [List.length_take, List.length_drop, Source.size770] <;> rfl⟩
def coveredPage770 : Page := ⟨Source.page770, [cell788480, lf, cell788645, lf, cell789069, lf, cell789487], by
  have h := (cutBytes_cover [164, 1, 423, 1, 417, 1] Source.page770).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap788644, gap789068, gap789486] at h
  exact h⟩
def cell789504 : Cell := ⟨Source.page771.take 286, 286, by simp only [List.length_take, List.length_drop, Source.size771] <;> rfl⟩
theorem gap789790 : (Source.page771.drop 286).take 1 = [10] := by rfl
def cell789791 : Cell := ⟨(Source.page771.drop 287).take 396, 396, by simp only [List.length_take, List.length_drop, Source.size771] <;> rfl⟩
theorem gap790187 : (Source.page771.drop 683).take 1 = [10] := by rfl
def cell790188 : Cell := ⟨(Source.page771.drop 684), 340, by simp only [List.length_take, List.length_drop, Source.size771] <;> rfl⟩
def coveredPage771 : Page := ⟨Source.page771, [cell789504, lf, cell789791, lf, cell790188], by
  have h := (cutBytes_cover [286, 1, 396, 1] Source.page771).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap789790, gap790187] at h
  exact h⟩
def cell790528 : Cell := ⟨Source.page772.take 157, 157, by simp only [List.length_take, List.length_drop, Source.size772] <;> rfl⟩
theorem gap790685 : (Source.page772.drop 157).take 1 = [10] := by rfl
def cell790686 : Cell := ⟨(Source.page772.drop 158).take 514, 514, by simp only [List.length_take, List.length_drop, Source.size772] <;> rfl⟩
theorem gap791200 : (Source.page772.drop 672).take 1 = [10] := by rfl
def cell791201 : Cell := ⟨(Source.page772.drop 673), 351, by simp only [List.length_take, List.length_drop, Source.size772] <;> rfl⟩
def coveredPage772 : Page := ⟨Source.page772, [cell790528, lf, cell790686, lf, cell791201], by
  have h := (cutBytes_cover [157, 1, 514, 1] Source.page772).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap790685, gap791200] at h
  exact h⟩
def cell791552 : Cell := ⟨Source.page773.take 195, 195, by simp only [List.length_take, List.length_drop, Source.size773] <;> rfl⟩
theorem gap791747 : (Source.page773.drop 195).take 1 = [10] := by rfl
def cell791748 : Cell := ⟨(Source.page773.drop 196).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size773] <;> rfl⟩
theorem gap792255 : (Source.page773.drop 703).take 1 = [10] := by rfl
def cell792256 : Cell := ⟨(Source.page773.drop 704), 320, by simp only [List.length_take, List.length_drop, Source.size773] <;> rfl⟩
def coveredPage773 : Page := ⟨Source.page773, [cell791552, lf, cell791748, lf, cell792256], by
  have h := (cutBytes_cover [195, 1, 507, 1] Source.page773).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap791747, gap792255] at h
  exact h⟩
def cell792576 : Cell := ⟨Source.page774.take 61, 61, by simp only [List.length_take, List.length_drop, Source.size774] <;> rfl⟩
theorem gap792637 : (Source.page774.drop 61).take 1 = [10] := by rfl
def cell792638 : Cell := ⟨(Source.page774.drop 62).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size774] <;> rfl⟩
theorem gap793145 : (Source.page774.drop 569).take 1 = [10] := by rfl
def cell793146 : Cell := ⟨(Source.page774.drop 570).take 450, 450, by simp only [List.length_take, List.length_drop, Source.size774] <;> rfl⟩
theorem gap793596 : (Source.page774.drop 1020).take 1 = [10] := by rfl
def cell793597 : Cell := ⟨(Source.page774.drop 1021), 3, by simp only [List.length_take, List.length_drop, Source.size774] <;> rfl⟩
def coveredPage774 : Page := ⟨Source.page774, [cell792576, lf, cell792638, lf, cell793146, lf, cell793597], by
  have h := (cutBytes_cover [61, 1, 507, 1, 450, 1] Source.page774).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap792637, gap793145, gap793596] at h
  exact h⟩
def cell793600 : Cell := ⟨Source.page775.take 455, 455, by simp only [List.length_take, List.length_drop, Source.size775] <;> rfl⟩
theorem gap794055 : (Source.page775.drop 455).take 1 = [10] := by rfl
def cell794056 : Cell := ⟨(Source.page775.drop 456).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size775] <;> rfl⟩
theorem gap794557 : (Source.page775.drop 957).take 1 = [10] := by rfl
def cell794558 : Cell := ⟨(Source.page775.drop 958), 66, by simp only [List.length_take, List.length_drop, Source.size775] <;> rfl⟩
def coveredPage775 : Page := ⟨Source.page775, [cell793600, lf, cell794056, lf, cell794558], by
  have h := (cutBytes_cover [455, 1, 501, 1] Source.page775).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap794055, gap794557] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
