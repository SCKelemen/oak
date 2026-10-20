import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch049

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell811008 : Cell := ⟨Source.page792.take 386, 386, by simp only [List.length_take, List.length_drop, Source.size792] <;> rfl⟩
theorem gap811394 : (Source.page792.drop 386).take 1 = [10] := by rfl
def cell811395 : Cell := ⟨(Source.page792.drop 387).take 381, 381, by simp only [List.length_take, List.length_drop, Source.size792] <;> rfl⟩
theorem gap811776 : (Source.page792.drop 768).take 1 = [10] := by rfl
def cell811777 : Cell := ⟨(Source.page792.drop 769), 255, by simp only [List.length_take, List.length_drop, Source.size792] <;> rfl⟩
def coveredPage792 : Page := ⟨Source.page792, [cell811008, lf, cell811395, lf, cell811777], by
  have h := (cutBytes_cover [386, 1, 381, 1] Source.page792).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap811394, gap811776] at h
  exact h⟩
def cell812032 : Cell := ⟨Source.page793.take 247, 247, by simp only [List.length_take, List.length_drop, Source.size793] <;> rfl⟩
theorem gap812279 : (Source.page793.drop 247).take 1 = [10] := by rfl
def cell812280 : Cell := ⟨(Source.page793.drop 248).take 656, 656, by simp only [List.length_take, List.length_drop, Source.size793] <;> rfl⟩
theorem gap812936 : (Source.page793.drop 904).take 1 = [10] := by rfl
def cell812937 : Cell := ⟨(Source.page793.drop 905), 119, by simp only [List.length_take, List.length_drop, Source.size793] <;> rfl⟩
def coveredPage793 : Page := ⟨Source.page793, [cell812032, lf, cell812280, lf, cell812937], by
  have h := (cutBytes_cover [247, 1, 656, 1] Source.page793).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap812279, gap812936] at h
  exact h⟩
def cell813056 : Cell := ⟨Source.page794.take 448, 448, by simp only [List.length_take, List.length_drop, Source.size794] <;> rfl⟩
theorem gap813504 : (Source.page794.drop 448).take 1 = [10] := by rfl
def cell813505 : Cell := ⟨(Source.page794.drop 449).take 513, 513, by simp only [List.length_take, List.length_drop, Source.size794] <;> rfl⟩
theorem gap814018 : (Source.page794.drop 962).take 1 = [10] := by rfl
def cell814019 : Cell := ⟨(Source.page794.drop 963), 61, by simp only [List.length_take, List.length_drop, Source.size794] <;> rfl⟩
def coveredPage794 : Page := ⟨Source.page794, [cell813056, lf, cell813505, lf, cell814019], by
  have h := (cutBytes_cover [448, 1, 513, 1] Source.page794).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap813504, gap814018] at h
  exact h⟩
def cell814080 : Cell := ⟨Source.page795.take 446, 446, by simp only [List.length_take, List.length_drop, Source.size795] <;> rfl⟩
theorem gap814526 : (Source.page795.drop 446).take 1 = [10] := by rfl
def cell814527 : Cell := ⟨(Source.page795.drop 447).take 522, 522, by simp only [List.length_take, List.length_drop, Source.size795] <;> rfl⟩
theorem gap815049 : (Source.page795.drop 969).take 1 = [10] := by rfl
def cell815050 : Cell := ⟨(Source.page795.drop 970), 54, by simp only [List.length_take, List.length_drop, Source.size795] <;> rfl⟩
def coveredPage795 : Page := ⟨Source.page795, [cell814080, lf, cell814527, lf, cell815050], by
  have h := (cutBytes_cover [446, 1, 522, 1] Source.page795).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap814526, gap815049] at h
  exact h⟩
def cell815104 : Cell := ⟨Source.page796.take 399, 399, by simp only [List.length_take, List.length_drop, Source.size796] <;> rfl⟩
theorem gap815503 : (Source.page796.drop 399).take 1 = [10] := by rfl
def cell815504 : Cell := ⟨(Source.page796.drop 400).take 400, 400, by simp only [List.length_take, List.length_drop, Source.size796] <;> rfl⟩
theorem gap815904 : (Source.page796.drop 800).take 1 = [10] := by rfl
def cell815905 : Cell := ⟨(Source.page796.drop 801), 223, by simp only [List.length_take, List.length_drop, Source.size796] <;> rfl⟩
def coveredPage796 : Page := ⟨Source.page796, [cell815104, lf, cell815504, lf, cell815905], by
  have h := (cutBytes_cover [399, 1, 400, 1] Source.page796).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap815503, gap815904] at h
  exact h⟩
def cell816128 : Cell := ⟨Source.page797.take 247, 247, by simp only [List.length_take, List.length_drop, Source.size797] <;> rfl⟩
theorem gap816375 : (Source.page797.drop 247).take 1 = [10] := by rfl
def cell816376 : Cell := ⟨(Source.page797.drop 248).take 447, 447, by simp only [List.length_take, List.length_drop, Source.size797] <;> rfl⟩
theorem gap816823 : (Source.page797.drop 695).take 1 = [10] := by rfl
def cell816824 : Cell := ⟨(Source.page797.drop 696), 328, by simp only [List.length_take, List.length_drop, Source.size797] <;> rfl⟩
def coveredPage797 : Page := ⟨Source.page797, [cell816128, lf, cell816376, lf, cell816824], by
  have h := (cutBytes_cover [247, 1, 447, 1] Source.page797).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap816375, gap816823] at h
  exact h⟩
def cell817152 : Cell := ⟨Source.page798.take 152, 152, by simp only [List.length_take, List.length_drop, Source.size798] <;> rfl⟩
theorem gap817304 : (Source.page798.drop 152).take 1 = [10] := by rfl
def cell817305 : Cell := ⟨(Source.page798.drop 153).take 487, 487, by simp only [List.length_take, List.length_drop, Source.size798] <;> rfl⟩
theorem gap817792 : (Source.page798.drop 640).take 1 = [10] := by rfl
def cell817793 : Cell := ⟨(Source.page798.drop 641), 383, by simp only [List.length_take, List.length_drop, Source.size798] <;> rfl⟩
def coveredPage798 : Page := ⟨Source.page798, [cell817152, lf, cell817305, lf, cell817793], by
  have h := (cutBytes_cover [152, 1, 487, 1] Source.page798).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap817304, gap817792] at h
  exact h⟩
def cell818176 : Cell := ⟨Source.page799.take 85, 85, by simp only [List.length_take, List.length_drop, Source.size799] <;> rfl⟩
theorem gap818261 : (Source.page799.drop 85).take 1 = [10] := by rfl
def cell818262 : Cell := ⟨(Source.page799.drop 86).take 612, 612, by simp only [List.length_take, List.length_drop, Source.size799] <;> rfl⟩
theorem gap818874 : (Source.page799.drop 698).take 1 = [10] := by rfl
def cell818875 : Cell := ⟨(Source.page799.drop 699), 325, by simp only [List.length_take, List.length_drop, Source.size799] <;> rfl⟩
def coveredPage799 : Page := ⟨Source.page799, [cell818176, lf, cell818262, lf, cell818875], by
  have h := (cutBytes_cover [85, 1, 612, 1] Source.page799).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap818261, gap818874] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
