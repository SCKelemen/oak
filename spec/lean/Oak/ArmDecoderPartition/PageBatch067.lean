import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch033

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell548864 : Cell := ⟨Source.page536.take 461, 461, by simp only [List.length_take, List.length_drop, Source.size536] <;> rfl⟩
theorem gap549325 : (Source.page536.drop 461).take 1 = [10] := by rfl
def cell549326 : Cell := ⟨(Source.page536.drop 462).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size536] <;> rfl⟩
theorem gap549797 : (Source.page536.drop 933).take 1 = [10] := by rfl
def cell549798 : Cell := ⟨(Source.page536.drop 934), 90, by simp only [List.length_take, List.length_drop, Source.size536] <;> rfl⟩
def coveredPage536 : Page := ⟨Source.page536, [cell548864, lf, cell549326, lf, cell549798], by
  have h := (cutBytes_cover [461, 1, 471, 1] Source.page536).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap549325, gap549797] at h
  exact h⟩
def cell549888 : Cell := ⟨Source.page537.take 388, 388, by simp only [List.length_take, List.length_drop, Source.size537] <;> rfl⟩
theorem gap550276 : (Source.page537.drop 388).take 1 = [10] := by rfl
def cell550277 : Cell := ⟨(Source.page537.drop 389).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size537] <;> rfl⟩
theorem gap550757 : (Source.page537.drop 869).take 1 = [10] := by rfl
def cell550758 : Cell := ⟨(Source.page537.drop 870), 154, by simp only [List.length_take, List.length_drop, Source.size537] <;> rfl⟩
def coveredPage537 : Page := ⟨Source.page537, [cell549888, lf, cell550277, lf, cell550758], by
  have h := (cutBytes_cover [388, 1, 480, 1] Source.page537).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap550276, gap550757] at h
  exact h⟩
def cell550912 : Cell := ⟨Source.page538.take 308, 308, by simp only [List.length_take, List.length_drop, Source.size538] <;> rfl⟩
theorem gap551220 : (Source.page538.drop 308).take 1 = [10] := by rfl
def cell551221 : Cell := ⟨(Source.page538.drop 309).take 440, 440, by simp only [List.length_take, List.length_drop, Source.size538] <;> rfl⟩
theorem gap551661 : (Source.page538.drop 749).take 1 = [10] := by rfl
def cell551662 : Cell := ⟨(Source.page538.drop 750), 274, by simp only [List.length_take, List.length_drop, Source.size538] <;> rfl⟩
def coveredPage538 : Page := ⟨Source.page538, [cell550912, lf, cell551221, lf, cell551662], by
  have h := (cutBytes_cover [308, 1, 440, 1] Source.page538).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap551220, gap551661] at h
  exact h⟩
def cell551936 : Cell := ⟨Source.page539.take 195, 195, by simp only [List.length_take, List.length_drop, Source.size539] <;> rfl⟩
theorem gap552131 : (Source.page539.drop 195).take 1 = [10] := by rfl
def cell552132 : Cell := ⟨(Source.page539.drop 196).take 472, 472, by simp only [List.length_take, List.length_drop, Source.size539] <;> rfl⟩
theorem gap552604 : (Source.page539.drop 668).take 1 = [10] := by rfl
def cell552605 : Cell := ⟨(Source.page539.drop 669), 355, by simp only [List.length_take, List.length_drop, Source.size539] <;> rfl⟩
def coveredPage539 : Page := ⟨Source.page539, [cell551936, lf, cell552132, lf, cell552605], by
  have h := (cutBytes_cover [195, 1, 472, 1] Source.page539).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap552131, gap552604] at h
  exact h⟩
def cell552960 : Cell := ⟨Source.page540.take 151, 151, by simp only [List.length_take, List.length_drop, Source.size540] <;> rfl⟩
theorem gap553111 : (Source.page540.drop 151).take 1 = [10] := by rfl
def cell553112 : Cell := ⟨(Source.page540.drop 152).take 459, 459, by simp only [List.length_take, List.length_drop, Source.size540] <;> rfl⟩
theorem gap553571 : (Source.page540.drop 611).take 1 = [10] := by rfl
def cell553572 : Cell := ⟨(Source.page540.drop 612), 412, by simp only [List.length_take, List.length_drop, Source.size540] <;> rfl⟩
def coveredPage540 : Page := ⟨Source.page540, [cell552960, lf, cell553112, lf, cell553572], by
  have h := (cutBytes_cover [151, 1, 459, 1] Source.page540).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap553111, gap553571] at h
  exact h⟩
def cell553984 : Cell := ⟨Source.page541.take 66, 66, by simp only [List.length_take, List.length_drop, Source.size541] <;> rfl⟩
theorem gap554050 : (Source.page541.drop 66).take 1 = [10] := by rfl
def cell554051 : Cell := ⟨(Source.page541.drop 67).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size541] <;> rfl⟩
theorem gap554522 : (Source.page541.drop 538).take 1 = [10] := by rfl
def cell554523 : Cell := ⟨(Source.page541.drop 539), 485, by simp only [List.length_take, List.length_drop, Source.size541] <;> rfl⟩
def coveredPage541 : Page := ⟨Source.page541, [cell553984, lf, cell554051, lf, cell554523], by
  have h := (cutBytes_cover [66, 1, 471, 1] Source.page541).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap554050, gap554522] at h
  exact h⟩
def cell555008 : Cell := ⟨Source.page542.take 59, 59, by simp only [List.length_take, List.length_drop, Source.size542] <;> rfl⟩
theorem gap555067 : (Source.page542.drop 59).take 1 = [10] := by rfl
def cell555068 : Cell := ⟨(Source.page542.drop 60).take 334, 334, by simp only [List.length_take, List.length_drop, Source.size542] <;> rfl⟩
theorem gap555402 : (Source.page542.drop 394).take 1 = [10] := by rfl
def cell555403 : Cell := ⟨(Source.page542.drop 395).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size542] <;> rfl⟩
theorem gap555883 : (Source.page542.drop 875).take 1 = [10] := by rfl
def cell555884 : Cell := ⟨(Source.page542.drop 876), 148, by simp only [List.length_take, List.length_drop, Source.size542] <;> rfl⟩
def coveredPage542 : Page := ⟨Source.page542, [cell555008, lf, cell555068, lf, cell555403, lf, cell555884], by
  have h := (cutBytes_cover [59, 1, 334, 1, 480, 1] Source.page542).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap555067, gap555402, gap555883] at h
  exact h⟩
def cell556032 : Cell := ⟨Source.page543.take 278, 278, by simp only [List.length_take, List.length_drop, Source.size543] <;> rfl⟩
theorem gap556310 : (Source.page543.drop 278).take 1 = [10] := by rfl
def cell556311 : Cell := ⟨(Source.page543.drop 279).take 357, 357, by simp only [List.length_take, List.length_drop, Source.size543] <;> rfl⟩
theorem gap556668 : (Source.page543.drop 636).take 1 = [10] := by rfl
def cell556669 : Cell := ⟨(Source.page543.drop 637), 387, by simp only [List.length_take, List.length_drop, Source.size543] <;> rfl⟩
def coveredPage543 : Page := ⟨Source.page543, [cell556032, lf, cell556311, lf, cell556669], by
  have h := (cutBytes_cover [278, 1, 357, 1] Source.page543).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap556310, gap556668] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
