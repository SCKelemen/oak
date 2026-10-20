import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch048

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell794624 : Cell := ⟨Source.page776.take 485, 485, by simp only [List.length_take, List.length_drop, Source.size776] <;> rfl⟩
theorem gap795109 : (Source.page776.drop 485).take 1 = [10] := by rfl
def cell795110 : Cell := ⟨(Source.page776.drop 486).take 504, 504, by simp only [List.length_take, List.length_drop, Source.size776] <;> rfl⟩
theorem gap795614 : (Source.page776.drop 990).take 1 = [10] := by rfl
def cell795615 : Cell := ⟨(Source.page776.drop 991), 33, by simp only [List.length_take, List.length_drop, Source.size776] <;> rfl⟩
def coveredPage776 : Page := ⟨Source.page776, [cell794624, lf, cell795110, lf, cell795615], by
  have h := (cutBytes_cover [485, 1, 504, 1] Source.page776).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap795109, gap795614] at h
  exact h⟩
def cell795648 : Cell := ⟨Source.page777.take 539, 539, by simp only [List.length_take, List.length_drop, Source.size777] <;> rfl⟩
theorem gap796187 : (Source.page777.drop 539).take 1 = [10] := by rfl
def cell796188 : Cell := ⟨(Source.page777.drop 540), 484, by simp only [List.length_take, List.length_drop, Source.size777] <;> rfl⟩
def coveredPage777 : Page := ⟨Source.page777, [cell795648, lf, cell796188], by
  have h := (cutBytes_cover [539, 1] Source.page777).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap796187] at h
  exact h⟩
def cell796672 : Cell := ⟨Source.page778.take 187, 187, by simp only [List.length_take, List.length_drop, Source.size778] <;> rfl⟩
theorem gap796859 : (Source.page778.drop 187).take 1 = [10] := by rfl
def cell796860 : Cell := ⟨(Source.page778.drop 188).take 520, 520, by simp only [List.length_take, List.length_drop, Source.size778] <;> rfl⟩
theorem gap797380 : (Source.page778.drop 708).take 1 = [10] := by rfl
def cell797381 : Cell := ⟨(Source.page778.drop 709), 315, by simp only [List.length_take, List.length_drop, Source.size778] <;> rfl⟩
def coveredPage778 : Page := ⟨Source.page778, [cell796672, lf, cell796860, lf, cell797381], by
  have h := (cutBytes_cover [187, 1, 520, 1] Source.page778).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap796859, gap797380] at h
  exact h⟩
def cell797696 : Cell := ⟨Source.page779.take 230, 230, by simp only [List.length_take, List.length_drop, Source.size779] <;> rfl⟩
theorem gap797926 : (Source.page779.drop 230).take 1 = [10] := by rfl
def cell797927 : Cell := ⟨(Source.page779.drop 231).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size779] <;> rfl⟩
theorem gap798353 : (Source.page779.drop 657).take 1 = [10] := by rfl
def cell798354 : Cell := ⟨(Source.page779.drop 658), 366, by simp only [List.length_take, List.length_drop, Source.size779] <;> rfl⟩
def coveredPage779 : Page := ⟨Source.page779, [cell797696, lf, cell797927, lf, cell798354], by
  have h := (cutBytes_cover [230, 1, 426, 1] Source.page779).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap797926, gap798353] at h
  exact h⟩
def cell798720 : Cell := ⟨Source.page780.take 135, 135, by simp only [List.length_take, List.length_drop, Source.size780] <;> rfl⟩
theorem gap798855 : (Source.page780.drop 135).take 1 = [10] := by rfl
def cell798856 : Cell := ⟨(Source.page780.drop 136).take 411, 411, by simp only [List.length_take, List.length_drop, Source.size780] <;> rfl⟩
theorem gap799267 : (Source.page780.drop 547).take 1 = [10] := by rfl
def cell799268 : Cell := ⟨(Source.page780.drop 548).take 304, 304, by simp only [List.length_take, List.length_drop, Source.size780] <;> rfl⟩
theorem gap799572 : (Source.page780.drop 852).take 1 = [10] := by rfl
def cell799573 : Cell := ⟨(Source.page780.drop 853), 171, by simp only [List.length_take, List.length_drop, Source.size780] <;> rfl⟩
def coveredPage780 : Page := ⟨Source.page780, [cell798720, lf, cell798856, lf, cell799268, lf, cell799573], by
  have h := (cutBytes_cover [135, 1, 411, 1, 304, 1] Source.page780).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap798855, gap799267, gap799572] at h
  exact h⟩
def cell799744 : Cell := ⟨Source.page781.take 243, 243, by simp only [List.length_take, List.length_drop, Source.size781] <;> rfl⟩
theorem gap799987 : (Source.page781.drop 243).take 1 = [10] := by rfl
def cell799988 : Cell := ⟨(Source.page781.drop 244).take 459, 459, by simp only [List.length_take, List.length_drop, Source.size781] <;> rfl⟩
theorem gap800447 : (Source.page781.drop 703).take 1 = [10] := by rfl
def cell800448 : Cell := ⟨(Source.page781.drop 704).take 317, 317, by simp only [List.length_take, List.length_drop, Source.size781] <;> rfl⟩
theorem gap800765 : (Source.page781.drop 1021).take 1 = [10] := by rfl
def cell800766 : Cell := ⟨(Source.page781.drop 1022), 2, by simp only [List.length_take, List.length_drop, Source.size781] <;> rfl⟩
def coveredPage781 : Page := ⟨Source.page781, [cell799744, lf, cell799988, lf, cell800448, lf, cell800766], by
  have h := (cutBytes_cover [243, 1, 459, 1, 317, 1] Source.page781).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap799987, gap800447, gap800765] at h
  exact h⟩
def cell800768 : Cell := ⟨Source.page782.take 463, 463, by simp only [List.length_take, List.length_drop, Source.size782] <;> rfl⟩
theorem gap801231 : (Source.page782.drop 463).take 1 = [10] := by rfl
def cell801232 : Cell := ⟨(Source.page782.drop 464).take 467, 467, by simp only [List.length_take, List.length_drop, Source.size782] <;> rfl⟩
theorem gap801699 : (Source.page782.drop 931).take 1 = [10] := by rfl
def cell801700 : Cell := ⟨(Source.page782.drop 932), 92, by simp only [List.length_take, List.length_drop, Source.size782] <;> rfl⟩
def coveredPage782 : Page := ⟨Source.page782, [cell800768, lf, cell801232, lf, cell801700], by
  have h := (cutBytes_cover [463, 1, 467, 1] Source.page782).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap801231, gap801699] at h
  exact h⟩
def cell801792 : Cell := ⟨Source.page783.take 370, 370, by simp only [List.length_take, List.length_drop, Source.size783] <;> rfl⟩
theorem gap802162 : (Source.page783.drop 370).take 1 = [10] := by rfl
def cell802163 : Cell := ⟨(Source.page783.drop 371).take 438, 438, by simp only [List.length_take, List.length_drop, Source.size783] <;> rfl⟩
theorem gap802601 : (Source.page783.drop 809).take 1 = [10] := by rfl
def cell802602 : Cell := ⟨(Source.page783.drop 810), 214, by simp only [List.length_take, List.length_drop, Source.size783] <;> rfl⟩
def coveredPage783 : Page := ⟨Source.page783, [cell801792, lf, cell802163, lf, cell802602], by
  have h := (cutBytes_cover [370, 1, 438, 1] Source.page783).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap802162, gap802601] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
