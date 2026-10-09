import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch028

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell466944 : Cell := ⟨Source.page456.take 190, 190, by simp only [List.length_take, List.length_drop, Source.size456] <;> rfl⟩
theorem gap467134 : (Source.page456.drop 190).take 1 = [10] := by rfl
def cell467135 : Cell := ⟨(Source.page456.drop 191).take 524, 524, by simp only [List.length_take, List.length_drop, Source.size456] <;> rfl⟩
theorem gap467659 : (Source.page456.drop 715).take 1 = [10] := by rfl
def cell467660 : Cell := ⟨(Source.page456.drop 716), 308, by simp only [List.length_take, List.length_drop, Source.size456] <;> rfl⟩
def coveredPage456 : Page := ⟨Source.page456, [cell466944, lf, cell467135, lf, cell467660], by
  have h := (cutBytes_cover [190, 1, 524, 1] Source.page456).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap467134, gap467659] at h
  exact h⟩
def cell467968 : Cell := ⟨Source.page457.take 220, 220, by simp only [List.length_take, List.length_drop, Source.size457] <;> rfl⟩
theorem gap468188 : (Source.page457.drop 220).take 1 = [10] := by rfl
def cell468189 : Cell := ⟨(Source.page457.drop 221).take 381, 381, by simp only [List.length_take, List.length_drop, Source.size457] <;> rfl⟩
theorem gap468570 : (Source.page457.drop 602).take 1 = [10] := by rfl
def cell468571 : Cell := ⟨(Source.page457.drop 603), 421, by simp only [List.length_take, List.length_drop, Source.size457] <;> rfl⟩
def coveredPage457 : Page := ⟨Source.page457, [cell467968, lf, cell468189, lf, cell468571], by
  have h := (cutBytes_cover [220, 1, 381, 1] Source.page457).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap468188, gap468570] at h
  exact h⟩
def cell468992 : Cell := ⟨Source.page458.take 82, 82, by simp only [List.length_take, List.length_drop, Source.size458] <;> rfl⟩
theorem gap469074 : (Source.page458.drop 82).take 1 = [10] := by rfl
def cell469075 : Cell := ⟨(Source.page458.drop 83).take 370, 370, by simp only [List.length_take, List.length_drop, Source.size458] <;> rfl⟩
theorem gap469445 : (Source.page458.drop 453).take 1 = [10] := by rfl
def cell469446 : Cell := ⟨(Source.page458.drop 454).take 558, 558, by simp only [List.length_take, List.length_drop, Source.size458] <;> rfl⟩
theorem gap470004 : (Source.page458.drop 1012).take 1 = [10] := by rfl
def cell470005 : Cell := ⟨(Source.page458.drop 1013), 11, by simp only [List.length_take, List.length_drop, Source.size458] <;> rfl⟩
def coveredPage458 : Page := ⟨Source.page458, [cell468992, lf, cell469075, lf, cell469446, lf, cell470005], by
  have h := (cutBytes_cover [82, 1, 370, 1, 558, 1] Source.page458).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap469074, gap469445, gap470004] at h
  exact h⟩
def cell470016 : Cell := ⟨Source.page459.take 485, 485, by simp only [List.length_take, List.length_drop, Source.size459] <;> rfl⟩
theorem gap470501 : (Source.page459.drop 485).take 1 = [10] := by rfl
def cell470502 : Cell := ⟨(Source.page459.drop 486), 538, by simp only [List.length_take, List.length_drop, Source.size459] <;> rfl⟩
def coveredPage459 : Page := ⟨Source.page459, [cell470016, lf, cell470502], by
  have h := (cutBytes_cover [485, 1] Source.page459).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap470501] at h
  exact h⟩
def cell471040 : Cell := ⟨Source.page460.take 26, 26, by simp only [List.length_take, List.length_drop, Source.size460] <;> rfl⟩
theorem gap471066 : (Source.page460.drop 26).take 1 = [10] := by rfl
def cell471067 : Cell := ⟨(Source.page460.drop 27).take 547, 547, by simp only [List.length_take, List.length_drop, Source.size460] <;> rfl⟩
theorem gap471614 : (Source.page460.drop 574).take 1 = [10] := by rfl
def cell471615 : Cell := ⟨(Source.page460.drop 575), 449, by simp only [List.length_take, List.length_drop, Source.size460] <;> rfl⟩
def coveredPage460 : Page := ⟨Source.page460, [cell471040, lf, cell471067, lf, cell471615], by
  have h := (cutBytes_cover [26, 1, 547, 1] Source.page460).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap471066, gap471614] at h
  exact h⟩
def cell472064 : Cell := ⟨Source.page461.take 54, 54, by simp only [List.length_take, List.length_drop, Source.size461] <;> rfl⟩
theorem gap472118 : (Source.page461.drop 54).take 1 = [10] := by rfl
def cell472119 : Cell := ⟨(Source.page461.drop 55).take 532, 532, by simp only [List.length_take, List.length_drop, Source.size461] <;> rfl⟩
theorem gap472651 : (Source.page461.drop 587).take 1 = [10] := by rfl
def cell472652 : Cell := ⟨(Source.page461.drop 588).take 317, 317, by simp only [List.length_take, List.length_drop, Source.size461] <;> rfl⟩
theorem gap472969 : (Source.page461.drop 905).take 1 = [10] := by rfl
def cell472970 : Cell := ⟨(Source.page461.drop 906), 118, by simp only [List.length_take, List.length_drop, Source.size461] <;> rfl⟩
def coveredPage461 : Page := ⟨Source.page461, [cell472064, lf, cell472119, lf, cell472652, lf, cell472970], by
  have h := (cutBytes_cover [54, 1, 532, 1, 317, 1] Source.page461).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap472118, gap472651, gap472969] at h
  exact h⟩
def cell473088 : Cell := ⟨Source.page462.take 377, 377, by simp only [List.length_take, List.length_drop, Source.size462] <;> rfl⟩
theorem gap473465 : (Source.page462.drop 377).take 1 = [10] := by rfl
def cell473466 : Cell := ⟨(Source.page462.drop 378).take 544, 544, by simp only [List.length_take, List.length_drop, Source.size462] <;> rfl⟩
theorem gap474010 : (Source.page462.drop 922).take 1 = [10] := by rfl
def cell474011 : Cell := ⟨(Source.page462.drop 923), 101, by simp only [List.length_take, List.length_drop, Source.size462] <;> rfl⟩
def coveredPage462 : Page := ⟨Source.page462, [cell473088, lf, cell473466, lf, cell474011], by
  have h := (cutBytes_cover [377, 1, 544, 1] Source.page462).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap473465, gap474010] at h
  exact h⟩
def cell474112 : Cell := ⟨Source.page463.take 461, 461, by simp only [List.length_take, List.length_drop, Source.size463] <;> rfl⟩
theorem gap474573 : (Source.page463.drop 461).take 1 = [10] := by rfl
def cell474574 : Cell := ⟨(Source.page463.drop 462).take 441, 441, by simp only [List.length_take, List.length_drop, Source.size463] <;> rfl⟩
theorem gap475015 : (Source.page463.drop 903).take 1 = [10] := by rfl
def cell475016 : Cell := ⟨(Source.page463.drop 904), 120, by simp only [List.length_take, List.length_drop, Source.size463] <;> rfl⟩
def coveredPage463 : Page := ⟨Source.page463, [cell474112, lf, cell474574, lf, cell475016], by
  have h := (cutBytes_cover [461, 1, 441, 1] Source.page463).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap474573, gap475015] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
