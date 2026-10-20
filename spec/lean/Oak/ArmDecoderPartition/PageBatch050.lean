import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch025

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell409600 : Cell := ⟨Source.page400.take 98, 98, by simp only [List.length_take, List.length_drop, Source.size400] <;> rfl⟩
theorem gap409698 : (Source.page400.drop 98).take 1 = [10] := by rfl
def cell409699 : Cell := ⟨(Source.page400.drop 99).take 386, 386, by simp only [List.length_take, List.length_drop, Source.size400] <;> rfl⟩
theorem gap410085 : (Source.page400.drop 485).take 1 = [10] := by rfl
def cell410086 : Cell := ⟨(Source.page400.drop 486).take 428, 428, by simp only [List.length_take, List.length_drop, Source.size400] <;> rfl⟩
theorem gap410514 : (Source.page400.drop 914).take 1 = [10] := by rfl
def cell410515 : Cell := ⟨(Source.page400.drop 915), 109, by simp only [List.length_take, List.length_drop, Source.size400] <;> rfl⟩
def coveredPage400 : Page := ⟨Source.page400, [cell409600, lf, cell409699, lf, cell410086, lf, cell410515], by
  have h := (cutBytes_cover [98, 1, 386, 1, 428, 1] Source.page400).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap409698, gap410085, gap410514] at h
  exact h⟩
def cell410624 : Cell := ⟨Source.page401.take 427, 427, by simp only [List.length_take, List.length_drop, Source.size401] <;> rfl⟩
theorem gap411051 : (Source.page401.drop 427).take 1 = [10] := by rfl
def cell411052 : Cell := ⟨(Source.page401.drop 428).take 446, 446, by simp only [List.length_take, List.length_drop, Source.size401] <;> rfl⟩
theorem gap411498 : (Source.page401.drop 874).take 1 = [10] := by rfl
def cell411499 : Cell := ⟨(Source.page401.drop 875), 149, by simp only [List.length_take, List.length_drop, Source.size401] <;> rfl⟩
def coveredPage401 : Page := ⟨Source.page401, [cell410624, lf, cell411052, lf, cell411499], by
  have h := (cutBytes_cover [427, 1, 446, 1] Source.page401).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap411051, gap411498] at h
  exact h⟩
def cell411648 : Cell := ⟨Source.page402.take 271, 271, by simp only [List.length_take, List.length_drop, Source.size402] <;> rfl⟩
theorem gap411919 : (Source.page402.drop 271).take 1 = [10] := by rfl
def cell411920 : Cell := ⟨(Source.page402.drop 272).take 536, 536, by simp only [List.length_take, List.length_drop, Source.size402] <;> rfl⟩
theorem gap412456 : (Source.page402.drop 808).take 1 = [10] := by rfl
def cell412457 : Cell := ⟨(Source.page402.drop 809), 215, by simp only [List.length_take, List.length_drop, Source.size402] <;> rfl⟩
def coveredPage402 : Page := ⟨Source.page402, [cell411648, lf, cell411920, lf, cell412457], by
  have h := (cutBytes_cover [271, 1, 536, 1] Source.page402).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap411919, gap412456] at h
  exact h⟩
def cell412672 : Cell := ⟨Source.page403.take 250, 250, by simp only [List.length_take, List.length_drop, Source.size403] <;> rfl⟩
theorem gap412922 : (Source.page403.drop 250).take 1 = [10] := by rfl
def cell412923 : Cell := ⟨(Source.page403.drop 251).take 575, 575, by simp only [List.length_take, List.length_drop, Source.size403] <;> rfl⟩
theorem gap413498 : (Source.page403.drop 826).take 1 = [10] := by rfl
def cell413499 : Cell := ⟨(Source.page403.drop 827), 197, by simp only [List.length_take, List.length_drop, Source.size403] <;> rfl⟩
def coveredPage403 : Page := ⟨Source.page403, [cell412672, lf, cell412923, lf, cell413499], by
  have h := (cutBytes_cover [250, 1, 575, 1] Source.page403).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap412922, gap413498] at h
  exact h⟩
def cell413696 : Cell := ⟨Source.page404.take 316, 316, by simp only [List.length_take, List.length_drop, Source.size404] <;> rfl⟩
theorem gap414012 : (Source.page404.drop 316).take 1 = [10] := by rfl
def cell414013 : Cell := ⟨(Source.page404.drop 317).take 465, 465, by simp only [List.length_take, List.length_drop, Source.size404] <;> rfl⟩
theorem gap414478 : (Source.page404.drop 782).take 1 = [10] := by rfl
def cell414479 : Cell := ⟨(Source.page404.drop 783), 241, by simp only [List.length_take, List.length_drop, Source.size404] <;> rfl⟩
def coveredPage404 : Page := ⟨Source.page404, [cell413696, lf, cell414013, lf, cell414479], by
  have h := (cutBytes_cover [316, 1, 465, 1] Source.page404).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap414012, gap414478] at h
  exact h⟩
def cell414720 : Cell := ⟨Source.page405.take 167, 167, by simp only [List.length_take, List.length_drop, Source.size405] <;> rfl⟩
theorem gap414887 : (Source.page405.drop 167).take 1 = [10] := by rfl
def cell414888 : Cell := ⟨(Source.page405.drop 168).take 458, 458, by simp only [List.length_take, List.length_drop, Source.size405] <;> rfl⟩
theorem gap415346 : (Source.page405.drop 626).take 1 = [10] := by rfl
def cell415347 : Cell := ⟨(Source.page405.drop 627), 397, by simp only [List.length_take, List.length_drop, Source.size405] <;> rfl⟩
def coveredPage405 : Page := ⟨Source.page405, [cell414720, lf, cell414888, lf, cell415347], by
  have h := (cutBytes_cover [167, 1, 458, 1] Source.page405).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap414887, gap415346] at h
  exact h⟩
def cell415744 : Cell := ⟨Source.page406.take 139, 139, by simp only [List.length_take, List.length_drop, Source.size406] <;> rfl⟩
theorem gap415883 : (Source.page406.drop 139).take 1 = [10] := by rfl
def cell415884 : Cell := ⟨(Source.page406.drop 140).take 472, 472, by simp only [List.length_take, List.length_drop, Source.size406] <;> rfl⟩
theorem gap416356 : (Source.page406.drop 612).take 1 = [10] := by rfl
def cell416357 : Cell := ⟨(Source.page406.drop 613), 411, by simp only [List.length_take, List.length_drop, Source.size406] <;> rfl⟩
def coveredPage406 : Page := ⟨Source.page406, [cell415744, lf, cell415884, lf, cell416357], by
  have h := (cutBytes_cover [139, 1, 472, 1] Source.page406).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap415883, gap416356] at h
  exact h⟩
def cell416768 : Cell := ⟨Source.page407.take 72, 72, by simp only [List.length_take, List.length_drop, Source.size407] <;> rfl⟩
theorem gap416840 : (Source.page407.drop 72).take 1 = [10] := by rfl
def cell416841 : Cell := ⟨(Source.page407.drop 73).take 517, 517, by simp only [List.length_take, List.length_drop, Source.size407] <;> rfl⟩
theorem gap417358 : (Source.page407.drop 590).take 1 = [10] := by rfl
def cell417359 : Cell := ⟨(Source.page407.drop 591).take 292, 292, by simp only [List.length_take, List.length_drop, Source.size407] <;> rfl⟩
theorem gap417651 : (Source.page407.drop 883).take 1 = [10] := by rfl
def cell417652 : Cell := ⟨(Source.page407.drop 884), 140, by simp only [List.length_take, List.length_drop, Source.size407] <;> rfl⟩
def coveredPage407 : Page := ⟨Source.page407, [cell416768, lf, cell416841, lf, cell417359, lf, cell417652], by
  have h := (cutBytes_cover [72, 1, 517, 1, 292, 1] Source.page407).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap416840, gap417358, gap417651] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
