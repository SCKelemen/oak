import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch031

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell507904 : Cell := ⟨Source.page496.take 529, 529, by simp only [List.length_take, List.length_drop, Source.size496] <;> rfl⟩
theorem gap508433 : (Source.page496.drop 529).take 1 = [10] := by rfl
def cell508434 : Cell := ⟨(Source.page496.drop 530), 494, by simp only [List.length_take, List.length_drop, Source.size496] <;> rfl⟩
def coveredPage496 : Page := ⟨Source.page496, [cell507904, lf, cell508434], by
  have h := (cutBytes_cover [529, 1] Source.page496).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap508433] at h
  exact h⟩
def cell508928 : Cell := ⟨Source.page497.take 8, 8, by simp only [List.length_take, List.length_drop, Source.size497] <;> rfl⟩
theorem gap508936 : (Source.page497.drop 8).take 1 = [10] := by rfl
def cell508937 : Cell := ⟨(Source.page497.drop 9).take 474, 474, by simp only [List.length_take, List.length_drop, Source.size497] <;> rfl⟩
theorem gap509411 : (Source.page497.drop 483).take 1 = [10] := by rfl
def cell509412 : Cell := ⟨(Source.page497.drop 484).take 451, 451, by simp only [List.length_take, List.length_drop, Source.size497] <;> rfl⟩
theorem gap509863 : (Source.page497.drop 935).take 1 = [10] := by rfl
def cell509864 : Cell := ⟨(Source.page497.drop 936), 88, by simp only [List.length_take, List.length_drop, Source.size497] <;> rfl⟩
def coveredPage497 : Page := ⟨Source.page497, [cell508928, lf, cell508937, lf, cell509412, lf, cell509864], by
  have h := (cutBytes_cover [8, 1, 474, 1, 451, 1] Source.page497).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap508936, gap509411, gap509863] at h
  exact h⟩
def cell509952 : Cell := ⟨Source.page498.take 390, 390, by simp only [List.length_take, List.length_drop, Source.size498] <;> rfl⟩
theorem gap510342 : (Source.page498.drop 390).take 1 = [10] := by rfl
def cell510343 : Cell := ⟨(Source.page498.drop 391).take 522, 522, by simp only [List.length_take, List.length_drop, Source.size498] <;> rfl⟩
theorem gap510865 : (Source.page498.drop 913).take 1 = [10] := by rfl
def cell510866 : Cell := ⟨(Source.page498.drop 914), 110, by simp only [List.length_take, List.length_drop, Source.size498] <;> rfl⟩
def coveredPage498 : Page := ⟨Source.page498, [cell509952, lf, cell510343, lf, cell510866], by
  have h := (cutBytes_cover [390, 1, 522, 1] Source.page498).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap510342, gap510865] at h
  exact h⟩
def cell510976 : Cell := ⟨Source.page499.take 288, 288, by simp only [List.length_take, List.length_drop, Source.size499] <;> rfl⟩
theorem gap511264 : (Source.page499.drop 288).take 1 = [10] := by rfl
def cell511265 : Cell := ⟨(Source.page499.drop 289).take 478, 478, by simp only [List.length_take, List.length_drop, Source.size499] <;> rfl⟩
theorem gap511743 : (Source.page499.drop 767).take 1 = [10] := by rfl
def cell511744 : Cell := ⟨(Source.page499.drop 768), 256, by simp only [List.length_take, List.length_drop, Source.size499] <;> rfl⟩
def coveredPage499 : Page := ⟨Source.page499, [cell510976, lf, cell511265, lf, cell511744], by
  have h := (cutBytes_cover [288, 1, 478, 1] Source.page499).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap511264, gap511743] at h
  exact h⟩
def cell512000 : Cell := ⟨Source.page500.take 206, 206, by simp only [List.length_take, List.length_drop, Source.size500] <;> rfl⟩
theorem gap512206 : (Source.page500.drop 206).take 1 = [10] := by rfl
def cell512207 : Cell := ⟨(Source.page500.drop 207).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size500] <;> rfl⟩
theorem gap512714 : (Source.page500.drop 714).take 1 = [10] := by rfl
def cell512715 : Cell := ⟨(Source.page500.drop 715), 309, by simp only [List.length_take, List.length_drop, Source.size500] <;> rfl⟩
def coveredPage500 : Page := ⟨Source.page500, [cell512000, lf, cell512207, lf, cell512715], by
  have h := (cutBytes_cover [206, 1, 507, 1] Source.page500).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap512206, gap512714] at h
  exact h⟩
def cell513024 : Cell := ⟨Source.page501.take 114, 114, by simp only [List.length_take, List.length_drop, Source.size501] <;> rfl⟩
theorem gap513138 : (Source.page501.drop 114).take 1 = [10] := by rfl
def cell513139 : Cell := ⟨(Source.page501.drop 115).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size501] <;> rfl⟩
theorem gap513610 : (Source.page501.drop 586).take 1 = [10] := by rfl
def cell513611 : Cell := ⟨(Source.page501.drop 587), 437, by simp only [List.length_take, List.length_drop, Source.size501] <;> rfl⟩
def coveredPage501 : Page := ⟨Source.page501, [cell513024, lf, cell513139, lf, cell513611], by
  have h := (cutBytes_cover [114, 1, 471, 1] Source.page501).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap513138, gap513610] at h
  exact h⟩
def cell514048 : Cell := ⟨Source.page502.take 64, 64, by simp only [List.length_take, List.length_drop, Source.size502] <;> rfl⟩
theorem gap514112 : (Source.page502.drop 64).take 1 = [10] := by rfl
def cell514113 : Cell := ⟨(Source.page502.drop 65).take 408, 408, by simp only [List.length_take, List.length_drop, Source.size502] <;> rfl⟩
theorem gap514521 : (Source.page502.drop 473).take 1 = [10] := by rfl
def cell514522 : Cell := ⟨(Source.page502.drop 474), 550, by simp only [List.length_take, List.length_drop, Source.size502] <;> rfl⟩
def coveredPage502 : Page := ⟨Source.page502, [cell514048, lf, cell514113, lf, cell514522], by
  have h := (cutBytes_cover [64, 1, 408, 1] Source.page502).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap514112, gap514521] at h
  exact h⟩
def cell515072 : Cell := ⟨Source.page503.take 4, 4, by simp only [List.length_take, List.length_drop, Source.size503] <;> rfl⟩
theorem gap515076 : (Source.page503.drop 4).take 1 = [10] := by rfl
def cell515077 : Cell := ⟨(Source.page503.drop 5).take 446, 446, by simp only [List.length_take, List.length_drop, Source.size503] <;> rfl⟩
theorem gap515523 : (Source.page503.drop 451).take 1 = [10] := by rfl
def cell515524 : Cell := ⟨(Source.page503.drop 452).take 499, 499, by simp only [List.length_take, List.length_drop, Source.size503] <;> rfl⟩
theorem gap516023 : (Source.page503.drop 951).take 1 = [10] := by rfl
def cell516024 : Cell := ⟨(Source.page503.drop 952), 72, by simp only [List.length_take, List.length_drop, Source.size503] <;> rfl⟩
def coveredPage503 : Page := ⟨Source.page503, [cell515072, lf, cell515077, lf, cell515524, lf, cell516024], by
  have h := (cutBytes_cover [4, 1, 446, 1, 499, 1] Source.page503).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap515076, gap515523, gap516023] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
