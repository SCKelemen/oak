import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch039

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell647168 : Cell := ⟨Source.page632.take 365, 365, by simp only [List.length_take, List.length_drop, Source.size632] <;> rfl⟩
theorem gap647533 : (Source.page632.drop 365).take 1 = [10] := by rfl
def cell647534 : Cell := ⟨(Source.page632.drop 366).take 447, 447, by simp only [List.length_take, List.length_drop, Source.size632] <;> rfl⟩
theorem gap647981 : (Source.page632.drop 813).take 1 = [10] := by rfl
def cell647982 : Cell := ⟨(Source.page632.drop 814), 210, by simp only [List.length_take, List.length_drop, Source.size632] <;> rfl⟩
def coveredPage632 : Page := ⟨Source.page632, [cell647168, lf, cell647534, lf, cell647982], by
  have h := (cutBytes_cover [365, 1, 447, 1] Source.page632).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap647533, gap647981] at h
  exact h⟩
def cell648192 : Cell := ⟨Source.page633.take 291, 291, by simp only [List.length_take, List.length_drop, Source.size633] <;> rfl⟩
theorem gap648483 : (Source.page633.drop 291).take 1 = [10] := by rfl
def cell648484 : Cell := ⟨(Source.page633.drop 292).take 454, 454, by simp only [List.length_take, List.length_drop, Source.size633] <;> rfl⟩
theorem gap648938 : (Source.page633.drop 746).take 1 = [10] := by rfl
def cell648939 : Cell := ⟨(Source.page633.drop 747), 277, by simp only [List.length_take, List.length_drop, Source.size633] <;> rfl⟩
def coveredPage633 : Page := ⟨Source.page633, [cell648192, lf, cell648484, lf, cell648939], by
  have h := (cutBytes_cover [291, 1, 454, 1] Source.page633).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap648483, gap648938] at h
  exact h⟩
def cell649216 : Cell := ⟨Source.page634.take 241, 241, by simp only [List.length_take, List.length_drop, Source.size634] <;> rfl⟩
theorem gap649457 : (Source.page634.drop 241).take 1 = [10] := by rfl
def cell649458 : Cell := ⟨(Source.page634.drop 242).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size634] <;> rfl⟩
theorem gap649938 : (Source.page634.drop 722).take 1 = [10] := by rfl
def cell649939 : Cell := ⟨(Source.page634.drop 723), 301, by simp only [List.length_take, List.length_drop, Source.size634] <;> rfl⟩
def coveredPage634 : Page := ⟨Source.page634, [cell649216, lf, cell649458, lf, cell649939], by
  have h := (cutBytes_cover [241, 1, 480, 1] Source.page634).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap649457, gap649938] at h
  exact h⟩
def cell650240 : Cell := ⟨Source.page635.take 173, 173, by simp only [List.length_take, List.length_drop, Source.size635] <;> rfl⟩
theorem gap650413 : (Source.page635.drop 173).take 1 = [10] := by rfl
def cell650414 : Cell := ⟨(Source.page635.drop 174).take 422, 422, by simp only [List.length_take, List.length_drop, Source.size635] <;> rfl⟩
theorem gap650836 : (Source.page635.drop 596).take 1 = [10] := by rfl
def cell650837 : Cell := ⟨(Source.page635.drop 597), 427, by simp only [List.length_take, List.length_drop, Source.size635] <;> rfl⟩
def coveredPage635 : Page := ⟨Source.page635, [cell650240, lf, cell650414, lf, cell650837], by
  have h := (cutBytes_cover [173, 1, 422, 1] Source.page635).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap650413, gap650836] at h
  exact h⟩
def cell651264 : Cell := ⟨Source.page636.take 8, 8, by simp only [List.length_take, List.length_drop, Source.size636] <;> rfl⟩
theorem gap651272 : (Source.page636.drop 8).take 1 = [10] := by rfl
def cell651273 : Cell := ⟨(Source.page636.drop 9).take 536, 536, by simp only [List.length_take, List.length_drop, Source.size636] <;> rfl⟩
theorem gap651809 : (Source.page636.drop 545).take 1 = [10] := by rfl
def cell651810 : Cell := ⟨(Source.page636.drop 546).take 396, 396, by simp only [List.length_take, List.length_drop, Source.size636] <;> rfl⟩
theorem gap652206 : (Source.page636.drop 942).take 1 = [10] := by rfl
def cell652207 : Cell := ⟨(Source.page636.drop 943), 81, by simp only [List.length_take, List.length_drop, Source.size636] <;> rfl⟩
def coveredPage636 : Page := ⟨Source.page636, [cell651264, lf, cell651273, lf, cell651810, lf, cell652207], by
  have h := (cutBytes_cover [8, 1, 536, 1, 396, 1] Source.page636).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap651272, gap651809, gap652206] at h
  exact h⟩
def cell652288 : Cell := ⟨Source.page637.take 352, 352, by simp only [List.length_take, List.length_drop, Source.size637] <;> rfl⟩
theorem gap652640 : (Source.page637.drop 352).take 1 = [10] := by rfl
def cell652641 : Cell := ⟨(Source.page637.drop 353).take 330, 330, by simp only [List.length_take, List.length_drop, Source.size637] <;> rfl⟩
theorem gap652971 : (Source.page637.drop 683).take 1 = [10] := by rfl
def cell652972 : Cell := ⟨(Source.page637.drop 684), 340, by simp only [List.length_take, List.length_drop, Source.size637] <;> rfl⟩
def coveredPage637 : Page := ⟨Source.page637, [cell652288, lf, cell652641, lf, cell652972], by
  have h := (cutBytes_cover [352, 1, 330, 1] Source.page637).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap652640, gap652971] at h
  exact h⟩
def cell653312 : Cell := ⟨Source.page638.take 203, 203, by simp only [List.length_take, List.length_drop, Source.size638] <;> rfl⟩
theorem gap653515 : (Source.page638.drop 203).take 1 = [10] := by rfl
def cell653516 : Cell := ⟨(Source.page638.drop 204).take 285, 285, by simp only [List.length_take, List.length_drop, Source.size638] <;> rfl⟩
theorem gap653801 : (Source.page638.drop 489).take 1 = [10] := by rfl
def cell653802 : Cell := ⟨(Source.page638.drop 490).take 451, 451, by simp only [List.length_take, List.length_drop, Source.size638] <;> rfl⟩
theorem gap654253 : (Source.page638.drop 941).take 1 = [10] := by rfl
def cell654254 : Cell := ⟨(Source.page638.drop 942), 82, by simp only [List.length_take, List.length_drop, Source.size638] <;> rfl⟩
def coveredPage638 : Page := ⟨Source.page638, [cell653312, lf, cell653516, lf, cell653802, lf, cell654254], by
  have h := (cutBytes_cover [203, 1, 285, 1, 451, 1] Source.page638).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap653515, gap653801, gap654253] at h
  exact h⟩
def cell654336 : Cell := ⟨Source.page639.take 232, 232, by simp only [List.length_take, List.length_drop, Source.size639] <;> rfl⟩
theorem gap654568 : (Source.page639.drop 232).take 1 = [10] := by rfl
def cell654569 : Cell := ⟨(Source.page639.drop 233).take 631, 631, by simp only [List.length_take, List.length_drop, Source.size639] <;> rfl⟩
theorem gap655200 : (Source.page639.drop 864).take 1 = [10] := by rfl
def cell655201 : Cell := ⟨(Source.page639.drop 865), 159, by simp only [List.length_take, List.length_drop, Source.size639] <;> rfl⟩
def coveredPage639 : Page := ⟨Source.page639, [cell654336, lf, cell654569, lf, cell655201], by
  have h := (cutBytes_cover [232, 1, 631, 1] Source.page639).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap654568, gap655200] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
