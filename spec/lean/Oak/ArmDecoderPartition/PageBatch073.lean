import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch036

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell598016 : Cell := ⟨Source.page584.take 247, 247, by simp only [List.length_take, List.length_drop, Source.size584] <;> rfl⟩
theorem gap598263 : (Source.page584.drop 247).take 1 = [10] := by rfl
def cell598264 : Cell := ⟨(Source.page584.drop 248).take 462, 462, by simp only [List.length_take, List.length_drop, Source.size584] <;> rfl⟩
theorem gap598726 : (Source.page584.drop 710).take 1 = [10] := by rfl
def cell598727 : Cell := ⟨(Source.page584.drop 711), 313, by simp only [List.length_take, List.length_drop, Source.size584] <;> rfl⟩
def coveredPage584 : Page := ⟨Source.page584, [cell598016, lf, cell598264, lf, cell598727], by
  have h := (cutBytes_cover [247, 1, 462, 1] Source.page584).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap598263, gap598726] at h
  exact h⟩
def cell599040 : Cell := ⟨Source.page585.take 115, 115, by simp only [List.length_take, List.length_drop, Source.size585] <;> rfl⟩
theorem gap599155 : (Source.page585.drop 115).take 1 = [10] := by rfl
def cell599156 : Cell := ⟨(Source.page585.drop 116).take 511, 511, by simp only [List.length_take, List.length_drop, Source.size585] <;> rfl⟩
theorem gap599667 : (Source.page585.drop 627).take 1 = [10] := by rfl
def cell599668 : Cell := ⟨(Source.page585.drop 628), 396, by simp only [List.length_take, List.length_drop, Source.size585] <;> rfl⟩
def coveredPage585 : Page := ⟨Source.page585, [cell599040, lf, cell599156, lf, cell599668], by
  have h := (cutBytes_cover [115, 1, 511, 1] Source.page585).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap599155, gap599667] at h
  exact h⟩
def cell600064 : Cell := ⟨Source.page586.take 148, 148, by simp only [List.length_take, List.length_drop, Source.size586] <;> rfl⟩
theorem gap600212 : (Source.page586.drop 148).take 1 = [10] := by rfl
def cell600213 : Cell := ⟨(Source.page586.drop 149).take 499, 499, by simp only [List.length_take, List.length_drop, Source.size586] <;> rfl⟩
theorem gap600712 : (Source.page586.drop 648).take 1 = [10] := by rfl
def cell600713 : Cell := ⟨(Source.page586.drop 649), 375, by simp only [List.length_take, List.length_drop, Source.size586] <;> rfl⟩
def coveredPage586 : Page := ⟨Source.page586, [cell600064, lf, cell600213, lf, cell600713], by
  have h := (cutBytes_cover [148, 1, 499, 1] Source.page586).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap600212, gap600712] at h
  exact h⟩
def cell601088 : Cell := ⟨Source.page587.take 189, 189, by simp only [List.length_take, List.length_drop, Source.size587] <;> rfl⟩
theorem gap601277 : (Source.page587.drop 189).take 1 = [10] := by rfl
def cell601278 : Cell := ⟨(Source.page587.drop 190).take 386, 386, by simp only [List.length_take, List.length_drop, Source.size587] <;> rfl⟩
theorem gap601664 : (Source.page587.drop 576).take 1 = [10] := by rfl
def cell601665 : Cell := ⟨(Source.page587.drop 577), 447, by simp only [List.length_take, List.length_drop, Source.size587] <;> rfl⟩
def coveredPage587 : Page := ⟨Source.page587, [cell601088, lf, cell601278, lf, cell601665], by
  have h := (cutBytes_cover [189, 1, 386, 1] Source.page587).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap601277, gap601664] at h
  exact h⟩
def cell602112 : Cell := ⟨Source.page588.take 125, 125, by simp only [List.length_take, List.length_drop, Source.size588] <;> rfl⟩
theorem gap602237 : (Source.page588.drop 125).take 1 = [10] := by rfl
def cell602238 : Cell := ⟨(Source.page588.drop 126).take 372, 372, by simp only [List.length_take, List.length_drop, Source.size588] <;> rfl⟩
theorem gap602610 : (Source.page588.drop 498).take 1 = [10] := by rfl
def cell602611 : Cell := ⟨(Source.page588.drop 499).take 450, 450, by simp only [List.length_take, List.length_drop, Source.size588] <;> rfl⟩
theorem gap603061 : (Source.page588.drop 949).take 1 = [10] := by rfl
def cell603062 : Cell := ⟨(Source.page588.drop 950), 74, by simp only [List.length_take, List.length_drop, Source.size588] <;> rfl⟩
def coveredPage588 : Page := ⟨Source.page588, [cell602112, lf, cell602238, lf, cell602611, lf, cell603062], by
  have h := (cutBytes_cover [125, 1, 372, 1, 450, 1] Source.page588).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap602237, gap602610, gap603061] at h
  exact h⟩
def cell603136 : Cell := ⟨Source.page589.take 380, 380, by simp only [List.length_take, List.length_drop, Source.size589] <;> rfl⟩
theorem gap603516 : (Source.page589.drop 380).take 1 = [10] := by rfl
def cell603517 : Cell := ⟨(Source.page589.drop 381).take 495, 495, by simp only [List.length_take, List.length_drop, Source.size589] <;> rfl⟩
theorem gap604012 : (Source.page589.drop 876).take 1 = [10] := by rfl
def cell604013 : Cell := ⟨(Source.page589.drop 877), 147, by simp only [List.length_take, List.length_drop, Source.size589] <;> rfl⟩
def coveredPage589 : Page := ⟨Source.page589, [cell603136, lf, cell603517, lf, cell604013], by
  have h := (cutBytes_cover [380, 1, 495, 1] Source.page589).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap603516, gap604012] at h
  exact h⟩
def cell604160 : Cell := ⟨Source.page590.take 267, 267, by simp only [List.length_take, List.length_drop, Source.size590] <;> rfl⟩
theorem gap604427 : (Source.page590.drop 267).take 1 = [10] := by rfl
def cell604428 : Cell := ⟨(Source.page590.drop 268).take 546, 546, by simp only [List.length_take, List.length_drop, Source.size590] <;> rfl⟩
theorem gap604974 : (Source.page590.drop 814).take 1 = [10] := by rfl
def cell604975 : Cell := ⟨(Source.page590.drop 815), 209, by simp only [List.length_take, List.length_drop, Source.size590] <;> rfl⟩
def coveredPage590 : Page := ⟨Source.page590, [cell604160, lf, cell604428, lf, cell604975], by
  have h := (cutBytes_cover [267, 1, 546, 1] Source.page590).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap604427, gap604974] at h
  exact h⟩
def cell605184 : Cell := ⟨Source.page591.take 279, 279, by simp only [List.length_take, List.length_drop, Source.size591] <;> rfl⟩
theorem gap605463 : (Source.page591.drop 279).take 1 = [10] := by rfl
def cell605464 : Cell := ⟨(Source.page591.drop 280).take 459, 459, by simp only [List.length_take, List.length_drop, Source.size591] <;> rfl⟩
theorem gap605923 : (Source.page591.drop 739).take 1 = [10] := by rfl
def cell605924 : Cell := ⟨(Source.page591.drop 740), 284, by simp only [List.length_take, List.length_drop, Source.size591] <;> rfl⟩
def coveredPage591 : Page := ⟨Source.page591, [cell605184, lf, cell605464, lf, cell605924], by
  have h := (cutBytes_cover [279, 1, 459, 1] Source.page591).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap605463, gap605923] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
