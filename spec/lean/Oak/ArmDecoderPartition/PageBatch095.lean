import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch047

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell778240 : Cell := ⟨Source.page760.take 79, 79, by simp only [List.length_take, List.length_drop, Source.size760] <;> rfl⟩
theorem gap778319 : (Source.page760.drop 79).take 1 = [10] := by rfl
def cell778320 : Cell := ⟨(Source.page760.drop 80).take 566, 566, by simp only [List.length_take, List.length_drop, Source.size760] <;> rfl⟩
theorem gap778886 : (Source.page760.drop 646).take 1 = [10] := by rfl
def cell778887 : Cell := ⟨(Source.page760.drop 647), 377, by simp only [List.length_take, List.length_drop, Source.size760] <;> rfl⟩
def coveredPage760 : Page := ⟨Source.page760, [cell778240, lf, cell778320, lf, cell778887], by
  have h := (cutBytes_cover [79, 1, 566, 1] Source.page760).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap778319, gap778886] at h
  exact h⟩
def cell779264 : Cell := ⟨Source.page761.take 124, 124, by simp only [List.length_take, List.length_drop, Source.size761] <;> rfl⟩
theorem gap779388 : (Source.page761.drop 124).take 1 = [10] := by rfl
def cell779389 : Cell := ⟨(Source.page761.drop 125).take 531, 531, by simp only [List.length_take, List.length_drop, Source.size761] <;> rfl⟩
theorem gap779920 : (Source.page761.drop 656).take 1 = [10] := by rfl
def cell779921 : Cell := ⟨(Source.page761.drop 657), 367, by simp only [List.length_take, List.length_drop, Source.size761] <;> rfl⟩
def coveredPage761 : Page := ⟨Source.page761, [cell779264, lf, cell779389, lf, cell779921], by
  have h := (cutBytes_cover [124, 1, 531, 1] Source.page761).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap779388, gap779920] at h
  exact h⟩
def cell780288 : Cell := ⟨Source.page762.take 144, 144, by simp only [List.length_take, List.length_drop, Source.size762] <;> rfl⟩
theorem gap780432 : (Source.page762.drop 144).take 1 = [10] := by rfl
def cell780433 : Cell := ⟨(Source.page762.drop 145).take 517, 517, by simp only [List.length_take, List.length_drop, Source.size762] <;> rfl⟩
theorem gap780950 : (Source.page762.drop 662).take 1 = [10] := by rfl
def cell780951 : Cell := ⟨(Source.page762.drop 663), 361, by simp only [List.length_take, List.length_drop, Source.size762] <;> rfl⟩
def coveredPage762 : Page := ⟨Source.page762, [cell780288, lf, cell780433, lf, cell780951], by
  have h := (cutBytes_cover [144, 1, 517, 1] Source.page762).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap780432, gap780950] at h
  exact h⟩
def cell781312 : Cell := ⟨Source.page763.take 85, 85, by simp only [List.length_take, List.length_drop, Source.size763] <;> rfl⟩
theorem gap781397 : (Source.page763.drop 85).take 1 = [10] := by rfl
def cell781398 : Cell := ⟨(Source.page763.drop 86).take 513, 513, by simp only [List.length_take, List.length_drop, Source.size763] <;> rfl⟩
theorem gap781911 : (Source.page763.drop 599).take 1 = [10] := by rfl
def cell781912 : Cell := ⟨(Source.page763.drop 600), 424, by simp only [List.length_take, List.length_drop, Source.size763] <;> rfl⟩
def coveredPage763 : Page := ⟨Source.page763, [cell781312, lf, cell781398, lf, cell781912], by
  have h := (cutBytes_cover [85, 1, 513, 1] Source.page763).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap781397, gap781911] at h
  exact h⟩
def cell782336 : Cell := ⟨Source.page764.take 22, 22, by simp only [List.length_take, List.length_drop, Source.size764] <;> rfl⟩
theorem gap782358 : (Source.page764.drop 22).take 1 = [10] := by rfl
def cell782359 : Cell := ⟨(Source.page764.drop 23).take 468, 468, by simp only [List.length_take, List.length_drop, Source.size764] <;> rfl⟩
theorem gap782827 : (Source.page764.drop 491).take 1 = [10] := by rfl
def cell782828 : Cell := ⟨(Source.page764.drop 492).take 522, 522, by simp only [List.length_take, List.length_drop, Source.size764] <;> rfl⟩
theorem gap783350 : (Source.page764.drop 1014).take 1 = [10] := by rfl
def cell783351 : Cell := ⟨(Source.page764.drop 1015), 9, by simp only [List.length_take, List.length_drop, Source.size764] <;> rfl⟩
def coveredPage764 : Page := ⟨Source.page764, [cell782336, lf, cell782359, lf, cell782828, lf, cell783351], by
  have h := (cutBytes_cover [22, 1, 468, 1, 522, 1] Source.page764).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap782358, gap782827, gap783350] at h
  exact h⟩
def cell783360 : Cell := ⟨Source.page765.take 544, 544, by simp only [List.length_take, List.length_drop, Source.size765] <;> rfl⟩
theorem gap783904 : (Source.page765.drop 544).take 1 = [10] := by rfl
def cell783905 : Cell := ⟨(Source.page765.drop 545), 479, by simp only [List.length_take, List.length_drop, Source.size765] <;> rfl⟩
def coveredPage765 : Page := ⟨Source.page765, [cell783360, lf, cell783905], by
  have h := (cutBytes_cover [544, 1] Source.page765).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap783904] at h
  exact h⟩
def cell784384 : Cell := ⟨Source.page766.take 65, 65, by simp only [List.length_take, List.length_drop, Source.size766] <;> rfl⟩
theorem gap784449 : (Source.page766.drop 65).take 1 = [10] := by rfl
def cell784450 : Cell := ⟨(Source.page766.drop 66).take 536, 536, by simp only [List.length_take, List.length_drop, Source.size766] <;> rfl⟩
theorem gap784986 : (Source.page766.drop 602).take 1 = [10] := by rfl
def cell784987 : Cell := ⟨(Source.page766.drop 603), 421, by simp only [List.length_take, List.length_drop, Source.size766] <;> rfl⟩
def coveredPage766 : Page := ⟨Source.page766, [cell784384, lf, cell784450, lf, cell784987], by
  have h := (cutBytes_cover [65, 1, 536, 1] Source.page766).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap784449, gap784986] at h
  exact h⟩
def cell785408 : Cell := ⟨Source.page767.take 107, 107, by simp only [List.length_take, List.length_drop, Source.size767] <;> rfl⟩
theorem gap785515 : (Source.page767.drop 107).take 1 = [10] := by rfl
def cell785516 : Cell := ⟨(Source.page767.drop 108).take 423, 423, by simp only [List.length_take, List.length_drop, Source.size767] <;> rfl⟩
theorem gap785939 : (Source.page767.drop 531).take 1 = [10] := by rfl
def cell785940 : Cell := ⟨(Source.page767.drop 532).take 386, 386, by simp only [List.length_take, List.length_drop, Source.size767] <;> rfl⟩
theorem gap786326 : (Source.page767.drop 918).take 1 = [10] := by rfl
def cell786327 : Cell := ⟨(Source.page767.drop 919), 105, by simp only [List.length_take, List.length_drop, Source.size767] <;> rfl⟩
def coveredPage767 : Page := ⟨Source.page767, [cell785408, lf, cell785516, lf, cell785940, lf, cell786327], by
  have h := (cutBytes_cover [107, 1, 423, 1, 386, 1] Source.page767).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap785515, gap785939, gap786326] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
