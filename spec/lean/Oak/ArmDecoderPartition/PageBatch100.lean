import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch050

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell819200 : Cell := ⟨Source.page800.take 145, 145, by simp only [List.length_take, List.length_drop, Source.size800] <;> rfl⟩
theorem gap819345 : (Source.page800.drop 145).take 1 = [10] := by rfl
def cell819346 : Cell := ⟨(Source.page800.drop 146).take 511, 511, by simp only [List.length_take, List.length_drop, Source.size800] <;> rfl⟩
theorem gap819857 : (Source.page800.drop 657).take 1 = [10] := by rfl
def cell819858 : Cell := ⟨(Source.page800.drop 658), 366, by simp only [List.length_take, List.length_drop, Source.size800] <;> rfl⟩
def coveredPage800 : Page := ⟨Source.page800, [cell819200, lf, cell819346, lf, cell819858], by
  have h := (cutBytes_cover [145, 1, 511, 1] Source.page800).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap819345, gap819857] at h
  exact h⟩
def cell820224 : Cell := ⟨Source.page801.take 166, 166, by simp only [List.length_take, List.length_drop, Source.size801] <;> rfl⟩
theorem gap820390 : (Source.page801.drop 166).take 1 = [10] := by rfl
def cell820391 : Cell := ⟨(Source.page801.drop 167).take 288, 288, by simp only [List.length_take, List.length_drop, Source.size801] <;> rfl⟩
theorem gap820679 : (Source.page801.drop 455).take 1 = [10] := by rfl
def cell820680 : Cell := ⟨(Source.page801.drop 456).take 438, 438, by simp only [List.length_take, List.length_drop, Source.size801] <;> rfl⟩
theorem gap821118 : (Source.page801.drop 894).take 1 = [10] := by rfl
def cell821119 : Cell := ⟨(Source.page801.drop 895), 129, by simp only [List.length_take, List.length_drop, Source.size801] <;> rfl⟩
def coveredPage801 : Page := ⟨Source.page801, [cell820224, lf, cell820391, lf, cell820680, lf, cell821119], by
  have h := (cutBytes_cover [166, 1, 288, 1, 438, 1] Source.page801).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap820390, gap820679, gap821118] at h
  exact h⟩
def cell821248 : Cell := ⟨Source.page802.take 282, 282, by simp only [List.length_take, List.length_drop, Source.size802] <;> rfl⟩
theorem gap821530 : (Source.page802.drop 282).take 1 = [10] := by rfl
def cell821531 : Cell := ⟨(Source.page802.drop 283).take 547, 547, by simp only [List.length_take, List.length_drop, Source.size802] <;> rfl⟩
theorem gap822078 : (Source.page802.drop 830).take 1 = [10] := by rfl
def cell822079 : Cell := ⟨(Source.page802.drop 831), 193, by simp only [List.length_take, List.length_drop, Source.size802] <;> rfl⟩
def coveredPage802 : Page := ⟨Source.page802, [cell821248, lf, cell821531, lf, cell822079], by
  have h := (cutBytes_cover [282, 1, 547, 1] Source.page802).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap821530, gap822078] at h
  exact h⟩
def cell822272 : Cell := ⟨Source.page803.take 369, 369, by simp only [List.length_take, List.length_drop, Source.size803] <;> rfl⟩
theorem gap822641 : (Source.page803.drop 369).take 1 = [10] := by rfl
def cell822642 : Cell := ⟨(Source.page803.drop 370).take 498, 498, by simp only [List.length_take, List.length_drop, Source.size803] <;> rfl⟩
theorem gap823140 : (Source.page803.drop 868).take 1 = [10] := by rfl
def cell823141 : Cell := ⟨(Source.page803.drop 869), 155, by simp only [List.length_take, List.length_drop, Source.size803] <;> rfl⟩
def coveredPage803 : Page := ⟨Source.page803, [cell822272, lf, cell822642, lf, cell823141], by
  have h := (cutBytes_cover [369, 1, 498, 1] Source.page803).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap822641, gap823140] at h
  exact h⟩
def cell823296 : Cell := ⟨Source.page804.take 286, 286, by simp only [List.length_take, List.length_drop, Source.size804] <;> rfl⟩
theorem gap823582 : (Source.page804.drop 286).take 1 = [10] := by rfl
def cell823583 : Cell := ⟨(Source.page804.drop 287).take 462, 462, by simp only [List.length_take, List.length_drop, Source.size804] <;> rfl⟩
theorem gap824045 : (Source.page804.drop 749).take 1 = [10] := by rfl
def cell824046 : Cell := ⟨(Source.page804.drop 750), 274, by simp only [List.length_take, List.length_drop, Source.size804] <;> rfl⟩
def coveredPage804 : Page := ⟨Source.page804, [cell823296, lf, cell823583, lf, cell824046], by
  have h := (cutBytes_cover [286, 1, 462, 1] Source.page804).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap823582, gap824045] at h
  exact h⟩
def cell824320 : Cell := ⟨Source.page805.take 206, 206, by simp only [List.length_take, List.length_drop, Source.size805] <;> rfl⟩
theorem gap824526 : (Source.page805.drop 206).take 1 = [10] := by rfl
def cell824527 : Cell := ⟨(Source.page805.drop 207).take 564, 564, by simp only [List.length_take, List.length_drop, Source.size805] <;> rfl⟩
theorem gap825091 : (Source.page805.drop 771).take 1 = [10] := by rfl
def cell825092 : Cell := ⟨(Source.page805.drop 772), 252, by simp only [List.length_take, List.length_drop, Source.size805] <;> rfl⟩
def coveredPage805 : Page := ⟨Source.page805, [cell824320, lf, cell824527, lf, cell825092], by
  have h := (cutBytes_cover [206, 1, 564, 1] Source.page805).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap824526, gap825091] at h
  exact h⟩
def cell825344 : Cell := ⟨Source.page806.take 171, 171, by simp only [List.length_take, List.length_drop, Source.size806] <;> rfl⟩
theorem gap825515 : (Source.page806.drop 171).take 1 = [10] := by rfl
def cell825516 : Cell := ⟨(Source.page806.drop 172).take 572, 572, by simp only [List.length_take, List.length_drop, Source.size806] <;> rfl⟩
theorem gap826088 : (Source.page806.drop 744).take 1 = [10] := by rfl
def cell826089 : Cell := ⟨(Source.page806.drop 745), 279, by simp only [List.length_take, List.length_drop, Source.size806] <;> rfl⟩
def coveredPage806 : Page := ⟨Source.page806, [cell825344, lf, cell825516, lf, cell826089], by
  have h := (cutBytes_cover [171, 1, 572, 1] Source.page806).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap825515, gap826088] at h
  exact h⟩
def cell826368 : Cell := ⟨Source.page807.take 172, 172, by simp only [List.length_take, List.length_drop, Source.size807] <;> rfl⟩
theorem gap826540 : (Source.page807.drop 172).take 1 = [10] := by rfl
def cell826541 : Cell := ⟨(Source.page807.drop 173).take 458, 458, by simp only [List.length_take, List.length_drop, Source.size807] <;> rfl⟩
theorem gap826999 : (Source.page807.drop 631).take 1 = [10] := by rfl
def cell827000 : Cell := ⟨(Source.page807.drop 632), 392, by simp only [List.length_take, List.length_drop, Source.size807] <;> rfl⟩
def coveredPage807 : Page := ⟨Source.page807, [cell826368, lf, cell826541, lf, cell827000], by
  have h := (cutBytes_cover [172, 1, 458, 1] Source.page807).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap826540, gap826999] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
