import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch027

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell442368 : Cell := ⟨Source.page432.take 59, 59, by simp only [List.length_take, List.length_drop, Source.size432] <;> rfl⟩
theorem gap442427 : (Source.page432.drop 59).take 1 = [10] := by rfl
def cell442428 : Cell := ⟨(Source.page432.drop 60).take 304, 304, by simp only [List.length_take, List.length_drop, Source.size432] <;> rfl⟩
theorem gap442732 : (Source.page432.drop 364).take 1 = [10] := by rfl
def cell442733 : Cell := ⟨(Source.page432.drop 365).take 400, 400, by simp only [List.length_take, List.length_drop, Source.size432] <;> rfl⟩
theorem gap443133 : (Source.page432.drop 765).take 1 = [10] := by rfl
def cell443134 : Cell := ⟨(Source.page432.drop 766), 258, by simp only [List.length_take, List.length_drop, Source.size432] <;> rfl⟩
def coveredPage432 : Page := ⟨Source.page432, [cell442368, lf, cell442428, lf, cell442733, lf, cell443134], by
  have h := (cutBytes_cover [59, 1, 304, 1, 400, 1] Source.page432).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap442427, gap442732, gap443133] at h
  exact h⟩
def cell443392 : Cell := ⟨Source.page433.take 256, 256, by simp only [List.length_take, List.length_drop, Source.size433] <;> rfl⟩
theorem gap443648 : (Source.page433.drop 256).take 1 = [10] := by rfl
def cell443649 : Cell := ⟨(Source.page433.drop 257).take 419, 419, by simp only [List.length_take, List.length_drop, Source.size433] <;> rfl⟩
theorem gap444068 : (Source.page433.drop 676).take 1 = [10] := by rfl
def cell444069 : Cell := ⟨(Source.page433.drop 677), 347, by simp only [List.length_take, List.length_drop, Source.size433] <;> rfl⟩
def coveredPage433 : Page := ⟨Source.page433, [cell443392, lf, cell443649, lf, cell444069], by
  have h := (cutBytes_cover [256, 1, 419, 1] Source.page433).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap443648, gap444068] at h
  exact h⟩
def cell444416 : Cell := ⟨Source.page434.take 166, 166, by simp only [List.length_take, List.length_drop, Source.size434] <;> rfl⟩
theorem gap444582 : (Source.page434.drop 166).take 1 = [10] := by rfl
def cell444583 : Cell := ⟨(Source.page434.drop 167).take 420, 420, by simp only [List.length_take, List.length_drop, Source.size434] <;> rfl⟩
theorem gap445003 : (Source.page434.drop 587).take 1 = [10] := by rfl
def cell445004 : Cell := ⟨(Source.page434.drop 588).take 398, 398, by simp only [List.length_take, List.length_drop, Source.size434] <;> rfl⟩
theorem gap445402 : (Source.page434.drop 986).take 1 = [10] := by rfl
def cell445403 : Cell := ⟨(Source.page434.drop 987), 37, by simp only [List.length_take, List.length_drop, Source.size434] <;> rfl⟩
def coveredPage434 : Page := ⟨Source.page434, [cell444416, lf, cell444583, lf, cell445004, lf, cell445403], by
  have h := (cutBytes_cover [166, 1, 420, 1, 398, 1] Source.page434).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap444582, gap445003, gap445402] at h
  exact h⟩
def cell445440 : Cell := ⟨Source.page435.take 421, 421, by simp only [List.length_take, List.length_drop, Source.size435] <;> rfl⟩
theorem gap445861 : (Source.page435.drop 421).take 1 = [10] := by rfl
def cell445862 : Cell := ⟨(Source.page435.drop 422).take 377, 377, by simp only [List.length_take, List.length_drop, Source.size435] <;> rfl⟩
theorem gap446239 : (Source.page435.drop 799).take 1 = [10] := by rfl
def cell446240 : Cell := ⟨(Source.page435.drop 800), 224, by simp only [List.length_take, List.length_drop, Source.size435] <;> rfl⟩
def coveredPage435 : Page := ⟨Source.page435, [cell445440, lf, cell445862, lf, cell446240], by
  have h := (cutBytes_cover [421, 1, 377, 1] Source.page435).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap445861, gap446239] at h
  exact h⟩
def cell446464 : Cell := ⟨Source.page436.take 280, 280, by simp only [List.length_take, List.length_drop, Source.size436] <;> rfl⟩
theorem gap446744 : (Source.page436.drop 280).take 1 = [10] := by rfl
def cell446745 : Cell := ⟨(Source.page436.drop 281).take 450, 450, by simp only [List.length_take, List.length_drop, Source.size436] <;> rfl⟩
theorem gap447195 : (Source.page436.drop 731).take 1 = [10] := by rfl
def cell447196 : Cell := ⟨(Source.page436.drop 732), 292, by simp only [List.length_take, List.length_drop, Source.size436] <;> rfl⟩
def coveredPage436 : Page := ⟨Source.page436, [cell446464, lf, cell446745, lf, cell447196], by
  have h := (cutBytes_cover [280, 1, 450, 1] Source.page436).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap446744, gap447195] at h
  exact h⟩
def cell447488 : Cell := ⟨Source.page437.take 174, 174, by simp only [List.length_take, List.length_drop, Source.size437] <;> rfl⟩
theorem gap447662 : (Source.page437.drop 174).take 1 = [10] := by rfl
def cell447663 : Cell := ⟨(Source.page437.drop 175).take 486, 486, by simp only [List.length_take, List.length_drop, Source.size437] <;> rfl⟩
theorem gap448149 : (Source.page437.drop 661).take 1 = [10] := by rfl
def cell448150 : Cell := ⟨(Source.page437.drop 662), 362, by simp only [List.length_take, List.length_drop, Source.size437] <;> rfl⟩
def coveredPage437 : Page := ⟨Source.page437, [cell447488, lf, cell447663, lf, cell448150], by
  have h := (cutBytes_cover [174, 1, 486, 1] Source.page437).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap447662, gap448149] at h
  exact h⟩
def cell448512 : Cell := ⟨Source.page438.take 186, 186, by simp only [List.length_take, List.length_drop, Source.size438] <;> rfl⟩
theorem gap448698 : (Source.page438.drop 186).take 1 = [10] := by rfl
def cell448699 : Cell := ⟨(Source.page438.drop 187).take 446, 446, by simp only [List.length_take, List.length_drop, Source.size438] <;> rfl⟩
theorem gap449145 : (Source.page438.drop 633).take 1 = [10] := by rfl
def cell449146 : Cell := ⟨(Source.page438.drop 634), 390, by simp only [List.length_take, List.length_drop, Source.size438] <;> rfl⟩
def coveredPage438 : Page := ⟨Source.page438, [cell448512, lf, cell448699, lf, cell449146], by
  have h := (cutBytes_cover [186, 1, 446, 1] Source.page438).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap448698, gap449145] at h
  exact h⟩
def cell449536 : Cell := ⟨Source.page439.take 34, 34, by simp only [List.length_take, List.length_drop, Source.size439] <;> rfl⟩
theorem gap449570 : (Source.page439.drop 34).take 1 = [10] := by rfl
def cell449571 : Cell := ⟨(Source.page439.drop 35).take 517, 517, by simp only [List.length_take, List.length_drop, Source.size439] <;> rfl⟩
theorem gap450088 : (Source.page439.drop 552).take 1 = [10] := by rfl
def cell450089 : Cell := ⟨(Source.page439.drop 553), 471, by simp only [List.length_take, List.length_drop, Source.size439] <;> rfl⟩
def coveredPage439 : Page := ⟨Source.page439, [cell449536, lf, cell449571, lf, cell450089], by
  have h := (cutBytes_cover [34, 1, 517, 1] Source.page439).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap449570, gap450088] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
