import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch041

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell671744 : Cell := ⟨Source.page656.take 436, 436, by simp only [List.length_take, List.length_drop, Source.size656] <;> rfl⟩
theorem gap672180 : (Source.page656.drop 436).take 1 = [10] := by rfl
def cell672181 : Cell := ⟨(Source.page656.drop 437).take 442, 442, by simp only [List.length_take, List.length_drop, Source.size656] <;> rfl⟩
theorem gap672623 : (Source.page656.drop 879).take 1 = [10] := by rfl
def cell672624 : Cell := ⟨(Source.page656.drop 880), 144, by simp only [List.length_take, List.length_drop, Source.size656] <;> rfl⟩
def coveredPage656 : Page := ⟨Source.page656, [cell671744, lf, cell672181, lf, cell672624], by
  have h := (cutBytes_cover [436, 1, 442, 1] Source.page656).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap672180, gap672623] at h
  exact h⟩
def cell672768 : Cell := ⟨Source.page657.take 269, 269, by simp only [List.length_take, List.length_drop, Source.size657] <;> rfl⟩
theorem gap673037 : (Source.page657.drop 269).take 1 = [10] := by rfl
def cell673038 : Cell := ⟨(Source.page657.drop 270).take 435, 435, by simp only [List.length_take, List.length_drop, Source.size657] <;> rfl⟩
theorem gap673473 : (Source.page657.drop 705).take 1 = [10] := by rfl
def cell673474 : Cell := ⟨(Source.page657.drop 706), 318, by simp only [List.length_take, List.length_drop, Source.size657] <;> rfl⟩
def coveredPage657 : Page := ⟨Source.page657, [cell672768, lf, cell673038, lf, cell673474], by
  have h := (cutBytes_cover [269, 1, 435, 1] Source.page657).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap673037, gap673473] at h
  exact h⟩
def cell673792 : Cell := ⟨Source.page658.take 78, 78, by simp only [List.length_take, List.length_drop, Source.size658] <;> rfl⟩
theorem gap673870 : (Source.page658.drop 78).take 1 = [10] := by rfl
def cell673871 : Cell := ⟨(Source.page658.drop 79).take 337, 337, by simp only [List.length_take, List.length_drop, Source.size658] <;> rfl⟩
theorem gap674208 : (Source.page658.drop 416).take 1 = [10] := by rfl
def cell674209 : Cell := ⟨(Source.page658.drop 417), 607, by simp only [List.length_take, List.length_drop, Source.size658] <;> rfl⟩
def coveredPage658 : Page := ⟨Source.page658, [cell673792, lf, cell673871, lf, cell674209], by
  have h := (cutBytes_cover [78, 1, 337, 1] Source.page658).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap673870, gap674208] at h
  exact h⟩
def cell674816 : Cell := ⟨Source.page659.take 1, 1, by simp only [List.length_take, List.length_drop, Source.size659] <;> rfl⟩
theorem gap674817 : (Source.page659.drop 1).take 1 = [10] := by rfl
def cell674818 : Cell := ⟨(Source.page659.drop 2).take 234, 234, by simp only [List.length_take, List.length_drop, Source.size659] <;> rfl⟩
theorem gap675052 : (Source.page659.drop 236).take 1 = [10] := by rfl
def cell675053 : Cell := ⟨(Source.page659.drop 237).take 402, 402, by simp only [List.length_take, List.length_drop, Source.size659] <;> rfl⟩
theorem gap675455 : (Source.page659.drop 639).take 1 = [10] := by rfl
def cell675456 : Cell := ⟨(Source.page659.drop 640), 384, by simp only [List.length_take, List.length_drop, Source.size659] <;> rfl⟩
def coveredPage659 : Page := ⟨Source.page659, [cell674816, lf, cell674818, lf, cell675053, lf, cell675456], by
  have h := (cutBytes_cover [1, 1, 234, 1, 402, 1] Source.page659).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap674817, gap675052, gap675455] at h
  exact h⟩
def cell675840 : Cell := ⟨Source.page660.take 86, 86, by simp only [List.length_take, List.length_drop, Source.size660] <;> rfl⟩
theorem gap675926 : (Source.page660.drop 86).take 1 = [10] := by rfl
def cell675927 : Cell := ⟨(Source.page660.drop 87).take 448, 448, by simp only [List.length_take, List.length_drop, Source.size660] <;> rfl⟩
theorem gap676375 : (Source.page660.drop 535).take 1 = [10] := by rfl
def cell676376 : Cell := ⟨(Source.page660.drop 536).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size660] <;> rfl⟩
theorem gap676802 : (Source.page660.drop 962).take 1 = [10] := by rfl
def cell676803 : Cell := ⟨(Source.page660.drop 963), 61, by simp only [List.length_take, List.length_drop, Source.size660] <;> rfl⟩
def coveredPage660 : Page := ⟨Source.page660, [cell675840, lf, cell675927, lf, cell676376, lf, cell676803], by
  have h := (cutBytes_cover [86, 1, 448, 1, 426, 1] Source.page660).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap675926, gap676375, gap676802] at h
  exact h⟩
def cell676864 : Cell := ⟨Source.page661.take 140, 140, by simp only [List.length_take, List.length_drop, Source.size661] <;> rfl⟩
theorem gap677004 : (Source.page661.drop 140).take 1 = [10] := by rfl
def cell677005 : Cell := ⟨(Source.page661.drop 141).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size661] <;> rfl⟩
theorem gap677506 : (Source.page661.drop 642).take 1 = [10] := by rfl
def cell677507 : Cell := ⟨(Source.page661.drop 643), 381, by simp only [List.length_take, List.length_drop, Source.size661] <;> rfl⟩
def coveredPage661 : Page := ⟨Source.page661, [cell676864, lf, cell677005, lf, cell677507], by
  have h := (cutBytes_cover [140, 1, 501, 1] Source.page661).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap677004, gap677506] at h
  exact h⟩
def cell677888 : Cell := ⟨Source.page662.take 132, 132, by simp only [List.length_take, List.length_drop, Source.size662] <;> rfl⟩
theorem gap678020 : (Source.page662.drop 132).take 1 = [10] := by rfl
def cell678021 : Cell := ⟨(Source.page662.drop 133).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size662] <;> rfl⟩
theorem gap678492 : (Source.page662.drop 604).take 1 = [10] := by rfl
def cell678493 : Cell := ⟨(Source.page662.drop 605), 419, by simp only [List.length_take, List.length_drop, Source.size662] <;> rfl⟩
def coveredPage662 : Page := ⟨Source.page662, [cell677888, lf, cell678021, lf, cell678493], by
  have h := (cutBytes_cover [132, 1, 471, 1] Source.page662).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap678020, gap678492] at h
  exact h⟩
def cell678912 : Cell := ⟨Source.page663.take 24, 24, by simp only [List.length_take, List.length_drop, Source.size663] <;> rfl⟩
theorem gap678936 : (Source.page663.drop 24).take 1 = [10] := by rfl
def cell678937 : Cell := ⟨(Source.page663.drop 25).take 545, 545, by simp only [List.length_take, List.length_drop, Source.size663] <;> rfl⟩
theorem gap679482 : (Source.page663.drop 570).take 1 = [10] := by rfl
def cell679483 : Cell := ⟨(Source.page663.drop 571), 453, by simp only [List.length_take, List.length_drop, Source.size663] <;> rfl⟩
def coveredPage663 : Page := ⟨Source.page663, [cell678912, lf, cell678937, lf, cell679483], by
  have h := (cutBytes_cover [24, 1, 545, 1] Source.page663).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap678936, gap679482] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
