import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch024

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell401408 : Cell := ⟨Source.page392.take 62, 62, by simp only [List.length_take, List.length_drop, Source.size392] <;> rfl⟩
theorem gap401470 : (Source.page392.drop 62).take 1 = [10] := by rfl
def cell401471 : Cell := ⟨(Source.page392.drop 63).take 511, 511, by simp only [List.length_take, List.length_drop, Source.size392] <;> rfl⟩
theorem gap401982 : (Source.page392.drop 574).take 1 = [10] := by rfl
def cell401983 : Cell := ⟨(Source.page392.drop 575), 449, by simp only [List.length_take, List.length_drop, Source.size392] <;> rfl⟩
def coveredPage392 : Page := ⟨Source.page392, [cell401408, lf, cell401471, lf, cell401983], by
  have h := (cutBytes_cover [62, 1, 511, 1] Source.page392).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap401470, gap401982] at h
  exact h⟩
def cell402432 : Cell := ⟨Source.page393.take 50, 50, by simp only [List.length_take, List.length_drop, Source.size393] <;> rfl⟩
theorem gap402482 : (Source.page393.drop 50).take 1 = [10] := by rfl
def cell402483 : Cell := ⟨(Source.page393.drop 51).take 546, 546, by simp only [List.length_take, List.length_drop, Source.size393] <;> rfl⟩
theorem gap403029 : (Source.page393.drop 597).take 1 = [10] := by rfl
def cell403030 : Cell := ⟨(Source.page393.drop 598), 426, by simp only [List.length_take, List.length_drop, Source.size393] <;> rfl⟩
def coveredPage393 : Page := ⟨Source.page393, [cell402432, lf, cell402483, lf, cell403030], by
  have h := (cutBytes_cover [50, 1, 546, 1] Source.page393).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap402482, gap403029] at h
  exact h⟩
def cell403456 : Cell := ⟨Source.page394.take 73, 73, by simp only [List.length_take, List.length_drop, Source.size394] <;> rfl⟩
theorem gap403529 : (Source.page394.drop 73).take 1 = [10] := by rfl
def cell403530 : Cell := ⟨(Source.page394.drop 74).take 470, 470, by simp only [List.length_take, List.length_drop, Source.size394] <;> rfl⟩
theorem gap404000 : (Source.page394.drop 544).take 1 = [10] := by rfl
def cell404001 : Cell := ⟨(Source.page394.drop 545), 479, by simp only [List.length_take, List.length_drop, Source.size394] <;> rfl⟩
def coveredPage394 : Page := ⟨Source.page394, [cell403456, lf, cell403530, lf, cell404001], by
  have h := (cutBytes_cover [73, 1, 470, 1] Source.page394).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap403529, gap404000] at h
  exact h⟩
def cell404480 : Cell := ⟨Source.page395.take 75, 75, by simp only [List.length_take, List.length_drop, Source.size395] <;> rfl⟩
theorem gap404555 : (Source.page395.drop 75).take 1 = [10] := by rfl
def cell404556 : Cell := ⟨(Source.page395.drop 76).take 654, 654, by simp only [List.length_take, List.length_drop, Source.size395] <;> rfl⟩
theorem gap405210 : (Source.page395.drop 730).take 1 = [10] := by rfl
def cell405211 : Cell := ⟨(Source.page395.drop 731), 293, by simp only [List.length_take, List.length_drop, Source.size395] <;> rfl⟩
def coveredPage395 : Page := ⟨Source.page395, [cell404480, lf, cell404556, lf, cell405211], by
  have h := (cutBytes_cover [75, 1, 654, 1] Source.page395).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap404555, gap405210] at h
  exact h⟩
def cell405504 : Cell := ⟨Source.page396.take 368, 368, by simp only [List.length_take, List.length_drop, Source.size396] <;> rfl⟩
theorem gap405872 : (Source.page396.drop 368).take 1 = [10] := by rfl
def cell405873 : Cell := ⟨(Source.page396.drop 369).take 320, 320, by simp only [List.length_take, List.length_drop, Source.size396] <;> rfl⟩
theorem gap406193 : (Source.page396.drop 689).take 1 = [10] := by rfl
def cell406194 : Cell := ⟨(Source.page396.drop 690), 334, by simp only [List.length_take, List.length_drop, Source.size396] <;> rfl⟩
def coveredPage396 : Page := ⟨Source.page396, [cell405504, lf, cell405873, lf, cell406194], by
  have h := (cutBytes_cover [368, 1, 320, 1] Source.page396).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap405872, gap406193] at h
  exact h⟩
def cell406528 : Cell := ⟨Source.page397.take 79, 79, by simp only [List.length_take, List.length_drop, Source.size397] <;> rfl⟩
theorem gap406607 : (Source.page397.drop 79).take 1 = [10] := by rfl
def cell406608 : Cell := ⟨(Source.page397.drop 80).take 500, 500, by simp only [List.length_take, List.length_drop, Source.size397] <;> rfl⟩
theorem gap407108 : (Source.page397.drop 580).take 1 = [10] := by rfl
def cell407109 : Cell := ⟨(Source.page397.drop 581), 443, by simp only [List.length_take, List.length_drop, Source.size397] <;> rfl⟩
def coveredPage397 : Page := ⟨Source.page397, [cell406528, lf, cell406608, lf, cell407109], by
  have h := (cutBytes_cover [79, 1, 500, 1] Source.page397).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap406607, gap407108] at h
  exact h⟩
def cell407552 : Cell := ⟨Source.page398.take 43, 43, by simp only [List.length_take, List.length_drop, Source.size398] <;> rfl⟩
theorem gap407595 : (Source.page398.drop 43).take 1 = [10] := by rfl
def cell407596 : Cell := ⟨(Source.page398.drop 44).take 567, 567, by simp only [List.length_take, List.length_drop, Source.size398] <;> rfl⟩
theorem gap408163 : (Source.page398.drop 611).take 1 = [10] := by rfl
def cell408164 : Cell := ⟨(Source.page398.drop 612), 412, by simp only [List.length_take, List.length_drop, Source.size398] <;> rfl⟩
def coveredPage398 : Page := ⟨Source.page398, [cell407552, lf, cell407596, lf, cell408164], by
  have h := (cutBytes_cover [43, 1, 567, 1] Source.page398).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap407595, gap408163] at h
  exact h⟩
def cell408576 : Cell := ⟨Source.page399.take 85, 85, by simp only [List.length_take, List.length_drop, Source.size399] <;> rfl⟩
theorem gap408661 : (Source.page399.drop 85).take 1 = [10] := by rfl
def cell408662 : Cell := ⟨(Source.page399.drop 86).take 522, 522, by simp only [List.length_take, List.length_drop, Source.size399] <;> rfl⟩
theorem gap409184 : (Source.page399.drop 608).take 1 = [10] := by rfl
def cell409185 : Cell := ⟨(Source.page399.drop 609), 415, by simp only [List.length_take, List.length_drop, Source.size399] <;> rfl⟩
def coveredPage399 : Page := ⟨Source.page399, [cell408576, lf, cell408662, lf, cell409185], by
  have h := (cutBytes_cover [85, 1, 522, 1] Source.page399).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap408661, gap409184] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
