import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch033

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell540672 : Cell := ⟨Source.page528.take 83, 83, by simp only [List.length_take, List.length_drop, Source.size528] <;> rfl⟩
theorem gap540755 : (Source.page528.drop 83).take 1 = [10] := by rfl
def cell540756 : Cell := ⟨(Source.page528.drop 84).take 513, 513, by simp only [List.length_take, List.length_drop, Source.size528] <;> rfl⟩
theorem gap541269 : (Source.page528.drop 597).take 1 = [10] := by rfl
def cell541270 : Cell := ⟨(Source.page528.drop 598), 426, by simp only [List.length_take, List.length_drop, Source.size528] <;> rfl⟩
def coveredPage528 : Page := ⟨Source.page528, [cell540672, lf, cell540756, lf, cell541270], by
  have h := (cutBytes_cover [83, 1, 513, 1] Source.page528).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap540755, gap541269] at h
  exact h⟩
def cell541696 : Cell := ⟨Source.page529.take 41, 41, by simp only [List.length_take, List.length_drop, Source.size529] <;> rfl⟩
theorem gap541737 : (Source.page529.drop 41).take 1 = [10] := by rfl
def cell541738 : Cell := ⟨(Source.page529.drop 42).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size529] <;> rfl⟩
theorem gap542164 : (Source.page529.drop 468).take 1 = [10] := by rfl
def cell542165 : Cell := ⟨(Source.page529.drop 469).take 517, 517, by simp only [List.length_take, List.length_drop, Source.size529] <;> rfl⟩
theorem gap542682 : (Source.page529.drop 986).take 1 = [10] := by rfl
def cell542683 : Cell := ⟨(Source.page529.drop 987), 37, by simp only [List.length_take, List.length_drop, Source.size529] <;> rfl⟩
def coveredPage529 : Page := ⟨Source.page529, [cell541696, lf, cell541738, lf, cell542165, lf, cell542683], by
  have h := (cutBytes_cover [41, 1, 426, 1, 517, 1] Source.page529).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap541737, gap542164, gap542682] at h
  exact h⟩
def cell542720 : Cell := ⟨Source.page530.take 509, 509, by simp only [List.length_take, List.length_drop, Source.size530] <;> rfl⟩
theorem gap543229 : (Source.page530.drop 509).take 1 = [10] := by rfl
def cell543230 : Cell := ⟨(Source.page530.drop 510).take 473, 473, by simp only [List.length_take, List.length_drop, Source.size530] <;> rfl⟩
theorem gap543703 : (Source.page530.drop 983).take 1 = [10] := by rfl
def cell543704 : Cell := ⟨(Source.page530.drop 984), 40, by simp only [List.length_take, List.length_drop, Source.size530] <;> rfl⟩
def coveredPage530 : Page := ⟨Source.page530, [cell542720, lf, cell543230, lf, cell543704], by
  have h := (cutBytes_cover [509, 1, 473, 1] Source.page530).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap543229, gap543703] at h
  exact h⟩
def cell543744 : Cell := ⟨Source.page531.take 399, 399, by simp only [List.length_take, List.length_drop, Source.size531] <;> rfl⟩
theorem gap544143 : (Source.page531.drop 399).take 1 = [10] := by rfl
def cell544144 : Cell := ⟨(Source.page531.drop 400).take 315, 315, by simp only [List.length_take, List.length_drop, Source.size531] <;> rfl⟩
theorem gap544459 : (Source.page531.drop 715).take 1 = [10] := by rfl
def cell544460 : Cell := ⟨(Source.page531.drop 716), 308, by simp only [List.length_take, List.length_drop, Source.size531] <;> rfl⟩
def coveredPage531 : Page := ⟨Source.page531, [cell543744, lf, cell544144, lf, cell544460], by
  have h := (cutBytes_cover [399, 1, 315, 1] Source.page531).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap544143, gap544459] at h
  exact h⟩
def cell544768 : Cell := ⟨Source.page532.take 112, 112, by simp only [List.length_take, List.length_drop, Source.size532] <;> rfl⟩
theorem gap544880 : (Source.page532.drop 112).take 1 = [10] := by rfl
def cell544881 : Cell := ⟨(Source.page532.drop 113).take 440, 440, by simp only [List.length_take, List.length_drop, Source.size532] <;> rfl⟩
theorem gap545321 : (Source.page532.drop 553).take 1 = [10] := by rfl
def cell545322 : Cell := ⟨(Source.page532.drop 554).take 463, 463, by simp only [List.length_take, List.length_drop, Source.size532] <;> rfl⟩
theorem gap545785 : (Source.page532.drop 1017).take 1 = [10] := by rfl
def cell545786 : Cell := ⟨(Source.page532.drop 1018), 6, by simp only [List.length_take, List.length_drop, Source.size532] <;> rfl⟩
def coveredPage532 : Page := ⟨Source.page532, [cell544768, lf, cell544881, lf, cell545322, lf, cell545786], by
  have h := (cutBytes_cover [112, 1, 440, 1, 463, 1] Source.page532).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap544880, gap545321, gap545785] at h
  exact h⟩
def cell545792 : Cell := ⟨Source.page533.take 540, 540, by simp only [List.length_take, List.length_drop, Source.size533] <;> rfl⟩
theorem gap546332 : (Source.page533.drop 540).take 1 = [10] := by rfl
def cell546333 : Cell := ⟨(Source.page533.drop 541).take 412, 412, by simp only [List.length_take, List.length_drop, Source.size533] <;> rfl⟩
theorem gap546745 : (Source.page533.drop 953).take 1 = [10] := by rfl
def cell546746 : Cell := ⟨(Source.page533.drop 954), 70, by simp only [List.length_take, List.length_drop, Source.size533] <;> rfl⟩
def coveredPage533 : Page := ⟨Source.page533, [cell545792, lf, cell546333, lf, cell546746], by
  have h := (cutBytes_cover [540, 1, 412, 1] Source.page533).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap546332, gap546745] at h
  exact h⟩
def cell546816 : Cell := ⟨Source.page534.take 411, 411, by simp only [List.length_take, List.length_drop, Source.size534] <;> rfl⟩
theorem gap547227 : (Source.page534.drop 411).take 1 = [10] := by rfl
def cell547228 : Cell := ⟨(Source.page534.drop 412).take 417, 417, by simp only [List.length_take, List.length_drop, Source.size534] <;> rfl⟩
theorem gap547645 : (Source.page534.drop 829).take 1 = [10] := by rfl
def cell547646 : Cell := ⟨(Source.page534.drop 830), 194, by simp only [List.length_take, List.length_drop, Source.size534] <;> rfl⟩
def coveredPage534 : Page := ⟨Source.page534, [cell546816, lf, cell547228, lf, cell547646], by
  have h := (cutBytes_cover [411, 1, 417, 1] Source.page534).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap547227, gap547645] at h
  exact h⟩
def cell547840 : Cell := ⟨Source.page535.take 370, 370, by simp only [List.length_take, List.length_drop, Source.size535] <;> rfl⟩
theorem gap548210 : (Source.page535.drop 370).take 1 = [10] := by rfl
def cell548211 : Cell := ⟨(Source.page535.drop 371).take 499, 499, by simp only [List.length_take, List.length_drop, Source.size535] <;> rfl⟩
theorem gap548710 : (Source.page535.drop 870).take 1 = [10] := by rfl
def cell548711 : Cell := ⟨(Source.page535.drop 871), 153, by simp only [List.length_take, List.length_drop, Source.size535] <;> rfl⟩
def coveredPage535 : Page := ⟨Source.page535, [cell547840, lf, cell548211, lf, cell548711], by
  have h := (cutBytes_cover [370, 1, 499, 1] Source.page535).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap548210, gap548710] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
