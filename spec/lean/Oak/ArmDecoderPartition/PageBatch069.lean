import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch034

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell565248 : Cell := ⟨Source.page552.take 253, 253, by simp only [List.length_take, List.length_drop, Source.size552] <;> rfl⟩
theorem gap565501 : (Source.page552.drop 253).take 1 = [10] := by rfl
def cell565502 : Cell := ⟨(Source.page552.drop 254).take 487, 487, by simp only [List.length_take, List.length_drop, Source.size552] <;> rfl⟩
theorem gap565989 : (Source.page552.drop 741).take 1 = [10] := by rfl
def cell565990 : Cell := ⟨(Source.page552.drop 742), 282, by simp only [List.length_take, List.length_drop, Source.size552] <;> rfl⟩
def coveredPage552 : Page := ⟨Source.page552, [cell565248, lf, cell565502, lf, cell565990], by
  have h := (cutBytes_cover [253, 1, 487, 1] Source.page552).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap565501, gap565989] at h
  exact h⟩
def cell566272 : Cell := ⟨Source.page553.take 171, 171, by simp only [List.length_take, List.length_drop, Source.size553] <;> rfl⟩
theorem gap566443 : (Source.page553.drop 171).take 1 = [10] := by rfl
def cell566444 : Cell := ⟨(Source.page553.drop 172).take 546, 546, by simp only [List.length_take, List.length_drop, Source.size553] <;> rfl⟩
theorem gap566990 : (Source.page553.drop 718).take 1 = [10] := by rfl
def cell566991 : Cell := ⟨(Source.page553.drop 719), 305, by simp only [List.length_take, List.length_drop, Source.size553] <;> rfl⟩
def coveredPage553 : Page := ⟨Source.page553, [cell566272, lf, cell566444, lf, cell566991], by
  have h := (cutBytes_cover [171, 1, 546, 1] Source.page553).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap566443, gap566990] at h
  exact h⟩
def cell567296 : Cell := ⟨Source.page554.take 214, 214, by simp only [List.length_take, List.length_drop, Source.size554] <;> rfl⟩
theorem gap567510 : (Source.page554.drop 214).take 1 = [10] := by rfl
def cell567511 : Cell := ⟨(Source.page554.drop 215).take 313, 313, by simp only [List.length_take, List.length_drop, Source.size554] <;> rfl⟩
theorem gap567824 : (Source.page554.drop 528).take 1 = [10] := by rfl
def cell567825 : Cell := ⟨(Source.page554.drop 529).take 393, 393, by simp only [List.length_take, List.length_drop, Source.size554] <;> rfl⟩
theorem gap568218 : (Source.page554.drop 922).take 1 = [10] := by rfl
def cell568219 : Cell := ⟨(Source.page554.drop 923), 101, by simp only [List.length_take, List.length_drop, Source.size554] <;> rfl⟩
def coveredPage554 : Page := ⟨Source.page554, [cell567296, lf, cell567511, lf, cell567825, lf, cell568219], by
  have h := (cutBytes_cover [214, 1, 313, 1, 393, 1] Source.page554).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap567510, gap567824, gap568218] at h
  exact h⟩
def cell568320 : Cell := ⟨Source.page555.take 396, 396, by simp only [List.length_take, List.length_drop, Source.size555] <;> rfl⟩
theorem gap568716 : (Source.page555.drop 396).take 1 = [10] := by rfl
def cell568717 : Cell := ⟨(Source.page555.drop 397).take 483, 483, by simp only [List.length_take, List.length_drop, Source.size555] <;> rfl⟩
theorem gap569200 : (Source.page555.drop 880).take 1 = [10] := by rfl
def cell569201 : Cell := ⟨(Source.page555.drop 881), 143, by simp only [List.length_take, List.length_drop, Source.size555] <;> rfl⟩
def coveredPage555 : Page := ⟨Source.page555, [cell568320, lf, cell568717, lf, cell569201], by
  have h := (cutBytes_cover [396, 1, 483, 1] Source.page555).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap568716, gap569200] at h
  exact h⟩
def cell569344 : Cell := ⟨Source.page556.take 348, 348, by simp only [List.length_take, List.length_drop, Source.size556] <;> rfl⟩
theorem gap569692 : (Source.page556.drop 348).take 1 = [10] := by rfl
def cell569693 : Cell := ⟨(Source.page556.drop 349).take 369, 369, by simp only [List.length_take, List.length_drop, Source.size556] <;> rfl⟩
theorem gap570062 : (Source.page556.drop 718).take 1 = [10] := by rfl
def cell570063 : Cell := ⟨(Source.page556.drop 719), 305, by simp only [List.length_take, List.length_drop, Source.size556] <;> rfl⟩
def coveredPage556 : Page := ⟨Source.page556, [cell569344, lf, cell569693, lf, cell570063], by
  have h := (cutBytes_cover [348, 1, 369, 1] Source.page556).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap569692, gap570062] at h
  exact h⟩
def cell570368 : Cell := ⟨Source.page557.take 300, 300, by simp only [List.length_take, List.length_drop, Source.size557] <;> rfl⟩
theorem gap570668 : (Source.page557.drop 300).take 1 = [10] := by rfl
def cell570669 : Cell := ⟨(Source.page557.drop 301).take 528, 528, by simp only [List.length_take, List.length_drop, Source.size557] <;> rfl⟩
theorem gap571197 : (Source.page557.drop 829).take 1 = [10] := by rfl
def cell571198 : Cell := ⟨(Source.page557.drop 830), 194, by simp only [List.length_take, List.length_drop, Source.size557] <;> rfl⟩
def coveredPage557 : Page := ⟨Source.page557, [cell570368, lf, cell570669, lf, cell571198], by
  have h := (cutBytes_cover [300, 1, 528, 1] Source.page557).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap570668, gap571197] at h
  exact h⟩
def cell571392 : Cell := ⟨Source.page558.take 229, 229, by simp only [List.length_take, List.length_drop, Source.size558] <;> rfl⟩
theorem gap571621 : (Source.page558.drop 229).take 1 = [10] := by rfl
def cell571622 : Cell := ⟨(Source.page558.drop 230).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size558] <;> rfl⟩
theorem gap572123 : (Source.page558.drop 731).take 1 = [10] := by rfl
def cell572124 : Cell := ⟨(Source.page558.drop 732), 292, by simp only [List.length_take, List.length_drop, Source.size558] <;> rfl⟩
def coveredPage558 : Page := ⟨Source.page558, [cell571392, lf, cell571622, lf, cell572124], by
  have h := (cutBytes_cover [229, 1, 501, 1] Source.page558).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap571621, gap572123] at h
  exact h⟩
def cell572416 : Cell := ⟨Source.page559.take 259, 259, by simp only [List.length_take, List.length_drop, Source.size559] <;> rfl⟩
theorem gap572675 : (Source.page559.drop 259).take 1 = [10] := by rfl
def cell572676 : Cell := ⟨(Source.page559.drop 260).take 554, 554, by simp only [List.length_take, List.length_drop, Source.size559] <;> rfl⟩
theorem gap573230 : (Source.page559.drop 814).take 1 = [10] := by rfl
def cell573231 : Cell := ⟨(Source.page559.drop 815), 209, by simp only [List.length_take, List.length_drop, Source.size559] <;> rfl⟩
def coveredPage559 : Page := ⟨Source.page559, [cell572416, lf, cell572676, lf, cell573231], by
  have h := (cutBytes_cover [259, 1, 554, 1] Source.page559).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap572675, gap573230] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
