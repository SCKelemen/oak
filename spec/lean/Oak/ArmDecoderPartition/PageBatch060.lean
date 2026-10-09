import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch030

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell491520 : Cell := ⟨Source.page480.take 285, 285, by simp only [List.length_take, List.length_drop, Source.size480] <;> rfl⟩
theorem gap491805 : (Source.page480.drop 285).take 1 = [10] := by rfl
def cell491806 : Cell := ⟨(Source.page480.drop 286).take 513, 513, by simp only [List.length_take, List.length_drop, Source.size480] <;> rfl⟩
theorem gap492319 : (Source.page480.drop 799).take 1 = [10] := by rfl
def cell492320 : Cell := ⟨(Source.page480.drop 800), 224, by simp only [List.length_take, List.length_drop, Source.size480] <;> rfl⟩
def coveredPage480 : Page := ⟨Source.page480, [cell491520, lf, cell491806, lf, cell492320], by
  have h := (cutBytes_cover [285, 1, 513, 1] Source.page480).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap491805, gap492319] at h
  exact h⟩
def cell492544 : Cell := ⟨Source.page481.take 259, 259, by simp only [List.length_take, List.length_drop, Source.size481] <;> rfl⟩
theorem gap492803 : (Source.page481.drop 259).take 1 = [10] := by rfl
def cell492804 : Cell := ⟨(Source.page481.drop 260).take 473, 473, by simp only [List.length_take, List.length_drop, Source.size481] <;> rfl⟩
theorem gap493277 : (Source.page481.drop 733).take 1 = [10] := by rfl
def cell493278 : Cell := ⟨(Source.page481.drop 734), 290, by simp only [List.length_take, List.length_drop, Source.size481] <;> rfl⟩
def coveredPage481 : Page := ⟨Source.page481, [cell492544, lf, cell492804, lf, cell493278], by
  have h := (cutBytes_cover [259, 1, 473, 1] Source.page481).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap492803, gap493277] at h
  exact h⟩
def cell493568 : Cell := ⟨Source.page482.take 107, 107, by simp only [List.length_take, List.length_drop, Source.size482] <;> rfl⟩
theorem gap493675 : (Source.page482.drop 107).take 1 = [10] := by rfl
def cell493676 : Cell := ⟨(Source.page482.drop 108).take 414, 414, by simp only [List.length_take, List.length_drop, Source.size482] <;> rfl⟩
theorem gap494090 : (Source.page482.drop 522).take 1 = [10] := by rfl
def cell494091 : Cell := ⟨(Source.page482.drop 523).take 414, 414, by simp only [List.length_take, List.length_drop, Source.size482] <;> rfl⟩
theorem gap494505 : (Source.page482.drop 937).take 1 = [10] := by rfl
def cell494506 : Cell := ⟨(Source.page482.drop 938), 86, by simp only [List.length_take, List.length_drop, Source.size482] <;> rfl⟩
def coveredPage482 : Page := ⟨Source.page482, [cell493568, lf, cell493676, lf, cell494091, lf, cell494506], by
  have h := (cutBytes_cover [107, 1, 414, 1, 414, 1] Source.page482).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap493675, gap494090, gap494505] at h
  exact h⟩
def cell494592 : Cell := ⟨Source.page483.take 381, 381, by simp only [List.length_take, List.length_drop, Source.size483] <;> rfl⟩
theorem gap494973 : (Source.page483.drop 381).take 1 = [10] := by rfl
def cell494974 : Cell := ⟨(Source.page483.drop 382).take 513, 513, by simp only [List.length_take, List.length_drop, Source.size483] <;> rfl⟩
theorem gap495487 : (Source.page483.drop 895).take 1 = [10] := by rfl
def cell495488 : Cell := ⟨(Source.page483.drop 896), 128, by simp only [List.length_take, List.length_drop, Source.size483] <;> rfl⟩
def coveredPage483 : Page := ⟨Source.page483, [cell494592, lf, cell494974, lf, cell495488], by
  have h := (cutBytes_cover [381, 1, 513, 1] Source.page483).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap494973, gap495487] at h
  exact h⟩
def cell495616 : Cell := ⟨Source.page484.take 418, 418, by simp only [List.length_take, List.length_drop, Source.size484] <;> rfl⟩
theorem gap496034 : (Source.page484.drop 418).take 1 = [10] := by rfl
def cell496035 : Cell := ⟨(Source.page484.drop 419).take 428, 428, by simp only [List.length_take, List.length_drop, Source.size484] <;> rfl⟩
theorem gap496463 : (Source.page484.drop 847).take 1 = [10] := by rfl
def cell496464 : Cell := ⟨(Source.page484.drop 848), 176, by simp only [List.length_take, List.length_drop, Source.size484] <;> rfl⟩
def coveredPage484 : Page := ⟨Source.page484, [cell495616, lf, cell496035, lf, cell496464], by
  have h := (cutBytes_cover [418, 1, 428, 1] Source.page484).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap496034, gap496463] at h
  exact h⟩
def cell496640 : Cell := ⟨Source.page485.take 278, 278, by simp only [List.length_take, List.length_drop, Source.size485] <;> rfl⟩
theorem gap496918 : (Source.page485.drop 278).take 1 = [10] := by rfl
def cell496919 : Cell := ⟨(Source.page485.drop 279).take 407, 407, by simp only [List.length_take, List.length_drop, Source.size485] <;> rfl⟩
theorem gap497326 : (Source.page485.drop 686).take 1 = [10] := by rfl
def cell497327 : Cell := ⟨(Source.page485.drop 687), 337, by simp only [List.length_take, List.length_drop, Source.size485] <;> rfl⟩
def coveredPage485 : Page := ⟨Source.page485, [cell496640, lf, cell496919, lf, cell497327], by
  have h := (cutBytes_cover [278, 1, 407, 1] Source.page485).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap496918, gap497326] at h
  exact h⟩
def cell497664 : Cell := ⟨Source.page486.take 40, 40, by simp only [List.length_take, List.length_drop, Source.size486] <;> rfl⟩
theorem gap497704 : (Source.page486.drop 40).take 1 = [10] := by rfl
def cell497705 : Cell := ⟨(Source.page486.drop 41).take 514, 514, by simp only [List.length_take, List.length_drop, Source.size486] <;> rfl⟩
theorem gap498219 : (Source.page486.drop 555).take 1 = [10] := by rfl
def cell498220 : Cell := ⟨(Source.page486.drop 556), 468, by simp only [List.length_take, List.length_drop, Source.size486] <;> rfl⟩
def coveredPage486 : Page := ⟨Source.page486, [cell497664, lf, cell497705, lf, cell498220], by
  have h := (cutBytes_cover [40, 1, 514, 1] Source.page486).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap497704, gap498219] at h
  exact h⟩
def cell498688 : Cell := ⟨Source.page487.take 27, 27, by simp only [List.length_take, List.length_drop, Source.size487] <;> rfl⟩
theorem gap498715 : (Source.page487.drop 27).take 1 = [10] := by rfl
def cell498716 : Cell := ⟨(Source.page487.drop 28).take 358, 358, by simp only [List.length_take, List.length_drop, Source.size487] <;> rfl⟩
theorem gap499074 : (Source.page487.drop 386).take 1 = [10] := by rfl
def cell499075 : Cell := ⟨(Source.page487.drop 387).take 459, 459, by simp only [List.length_take, List.length_drop, Source.size487] <;> rfl⟩
theorem gap499534 : (Source.page487.drop 846).take 1 = [10] := by rfl
def cell499535 : Cell := ⟨(Source.page487.drop 847), 177, by simp only [List.length_take, List.length_drop, Source.size487] <;> rfl⟩
def coveredPage487 : Page := ⟨Source.page487, [cell498688, lf, cell498716, lf, cell499075, lf, cell499535], by
  have h := (cutBytes_cover [27, 1, 358, 1, 459, 1] Source.page487).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap498715, gap499074, gap499534] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
