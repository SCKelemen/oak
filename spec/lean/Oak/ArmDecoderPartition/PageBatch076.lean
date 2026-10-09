import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch038

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell622592 : Cell := ⟨Source.page608.take 142, 142, by simp only [List.length_take, List.length_drop, Source.size608] <;> rfl⟩
theorem gap622734 : (Source.page608.drop 142).take 1 = [10] := by rfl
def cell622735 : Cell := ⟨(Source.page608.drop 143).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size608] <;> rfl⟩
theorem gap623215 : (Source.page608.drop 623).take 1 = [10] := by rfl
def cell623216 : Cell := ⟨(Source.page608.drop 624), 400, by simp only [List.length_take, List.length_drop, Source.size608] <;> rfl⟩
def coveredPage608 : Page := ⟨Source.page608, [cell622592, lf, cell622735, lf, cell623216], by
  have h := (cutBytes_cover [142, 1, 480, 1] Source.page608).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap622734, gap623215] at h
  exact h⟩
def cell623616 : Cell := ⟨Source.page609.take 94, 94, by simp only [List.length_take, List.length_drop, Source.size609] <;> rfl⟩
theorem gap623710 : (Source.page609.drop 94).take 1 = [10] := by rfl
def cell623711 : Cell := ⟨(Source.page609.drop 95).take 451, 451, by simp only [List.length_take, List.length_drop, Source.size609] <;> rfl⟩
theorem gap624162 : (Source.page609.drop 546).take 1 = [10] := by rfl
def cell624163 : Cell := ⟨(Source.page609.drop 547).take 324, 324, by simp only [List.length_take, List.length_drop, Source.size609] <;> rfl⟩
theorem gap624487 : (Source.page609.drop 871).take 1 = [10] := by rfl
def cell624488 : Cell := ⟨(Source.page609.drop 872), 152, by simp only [List.length_take, List.length_drop, Source.size609] <;> rfl⟩
def coveredPage609 : Page := ⟨Source.page609, [cell623616, lf, cell623711, lf, cell624163, lf, cell624488], by
  have h := (cutBytes_cover [94, 1, 451, 1, 324, 1] Source.page609).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap623710, gap624162, gap624487] at h
  exact h⟩
def cell624640 : Cell := ⟨Source.page610.take 415, 415, by simp only [List.length_take, List.length_drop, Source.size610] <;> rfl⟩
theorem gap625055 : (Source.page610.drop 415).take 1 = [10] := by rfl
def cell625056 : Cell := ⟨(Source.page610.drop 416).take 465, 465, by simp only [List.length_take, List.length_drop, Source.size610] <;> rfl⟩
theorem gap625521 : (Source.page610.drop 881).take 1 = [10] := by rfl
def cell625522 : Cell := ⟨(Source.page610.drop 882), 142, by simp only [List.length_take, List.length_drop, Source.size610] <;> rfl⟩
def coveredPage610 : Page := ⟨Source.page610, [cell624640, lf, cell625056, lf, cell625522], by
  have h := (cutBytes_cover [415, 1, 465, 1] Source.page610).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap625055, gap625521] at h
  exact h⟩
def cell625664 : Cell := ⟨Source.page611.take 430, 430, by simp only [List.length_take, List.length_drop, Source.size611] <;> rfl⟩
theorem gap626094 : (Source.page611.drop 430).take 1 = [10] := by rfl
def cell626095 : Cell := ⟨(Source.page611.drop 431).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size611] <;> rfl⟩
theorem gap626602 : (Source.page611.drop 938).take 1 = [10] := by rfl
def cell626603 : Cell := ⟨(Source.page611.drop 939), 85, by simp only [List.length_take, List.length_drop, Source.size611] <;> rfl⟩
def coveredPage611 : Page := ⟨Source.page611, [cell625664, lf, cell626095, lf, cell626603], by
  have h := (cutBytes_cover [430, 1, 507, 1] Source.page611).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap626094, gap626602] at h
  exact h⟩
def cell626688 : Cell := ⟨Source.page612.take 333, 333, by simp only [List.length_take, List.length_drop, Source.size612] <;> rfl⟩
theorem gap627021 : (Source.page612.drop 333).take 1 = [10] := by rfl
def cell627022 : Cell := ⟨(Source.page612.drop 334).take 519, 519, by simp only [List.length_take, List.length_drop, Source.size612] <;> rfl⟩
theorem gap627541 : (Source.page612.drop 853).take 1 = [10] := by rfl
def cell627542 : Cell := ⟨(Source.page612.drop 854), 170, by simp only [List.length_take, List.length_drop, Source.size612] <;> rfl⟩
def coveredPage612 : Page := ⟨Source.page612, [cell626688, lf, cell627022, lf, cell627542], by
  have h := (cutBytes_cover [333, 1, 519, 1] Source.page612).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap627021, gap627541] at h
  exact h⟩
def cell627712 : Cell := ⟨Source.page613.take 242, 242, by simp only [List.length_take, List.length_drop, Source.size613] <;> rfl⟩
theorem gap627954 : (Source.page613.drop 242).take 1 = [10] := by rfl
def cell627955 : Cell := ⟨(Source.page613.drop 243).take 478, 478, by simp only [List.length_take, List.length_drop, Source.size613] <;> rfl⟩
theorem gap628433 : (Source.page613.drop 721).take 1 = [10] := by rfl
def cell628434 : Cell := ⟨(Source.page613.drop 722), 302, by simp only [List.length_take, List.length_drop, Source.size613] <;> rfl⟩
def coveredPage613 : Page := ⟨Source.page613, [cell627712, lf, cell627955, lf, cell628434], by
  have h := (cutBytes_cover [242, 1, 478, 1] Source.page613).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap627954, gap628433] at h
  exact h⟩
def cell628736 : Cell := ⟨Source.page614.take 166, 166, by simp only [List.length_take, List.length_drop, Source.size614] <;> rfl⟩
theorem gap628902 : (Source.page614.drop 166).take 1 = [10] := by rfl
def cell628903 : Cell := ⟨(Source.page614.drop 167).take 562, 562, by simp only [List.length_take, List.length_drop, Source.size614] <;> rfl⟩
theorem gap629465 : (Source.page614.drop 729).take 1 = [10] := by rfl
def cell629466 : Cell := ⟨(Source.page614.drop 730), 294, by simp only [List.length_take, List.length_drop, Source.size614] <;> rfl⟩
def coveredPage614 : Page := ⟨Source.page614, [cell628736, lf, cell628903, lf, cell629466], by
  have h := (cutBytes_cover [166, 1, 562, 1] Source.page614).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap628902, gap629465] at h
  exact h⟩
def cell629760 : Cell := ⟨Source.page615.take 302, 302, by simp only [List.length_take, List.length_drop, Source.size615] <;> rfl⟩
theorem gap630062 : (Source.page615.drop 302).take 1 = [10] := by rfl
def cell630063 : Cell := ⟨(Source.page615.drop 303).take 537, 537, by simp only [List.length_take, List.length_drop, Source.size615] <;> rfl⟩
theorem gap630600 : (Source.page615.drop 840).take 1 = [10] := by rfl
def cell630601 : Cell := ⟨(Source.page615.drop 841), 183, by simp only [List.length_take, List.length_drop, Source.size615] <;> rfl⟩
def coveredPage615 : Page := ⟨Source.page615, [cell629760, lf, cell630063, lf, cell630601], by
  have h := (cutBytes_cover [302, 1, 537, 1] Source.page615).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap630062, gap630600] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
