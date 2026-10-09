import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch040

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell663552 : Cell := ⟨Source.page648.take 272, 272, by simp only [List.length_take, List.length_drop, Source.size648] <;> rfl⟩
theorem gap663824 : (Source.page648.drop 272).take 1 = [10] := by rfl
def cell663825 : Cell := ⟨(Source.page648.drop 273).take 386, 386, by simp only [List.length_take, List.length_drop, Source.size648] <;> rfl⟩
theorem gap664211 : (Source.page648.drop 659).take 1 = [10] := by rfl
def cell664212 : Cell := ⟨(Source.page648.drop 660), 364, by simp only [List.length_take, List.length_drop, Source.size648] <;> rfl⟩
def coveredPage648 : Page := ⟨Source.page648, [cell663552, lf, cell663825, lf, cell664212], by
  have h := (cutBytes_cover [272, 1, 386, 1] Source.page648).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap663824, gap664211] at h
  exact h⟩
def cell664576 : Cell := ⟨Source.page649.take 104, 104, by simp only [List.length_take, List.length_drop, Source.size649] <;> rfl⟩
theorem gap664680 : (Source.page649.drop 104).take 1 = [10] := by rfl
def cell664681 : Cell := ⟨(Source.page649.drop 105).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size649] <;> rfl⟩
theorem gap665182 : (Source.page649.drop 606).take 1 = [10] := by rfl
def cell665183 : Cell := ⟨(Source.page649.drop 607), 417, by simp only [List.length_take, List.length_drop, Source.size649] <;> rfl⟩
def coveredPage649 : Page := ⟨Source.page649, [cell664576, lf, cell664681, lf, cell665183], by
  have h := (cutBytes_cover [104, 1, 501, 1] Source.page649).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap664680, gap665182] at h
  exact h⟩
def cell665600 : Cell := ⟨Source.page650.take 137, 137, by simp only [List.length_take, List.length_drop, Source.size650] <;> rfl⟩
theorem gap665737 : (Source.page650.drop 137).take 1 = [10] := by rfl
def cell665738 : Cell := ⟨(Source.page650.drop 138).take 296, 296, by simp only [List.length_take, List.length_drop, Source.size650] <;> rfl⟩
theorem gap666034 : (Source.page650.drop 434).take 1 = [10] := by rfl
def cell666035 : Cell := ⟨(Source.page650.drop 435).take 532, 532, by simp only [List.length_take, List.length_drop, Source.size650] <;> rfl⟩
theorem gap666567 : (Source.page650.drop 967).take 1 = [10] := by rfl
def cell666568 : Cell := ⟨(Source.page650.drop 968), 56, by simp only [List.length_take, List.length_drop, Source.size650] <;> rfl⟩
def coveredPage650 : Page := ⟨Source.page650, [cell665600, lf, cell665738, lf, cell666035, lf, cell666568], by
  have h := (cutBytes_cover [137, 1, 296, 1, 532, 1] Source.page650).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap665737, gap666034, gap666567] at h
  exact h⟩
def cell666624 : Cell := ⟨Source.page651.take 418, 418, by simp only [List.length_take, List.length_drop, Source.size651] <;> rfl⟩
theorem gap667042 : (Source.page651.drop 418).take 1 = [10] := by rfl
def cell667043 : Cell := ⟨(Source.page651.drop 419).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size651] <;> rfl⟩
theorem gap667544 : (Source.page651.drop 920).take 1 = [10] := by rfl
def cell667545 : Cell := ⟨(Source.page651.drop 921), 103, by simp only [List.length_take, List.length_drop, Source.size651] <;> rfl⟩
def coveredPage651 : Page := ⟨Source.page651, [cell666624, lf, cell667043, lf, cell667545], by
  have h := (cutBytes_cover [418, 1, 501, 1] Source.page651).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap667042, gap667544] at h
  exact h⟩
def cell667648 : Cell := ⟨Source.page652.take 398, 398, by simp only [List.length_take, List.length_drop, Source.size652] <;> rfl⟩
theorem gap668046 : (Source.page652.drop 398).take 1 = [10] := by rfl
def cell668047 : Cell := ⟨(Source.page652.drop 399).take 466, 466, by simp only [List.length_take, List.length_drop, Source.size652] <;> rfl⟩
theorem gap668513 : (Source.page652.drop 865).take 1 = [10] := by rfl
def cell668514 : Cell := ⟨(Source.page652.drop 866), 158, by simp only [List.length_take, List.length_drop, Source.size652] <;> rfl⟩
def coveredPage652 : Page := ⟨Source.page652, [cell667648, lf, cell668047, lf, cell668514], by
  have h := (cutBytes_cover [398, 1, 466, 1] Source.page652).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap668046, gap668513] at h
  exact h⟩
def cell668672 : Cell := ⟨Source.page653.take 357, 357, by simp only [List.length_take, List.length_drop, Source.size653] <;> rfl⟩
theorem gap669029 : (Source.page653.drop 357).take 1 = [10] := by rfl
def cell669030 : Cell := ⟨(Source.page653.drop 358).take 492, 492, by simp only [List.length_take, List.length_drop, Source.size653] <;> rfl⟩
theorem gap669522 : (Source.page653.drop 850).take 1 = [10] := by rfl
def cell669523 : Cell := ⟨(Source.page653.drop 851), 173, by simp only [List.length_take, List.length_drop, Source.size653] <;> rfl⟩
def coveredPage653 : Page := ⟨Source.page653, [cell668672, lf, cell669030, lf, cell669523], by
  have h := (cutBytes_cover [357, 1, 492, 1] Source.page653).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap669029, gap669522] at h
  exact h⟩
def cell669696 : Cell := ⟨Source.page654.take 235, 235, by simp only [List.length_take, List.length_drop, Source.size654] <;> rfl⟩
theorem gap669931 : (Source.page654.drop 235).take 1 = [10] := by rfl
def cell669932 : Cell := ⟨(Source.page654.drop 236).take 440, 440, by simp only [List.length_take, List.length_drop, Source.size654] <;> rfl⟩
theorem gap670372 : (Source.page654.drop 676).take 1 = [10] := by rfl
def cell670373 : Cell := ⟨(Source.page654.drop 677), 347, by simp only [List.length_take, List.length_drop, Source.size654] <;> rfl⟩
def coveredPage654 : Page := ⟨Source.page654, [cell669696, lf, cell669932, lf, cell670373], by
  have h := (cutBytes_cover [235, 1, 440, 1] Source.page654).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap669931, gap670372] at h
  exact h⟩
def cell670720 : Cell := ⟨Source.page655.take 185, 185, by simp only [List.length_take, List.length_drop, Source.size655] <;> rfl⟩
theorem gap670905 : (Source.page655.drop 185).take 1 = [10] := by rfl
def cell670906 : Cell := ⟨(Source.page655.drop 186).take 548, 548, by simp only [List.length_take, List.length_drop, Source.size655] <;> rfl⟩
theorem gap671454 : (Source.page655.drop 734).take 1 = [10] := by rfl
def cell671455 : Cell := ⟨(Source.page655.drop 735).take 228, 228, by simp only [List.length_take, List.length_drop, Source.size655] <;> rfl⟩
theorem gap671683 : (Source.page655.drop 963).take 1 = [10] := by rfl
def cell671684 : Cell := ⟨(Source.page655.drop 964), 60, by simp only [List.length_take, List.length_drop, Source.size655] <;> rfl⟩
def coveredPage655 : Page := ⟨Source.page655, [cell670720, lf, cell670906, lf, cell671455, lf, cell671684], by
  have h := (cutBytes_cover [185, 1, 548, 1, 228, 1] Source.page655).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap670905, gap671454, gap671683] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
