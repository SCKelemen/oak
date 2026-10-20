import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch044

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell729088 : Cell := ⟨Source.page712.take 147, 147, by simp only [List.length_take, List.length_drop, Source.size712] <;> rfl⟩
theorem gap729235 : (Source.page712.drop 147).take 1 = [10] := by rfl
def cell729236 : Cell := ⟨(Source.page712.drop 148).take 536, 536, by simp only [List.length_take, List.length_drop, Source.size712] <;> rfl⟩
theorem gap729772 : (Source.page712.drop 684).take 1 = [10] := by rfl
def cell729773 : Cell := ⟨(Source.page712.drop 685), 339, by simp only [List.length_take, List.length_drop, Source.size712] <;> rfl⟩
def coveredPage712 : Page := ⟨Source.page712, [cell729088, lf, cell729236, lf, cell729773], by
  have h := (cutBytes_cover [147, 1, 536, 1] Source.page712).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap729235, gap729772] at h
  exact h⟩
def cell730112 : Cell := ⟨Source.page713.take 266, 266, by simp only [List.length_take, List.length_drop, Source.size713] <;> rfl⟩
theorem gap730378 : (Source.page713.drop 266).take 1 = [10] := by rfl
def cell730379 : Cell := ⟨(Source.page713.drop 267).take 497, 497, by simp only [List.length_take, List.length_drop, Source.size713] <;> rfl⟩
theorem gap730876 : (Source.page713.drop 764).take 1 = [10] := by rfl
def cell730877 : Cell := ⟨(Source.page713.drop 765), 259, by simp only [List.length_take, List.length_drop, Source.size713] <;> rfl⟩
def coveredPage713 : Page := ⟨Source.page713, [cell730112, lf, cell730379, lf, cell730877], by
  have h := (cutBytes_cover [266, 1, 497, 1] Source.page713).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap730378, gap730876] at h
  exact h⟩
def cell731136 : Cell := ⟨Source.page714.take 87, 87, by simp only [List.length_take, List.length_drop, Source.size714] <;> rfl⟩
theorem gap731223 : (Source.page714.drop 87).take 1 = [10] := by rfl
def cell731224 : Cell := ⟨(Source.page714.drop 88).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size714] <;> rfl⟩
theorem gap731650 : (Source.page714.drop 514).take 1 = [10] := by rfl
def cell731651 : Cell := ⟨(Source.page714.drop 515), 509, by simp only [List.length_take, List.length_drop, Source.size714] <;> rfl⟩
def coveredPage714 : Page := ⟨Source.page714, [cell731136, lf, cell731224, lf, cell731651], by
  have h := (cutBytes_cover [87, 1, 426, 1] Source.page714).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap731223, gap731650] at h
  exact h⟩
def cell732160 : Cell := ⟨Source.page715.take 4, 4, by simp only [List.length_take, List.length_drop, Source.size715] <;> rfl⟩
theorem gap732164 : (Source.page715.drop 4).take 1 = [10] := by rfl
def cell732165 : Cell := ⟨(Source.page715.drop 5).take 447, 447, by simp only [List.length_take, List.length_drop, Source.size715] <;> rfl⟩
theorem gap732612 : (Source.page715.drop 452).take 1 = [10] := by rfl
def cell732613 : Cell := ⟨(Source.page715.drop 453).take 417, 417, by simp only [List.length_take, List.length_drop, Source.size715] <;> rfl⟩
theorem gap733030 : (Source.page715.drop 870).take 1 = [10] := by rfl
def cell733031 : Cell := ⟨(Source.page715.drop 871), 153, by simp only [List.length_take, List.length_drop, Source.size715] <;> rfl⟩
def coveredPage715 : Page := ⟨Source.page715, [cell732160, lf, cell732165, lf, cell732613, lf, cell733031], by
  have h := (cutBytes_cover [4, 1, 447, 1, 417, 1] Source.page715).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap732164, gap732612, gap733030] at h
  exact h⟩
def cell733184 : Cell := ⟨Source.page716.take 266, 266, by simp only [List.length_take, List.length_drop, Source.size716] <;> rfl⟩
theorem gap733450 : (Source.page716.drop 266).take 1 = [10] := by rfl
def cell733451 : Cell := ⟨(Source.page716.drop 267).take 495, 495, by simp only [List.length_take, List.length_drop, Source.size716] <;> rfl⟩
theorem gap733946 : (Source.page716.drop 762).take 1 = [10] := by rfl
def cell733947 : Cell := ⟨(Source.page716.drop 763), 261, by simp only [List.length_take, List.length_drop, Source.size716] <;> rfl⟩
def coveredPage716 : Page := ⟨Source.page716, [cell733184, lf, cell733451, lf, cell733947], by
  have h := (cutBytes_cover [266, 1, 495, 1] Source.page716).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap733450, gap733946] at h
  exact h⟩
def cell734208 : Cell := ⟨Source.page717.take 271, 271, by simp only [List.length_take, List.length_drop, Source.size717] <;> rfl⟩
theorem gap734479 : (Source.page717.drop 271).take 1 = [10] := by rfl
def cell734480 : Cell := ⟨(Source.page717.drop 272).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size717] <;> rfl⟩
theorem gap734951 : (Source.page717.drop 743).take 1 = [10] := by rfl
def cell734952 : Cell := ⟨(Source.page717.drop 744), 280, by simp only [List.length_take, List.length_drop, Source.size717] <;> rfl⟩
def coveredPage717 : Page := ⟨Source.page717, [cell734208, lf, cell734480, lf, cell734952], by
  have h := (cutBytes_cover [271, 1, 471, 1] Source.page717).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap734479, gap734951] at h
  exact h⟩
def cell735232 : Cell := ⟨Source.page718.take 188, 188, by simp only [List.length_take, List.length_drop, Source.size718] <;> rfl⟩
theorem gap735420 : (Source.page718.drop 188).take 1 = [10] := by rfl
def cell735421 : Cell := ⟨(Source.page718.drop 189).take 512, 512, by simp only [List.length_take, List.length_drop, Source.size718] <;> rfl⟩
theorem gap735933 : (Source.page718.drop 701).take 1 = [10] := by rfl
def cell735934 : Cell := ⟨(Source.page718.drop 702), 322, by simp only [List.length_take, List.length_drop, Source.size718] <;> rfl⟩
def coveredPage718 : Page := ⟨Source.page718, [cell735232, lf, cell735421, lf, cell735934], by
  have h := (cutBytes_cover [188, 1, 512, 1] Source.page718).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap735420, gap735933] at h
  exact h⟩
def cell736256 : Cell := ⟨Source.page719.take 290, 290, by simp only [List.length_take, List.length_drop, Source.size719] <;> rfl⟩
theorem gap736546 : (Source.page719.drop 290).take 1 = [10] := by rfl
def cell736547 : Cell := ⟨(Source.page719.drop 291).take 671, 671, by simp only [List.length_take, List.length_drop, Source.size719] <;> rfl⟩
theorem gap737218 : (Source.page719.drop 962).take 1 = [10] := by rfl
def cell737219 : Cell := ⟨(Source.page719.drop 963), 61, by simp only [List.length_take, List.length_drop, Source.size719] <;> rfl⟩
def coveredPage719 : Page := ⟨Source.page719, [cell736256, lf, cell736547, lf, cell737219], by
  have h := (cutBytes_cover [290, 1, 671, 1] Source.page719).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap736546, gap737218] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
