import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch032

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell532480 : Cell := ⟨Source.page520.take 62, 62, by simp only [List.length_take, List.length_drop, Source.size520] <;> rfl⟩
theorem gap532542 : (Source.page520.drop 62).take 1 = [10] := by rfl
def cell532543 : Cell := ⟨(Source.page520.drop 63).take 362, 362, by simp only [List.length_take, List.length_drop, Source.size520] <;> rfl⟩
theorem gap532905 : (Source.page520.drop 425).take 1 = [10] := by rfl
def cell532906 : Cell := ⟨(Source.page520.drop 426).take 469, 469, by simp only [List.length_take, List.length_drop, Source.size520] <;> rfl⟩
theorem gap533375 : (Source.page520.drop 895).take 1 = [10] := by rfl
def cell533376 : Cell := ⟨(Source.page520.drop 896), 128, by simp only [List.length_take, List.length_drop, Source.size520] <;> rfl⟩
def coveredPage520 : Page := ⟨Source.page520, [cell532480, lf, cell532543, lf, cell532906, lf, cell533376], by
  have h := (cutBytes_cover [62, 1, 362, 1, 469, 1] Source.page520).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap532542, gap532905, gap533375] at h
  exact h⟩
def cell533504 : Cell := ⟨Source.page521.take 391, 391, by simp only [List.length_take, List.length_drop, Source.size521] <;> rfl⟩
theorem gap533895 : (Source.page521.drop 391).take 1 = [10] := by rfl
def cell533896 : Cell := ⟨(Source.page521.drop 392).take 462, 462, by simp only [List.length_take, List.length_drop, Source.size521] <;> rfl⟩
theorem gap534358 : (Source.page521.drop 854).take 1 = [10] := by rfl
def cell534359 : Cell := ⟨(Source.page521.drop 855), 169, by simp only [List.length_take, List.length_drop, Source.size521] <;> rfl⟩
def coveredPage521 : Page := ⟨Source.page521, [cell533504, lf, cell533896, lf, cell534359], by
  have h := (cutBytes_cover [391, 1, 462, 1] Source.page521).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap533895, gap534358] at h
  exact h⟩
def cell534528 : Cell := ⟨Source.page522.take 116, 116, by simp only [List.length_take, List.length_drop, Source.size522] <;> rfl⟩
theorem gap534644 : (Source.page522.drop 116).take 1 = [10] := by rfl
def cell534645 : Cell := ⟨(Source.page522.drop 117).take 435, 435, by simp only [List.length_take, List.length_drop, Source.size522] <;> rfl⟩
theorem gap535080 : (Source.page522.drop 552).take 1 = [10] := by rfl
def cell535081 : Cell := ⟨(Source.page522.drop 553).take 448, 448, by simp only [List.length_take, List.length_drop, Source.size522] <;> rfl⟩
theorem gap535529 : (Source.page522.drop 1001).take 1 = [10] := by rfl
def cell535530 : Cell := ⟨(Source.page522.drop 1002), 22, by simp only [List.length_take, List.length_drop, Source.size522] <;> rfl⟩
def coveredPage522 : Page := ⟨Source.page522, [cell534528, lf, cell534645, lf, cell535081, lf, cell535530], by
  have h := (cutBytes_cover [116, 1, 435, 1, 448, 1] Source.page522).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap534644, gap535080, gap535529] at h
  exact h⟩
def cell535552 : Cell := ⟨Source.page523.take 536, 536, by simp only [List.length_take, List.length_drop, Source.size523] <;> rfl⟩
theorem gap536088 : (Source.page523.drop 536).take 1 = [10] := by rfl
def cell536089 : Cell := ⟨(Source.page523.drop 537), 487, by simp only [List.length_take, List.length_drop, Source.size523] <;> rfl⟩
def coveredPage523 : Page := ⟨Source.page523, [cell535552, lf, cell536089], by
  have h := (cutBytes_cover [536, 1] Source.page523).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap536088] at h
  exact h⟩
def cell536576 : Cell := ⟨Source.page524.take 35, 35, by simp only [List.length_take, List.length_drop, Source.size524] <;> rfl⟩
theorem gap536611 : (Source.page524.drop 35).take 1 = [10] := by rfl
def cell536612 : Cell := ⟨(Source.page524.drop 36).take 494, 494, by simp only [List.length_take, List.length_drop, Source.size524] <;> rfl⟩
theorem gap537106 : (Source.page524.drop 530).take 1 = [10] := by rfl
def cell537107 : Cell := ⟨(Source.page524.drop 531).take 456, 456, by simp only [List.length_take, List.length_drop, Source.size524] <;> rfl⟩
theorem gap537563 : (Source.page524.drop 987).take 1 = [10] := by rfl
def cell537564 : Cell := ⟨(Source.page524.drop 988), 36, by simp only [List.length_take, List.length_drop, Source.size524] <;> rfl⟩
def coveredPage524 : Page := ⟨Source.page524, [cell536576, lf, cell536612, lf, cell537107, lf, cell537564], by
  have h := (cutBytes_cover [35, 1, 494, 1, 456, 1] Source.page524).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap536611, gap537106, gap537563] at h
  exact h⟩
def cell537600 : Cell := ⟨Source.page525.take 431, 431, by simp only [List.length_take, List.length_drop, Source.size525] <;> rfl⟩
theorem gap538031 : (Source.page525.drop 431).take 1 = [10] := by rfl
def cell538032 : Cell := ⟨(Source.page525.drop 432).take 474, 474, by simp only [List.length_take, List.length_drop, Source.size525] <;> rfl⟩
theorem gap538506 : (Source.page525.drop 906).take 1 = [10] := by rfl
def cell538507 : Cell := ⟨(Source.page525.drop 907), 117, by simp only [List.length_take, List.length_drop, Source.size525] <;> rfl⟩
def coveredPage525 : Page := ⟨Source.page525, [cell537600, lf, cell538032, lf, cell538507], by
  have h := (cutBytes_cover [431, 1, 474, 1] Source.page525).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap538031, gap538506] at h
  exact h⟩
def cell538624 : Cell := ⟨Source.page526.take 269, 269, by simp only [List.length_take, List.length_drop, Source.size526] <;> rfl⟩
theorem gap538893 : (Source.page526.drop 269).take 1 = [10] := by rfl
def cell538894 : Cell := ⟨(Source.page526.drop 270).take 556, 556, by simp only [List.length_take, List.length_drop, Source.size526] <;> rfl⟩
theorem gap539450 : (Source.page526.drop 826).take 1 = [10] := by rfl
def cell539451 : Cell := ⟨(Source.page526.drop 827), 197, by simp only [List.length_take, List.length_drop, Source.size526] <;> rfl⟩
def coveredPage526 : Page := ⟨Source.page526, [cell538624, lf, cell538894, lf, cell539451], by
  have h := (cutBytes_cover [269, 1, 556, 1] Source.page526).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap538893, gap539450] at h
  exact h⟩
def cell539648 : Cell := ⟨Source.page527.take 226, 226, by simp only [List.length_take, List.length_drop, Source.size527] <;> rfl⟩
theorem gap539874 : (Source.page527.drop 226).take 1 = [10] := by rfl
def cell539875 : Cell := ⟨(Source.page527.drop 227).take 412, 412, by simp only [List.length_take, List.length_drop, Source.size527] <;> rfl⟩
theorem gap540287 : (Source.page527.drop 639).take 1 = [10] := by rfl
def cell540288 : Cell := ⟨(Source.page527.drop 640), 384, by simp only [List.length_take, List.length_drop, Source.size527] <;> rfl⟩
def coveredPage527 : Page := ⟨Source.page527, [cell539648, lf, cell539875, lf, cell540288], by
  have h := (cutBytes_cover [226, 1, 412, 1] Source.page527).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap539874, gap540287] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
