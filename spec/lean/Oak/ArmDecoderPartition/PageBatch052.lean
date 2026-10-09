import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch026

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell425984 : Cell := ⟨Source.page416.take 454, 454, by simp only [List.length_take, List.length_drop, Source.size416] <;> rfl⟩
theorem gap426438 : (Source.page416.drop 454).take 1 = [10] := by rfl
def cell426439 : Cell := ⟨(Source.page416.drop 455).take 451, 451, by simp only [List.length_take, List.length_drop, Source.size416] <;> rfl⟩
theorem gap426890 : (Source.page416.drop 906).take 1 = [10] := by rfl
def cell426891 : Cell := ⟨(Source.page416.drop 907), 117, by simp only [List.length_take, List.length_drop, Source.size416] <;> rfl⟩
def coveredPage416 : Page := ⟨Source.page416, [cell425984, lf, cell426439, lf, cell426891], by
  have h := (cutBytes_cover [454, 1, 451, 1] Source.page416).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap426438, gap426890] at h
  exact h⟩
def cell427008 : Cell := ⟨Source.page417.take 240, 240, by simp only [List.length_take, List.length_drop, Source.size417] <;> rfl⟩
theorem gap427248 : (Source.page417.drop 240).take 1 = [10] := by rfl
def cell427249 : Cell := ⟨(Source.page417.drop 241).take 551, 551, by simp only [List.length_take, List.length_drop, Source.size417] <;> rfl⟩
theorem gap427800 : (Source.page417.drop 792).take 1 = [10] := by rfl
def cell427801 : Cell := ⟨(Source.page417.drop 793), 231, by simp only [List.length_take, List.length_drop, Source.size417] <;> rfl⟩
def coveredPage417 : Page := ⟨Source.page417, [cell427008, lf, cell427249, lf, cell427801], by
  have h := (cutBytes_cover [240, 1, 551, 1] Source.page417).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap427248, gap427800] at h
  exact h⟩
def cell428032 : Cell := ⟨Source.page418.take 215, 215, by simp only [List.length_take, List.length_drop, Source.size418] <;> rfl⟩
theorem gap428247 : (Source.page418.drop 215).take 1 = [10] := by rfl
def cell428248 : Cell := ⟨(Source.page418.drop 216).take 424, 424, by simp only [List.length_take, List.length_drop, Source.size418] <;> rfl⟩
theorem gap428672 : (Source.page418.drop 640).take 1 = [10] := by rfl
def cell428673 : Cell := ⟨(Source.page418.drop 641), 383, by simp only [List.length_take, List.length_drop, Source.size418] <;> rfl⟩
def coveredPage418 : Page := ⟨Source.page418, [cell428032, lf, cell428248, lf, cell428673], by
  have h := (cutBytes_cover [215, 1, 424, 1] Source.page418).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap428247, gap428672] at h
  exact h⟩
def cell429056 : Cell := ⟨Source.page419.take 124, 124, by simp only [List.length_take, List.length_drop, Source.size419] <;> rfl⟩
theorem gap429180 : (Source.page419.drop 124).take 1 = [10] := by rfl
def cell429181 : Cell := ⟨(Source.page419.drop 125).take 537, 537, by simp only [List.length_take, List.length_drop, Source.size419] <;> rfl⟩
theorem gap429718 : (Source.page419.drop 662).take 1 = [10] := by rfl
def cell429719 : Cell := ⟨(Source.page419.drop 663), 361, by simp only [List.length_take, List.length_drop, Source.size419] <;> rfl⟩
def coveredPage419 : Page := ⟨Source.page419, [cell429056, lf, cell429181, lf, cell429719], by
  have h := (cutBytes_cover [124, 1, 537, 1] Source.page419).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap429180, gap429718] at h
  exact h⟩
def cell430080 : Cell := ⟨Source.page420.take 86, 86, by simp only [List.length_take, List.length_drop, Source.size420] <;> rfl⟩
theorem gap430166 : (Source.page420.drop 86).take 1 = [10] := by rfl
def cell430167 : Cell := ⟨(Source.page420.drop 87).take 570, 570, by simp only [List.length_take, List.length_drop, Source.size420] <;> rfl⟩
theorem gap430737 : (Source.page420.drop 657).take 1 = [10] := by rfl
def cell430738 : Cell := ⟨(Source.page420.drop 658), 366, by simp only [List.length_take, List.length_drop, Source.size420] <;> rfl⟩
def coveredPage420 : Page := ⟨Source.page420, [cell430080, lf, cell430167, lf, cell430738], by
  have h := (cutBytes_cover [86, 1, 570, 1] Source.page420).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap430166, gap430737] at h
  exact h⟩
def cell431104 : Cell := ⟨Source.page421.take 60, 60, by simp only [List.length_take, List.length_drop, Source.size421] <;> rfl⟩
theorem gap431164 : (Source.page421.drop 60).take 1 = [10] := by rfl
def cell431165 : Cell := ⟨(Source.page421.drop 61).take 484, 484, by simp only [List.length_take, List.length_drop, Source.size421] <;> rfl⟩
theorem gap431649 : (Source.page421.drop 545).take 1 = [10] := by rfl
def cell431650 : Cell := ⟨(Source.page421.drop 546), 478, by simp only [List.length_take, List.length_drop, Source.size421] <;> rfl⟩
def coveredPage421 : Page := ⟨Source.page421, [cell431104, lf, cell431165, lf, cell431650], by
  have h := (cutBytes_cover [60, 1, 484, 1] Source.page421).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap431164, gap431649] at h
  exact h⟩
def cell432128 : Cell := ⟨Source.page422.take 18, 18, by simp only [List.length_take, List.length_drop, Source.size422] <;> rfl⟩
theorem gap432146 : (Source.page422.drop 18).take 1 = [10] := by rfl
def cell432147 : Cell := ⟨(Source.page422.drop 19).take 564, 564, by simp only [List.length_take, List.length_drop, Source.size422] <;> rfl⟩
theorem gap432711 : (Source.page422.drop 583).take 1 = [10] := by rfl
def cell432712 : Cell := ⟨(Source.page422.drop 584).take 412, 412, by simp only [List.length_take, List.length_drop, Source.size422] <;> rfl⟩
theorem gap433124 : (Source.page422.drop 996).take 1 = [10] := by rfl
def cell433125 : Cell := ⟨(Source.page422.drop 997), 27, by simp only [List.length_take, List.length_drop, Source.size422] <;> rfl⟩
def coveredPage422 : Page := ⟨Source.page422, [cell432128, lf, cell432147, lf, cell432712, lf, cell433125], by
  have h := (cutBytes_cover [18, 1, 564, 1, 412, 1] Source.page422).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap432146, gap432711, gap433124] at h
  exact h⟩
def cell433152 : Cell := ⟨Source.page423.take 524, 524, by simp only [List.length_take, List.length_drop, Source.size423] <;> rfl⟩
theorem gap433676 : (Source.page423.drop 524).take 1 = [10] := by rfl
def cell433677 : Cell := ⟨(Source.page423.drop 525), 499, by simp only [List.length_take, List.length_drop, Source.size423] <;> rfl⟩
def coveredPage423 : Page := ⟨Source.page423, [cell433152, lf, cell433677], by
  have h := (cutBytes_cover [524, 1] Source.page423).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap433676] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
