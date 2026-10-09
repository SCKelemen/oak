import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch027

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell450560 : Cell := ⟨Source.page440.take 40, 40, by simp only [List.length_take, List.length_drop, Source.size440] <;> rfl⟩
theorem gap450600 : (Source.page440.drop 40).take 1 = [10] := by rfl
def cell450601 : Cell := ⟨(Source.page440.drop 41).take 389, 389, by simp only [List.length_take, List.length_drop, Source.size440] <;> rfl⟩
theorem gap450990 : (Source.page440.drop 430).take 1 = [10] := by rfl
def cell450991 : Cell := ⟨(Source.page440.drop 431).take 427, 427, by simp only [List.length_take, List.length_drop, Source.size440] <;> rfl⟩
theorem gap451418 : (Source.page440.drop 858).take 1 = [10] := by rfl
def cell451419 : Cell := ⟨(Source.page440.drop 859), 165, by simp only [List.length_take, List.length_drop, Source.size440] <;> rfl⟩
def coveredPage440 : Page := ⟨Source.page440, [cell450560, lf, cell450601, lf, cell450991, lf, cell451419], by
  have h := (cutBytes_cover [40, 1, 389, 1, 427, 1] Source.page440).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap450600, gap450990, gap451418] at h
  exact h⟩
def cell451584 : Cell := ⟨Source.page441.take 389, 389, by simp only [List.length_take, List.length_drop, Source.size441] <;> rfl⟩
theorem gap451973 : (Source.page441.drop 389).take 1 = [10] := by rfl
def cell451974 : Cell := ⟨(Source.page441.drop 390).take 610, 610, by simp only [List.length_take, List.length_drop, Source.size441] <;> rfl⟩
theorem gap452584 : (Source.page441.drop 1000).take 1 = [10] := by rfl
def cell452585 : Cell := ⟨(Source.page441.drop 1001), 23, by simp only [List.length_take, List.length_drop, Source.size441] <;> rfl⟩
def coveredPage441 : Page := ⟨Source.page441, [cell451584, lf, cell451974, lf, cell452585], by
  have h := (cutBytes_cover [389, 1, 610, 1] Source.page441).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap451973, gap452584] at h
  exact h⟩
def cell452608 : Cell := ⟨Source.page442.take 542, 542, by simp only [List.length_take, List.length_drop, Source.size442] <;> rfl⟩
theorem gap453150 : (Source.page442.drop 542).take 1 = [10] := by rfl
def cell453151 : Cell := ⟨(Source.page442.drop 543), 481, by simp only [List.length_take, List.length_drop, Source.size442] <;> rfl⟩
def coveredPage442 : Page := ⟨Source.page442, [cell452608, lf, cell453151], by
  have h := (cutBytes_cover [542, 1] Source.page442).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap453150] at h
  exact h⟩
def cell453632 : Cell := ⟨Source.page443.take 55, 55, by simp only [List.length_take, List.length_drop, Source.size443] <;> rfl⟩
theorem gap453687 : (Source.page443.drop 55).take 1 = [10] := by rfl
def cell453688 : Cell := ⟨(Source.page443.drop 56).take 495, 495, by simp only [List.length_take, List.length_drop, Source.size443] <;> rfl⟩
theorem gap454183 : (Source.page443.drop 551).take 1 = [10] := by rfl
def cell454184 : Cell := ⟨(Source.page443.drop 552).take 304, 304, by simp only [List.length_take, List.length_drop, Source.size443] <;> rfl⟩
theorem gap454488 : (Source.page443.drop 856).take 1 = [10] := by rfl
def cell454489 : Cell := ⟨(Source.page443.drop 857), 167, by simp only [List.length_take, List.length_drop, Source.size443] <;> rfl⟩
def coveredPage443 : Page := ⟨Source.page443, [cell453632, lf, cell453688, lf, cell454184, lf, cell454489], by
  have h := (cutBytes_cover [55, 1, 495, 1, 304, 1] Source.page443).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap453687, gap454183, gap454488] at h
  exact h⟩
def cell454656 : Cell := ⟨Source.page444.take 305, 305, by simp only [List.length_take, List.length_drop, Source.size444] <;> rfl⟩
theorem gap454961 : (Source.page444.drop 305).take 1 = [10] := by rfl
def cell454962 : Cell := ⟨(Source.page444.drop 306).take 528, 528, by simp only [List.length_take, List.length_drop, Source.size444] <;> rfl⟩
theorem gap455490 : (Source.page444.drop 834).take 1 = [10] := by rfl
def cell455491 : Cell := ⟨(Source.page444.drop 835), 189, by simp only [List.length_take, List.length_drop, Source.size444] <;> rfl⟩
def coveredPage444 : Page := ⟨Source.page444, [cell454656, lf, cell454962, lf, cell455491], by
  have h := (cutBytes_cover [305, 1, 528, 1] Source.page444).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap454961, gap455490] at h
  exact h⟩
def cell455680 : Cell := ⟨Source.page445.take 335, 335, by simp only [List.length_take, List.length_drop, Source.size445] <;> rfl⟩
theorem gap456015 : (Source.page445.drop 335).take 1 = [10] := by rfl
def cell456016 : Cell := ⟨(Source.page445.drop 336).take 451, 451, by simp only [List.length_take, List.length_drop, Source.size445] <;> rfl⟩
theorem gap456467 : (Source.page445.drop 787).take 1 = [10] := by rfl
def cell456468 : Cell := ⟨(Source.page445.drop 788), 236, by simp only [List.length_take, List.length_drop, Source.size445] <;> rfl⟩
def coveredPage445 : Page := ⟨Source.page445, [cell455680, lf, cell456016, lf, cell456468], by
  have h := (cutBytes_cover [335, 1, 451, 1] Source.page445).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap456015, gap456467] at h
  exact h⟩
def cell456704 : Cell := ⟨Source.page446.take 210, 210, by simp only [List.length_take, List.length_drop, Source.size446] <;> rfl⟩
theorem gap456914 : (Source.page446.drop 210).take 1 = [10] := by rfl
def cell456915 : Cell := ⟨(Source.page446.drop 211).take 311, 311, by simp only [List.length_take, List.length_drop, Source.size446] <;> rfl⟩
theorem gap457226 : (Source.page446.drop 522).take 1 = [10] := by rfl
def cell457227 : Cell := ⟨(Source.page446.drop 523).take 413, 413, by simp only [List.length_take, List.length_drop, Source.size446] <;> rfl⟩
theorem gap457640 : (Source.page446.drop 936).take 1 = [10] := by rfl
def cell457641 : Cell := ⟨(Source.page446.drop 937), 87, by simp only [List.length_take, List.length_drop, Source.size446] <;> rfl⟩
def coveredPage446 : Page := ⟨Source.page446, [cell456704, lf, cell456915, lf, cell457227, lf, cell457641], by
  have h := (cutBytes_cover [210, 1, 311, 1, 413, 1] Source.page446).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap456914, gap457226, gap457640] at h
  exact h⟩
def cell457728 : Cell := ⟨Source.page447.take 364, 364, by simp only [List.length_take, List.length_drop, Source.size447] <;> rfl⟩
theorem gap458092 : (Source.page447.drop 364).take 1 = [10] := by rfl
def cell458093 : Cell := ⟨(Source.page447.drop 365).take 536, 536, by simp only [List.length_take, List.length_drop, Source.size447] <;> rfl⟩
theorem gap458629 : (Source.page447.drop 901).take 1 = [10] := by rfl
def cell458630 : Cell := ⟨(Source.page447.drop 902), 122, by simp only [List.length_take, List.length_drop, Source.size447] <;> rfl⟩
def coveredPage447 : Page := ⟨Source.page447, [cell457728, lf, cell458093, lf, cell458630], by
  have h := (cutBytes_cover [364, 1, 536, 1] Source.page447).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap458092, gap458629] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
