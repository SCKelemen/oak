import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch035

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell573440 : Cell := ⟨Source.page560.take 160, 160, by simp only [List.length_take, List.length_drop, Source.size560] <;> rfl⟩
theorem gap573600 : (Source.page560.drop 160).take 1 = [10] := by rfl
def cell573601 : Cell := ⟨(Source.page560.drop 161).take 451, 451, by simp only [List.length_take, List.length_drop, Source.size560] <;> rfl⟩
theorem gap574052 : (Source.page560.drop 612).take 1 = [10] := by rfl
def cell574053 : Cell := ⟨(Source.page560.drop 613).take 337, 337, by simp only [List.length_take, List.length_drop, Source.size560] <;> rfl⟩
theorem gap574390 : (Source.page560.drop 950).take 1 = [10] := by rfl
def cell574391 : Cell := ⟨(Source.page560.drop 951), 73, by simp only [List.length_take, List.length_drop, Source.size560] <;> rfl⟩
def coveredPage560 : Page := ⟨Source.page560, [cell573440, lf, cell573601, lf, cell574053, lf, cell574391], by
  have h := (cutBytes_cover [160, 1, 451, 1, 337, 1] Source.page560).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap573600, gap574052, gap574390] at h
  exact h⟩
def cell574464 : Cell := ⟨Source.page561.take 344, 344, by simp only [List.length_take, List.length_drop, Source.size561] <;> rfl⟩
theorem gap574808 : (Source.page561.drop 344).take 1 = [10] := by rfl
def cell574809 : Cell := ⟨(Source.page561.drop 345).take 516, 516, by simp only [List.length_take, List.length_drop, Source.size561] <;> rfl⟩
theorem gap575325 : (Source.page561.drop 861).take 1 = [10] := by rfl
def cell575326 : Cell := ⟨(Source.page561.drop 862), 162, by simp only [List.length_take, List.length_drop, Source.size561] <;> rfl⟩
def coveredPage561 : Page := ⟨Source.page561, [cell574464, lf, cell574809, lf, cell575326], by
  have h := (cutBytes_cover [344, 1, 516, 1] Source.page561).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap574808, gap575325] at h
  exact h⟩
def cell575488 : Cell := ⟨Source.page562.take 300, 300, by simp only [List.length_take, List.length_drop, Source.size562] <;> rfl⟩
theorem gap575788 : (Source.page562.drop 300).take 1 = [10] := by rfl
def cell575789 : Cell := ⟨(Source.page562.drop 301).take 436, 436, by simp only [List.length_take, List.length_drop, Source.size562] <;> rfl⟩
theorem gap576225 : (Source.page562.drop 737).take 1 = [10] := by rfl
def cell576226 : Cell := ⟨(Source.page562.drop 738), 286, by simp only [List.length_take, List.length_drop, Source.size562] <;> rfl⟩
def coveredPage562 : Page := ⟨Source.page562, [cell575488, lf, cell575789, lf, cell576226], by
  have h := (cutBytes_cover [300, 1, 436, 1] Source.page562).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap575788, gap576225] at h
  exact h⟩
def cell576512 : Cell := ⟨Source.page563.take 236, 236, by simp only [List.length_take, List.length_drop, Source.size563] <;> rfl⟩
theorem gap576748 : (Source.page563.drop 236).take 1 = [10] := by rfl
def cell576749 : Cell := ⟨(Source.page563.drop 237).take 448, 448, by simp only [List.length_take, List.length_drop, Source.size563] <;> rfl⟩
theorem gap577197 : (Source.page563.drop 685).take 1 = [10] := by rfl
def cell577198 : Cell := ⟨(Source.page563.drop 686), 338, by simp only [List.length_take, List.length_drop, Source.size563] <;> rfl⟩
def coveredPage563 : Page := ⟨Source.page563, [cell576512, lf, cell576749, lf, cell577198], by
  have h := (cutBytes_cover [236, 1, 448, 1] Source.page563).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap576748, gap577197] at h
  exact h⟩
def cell577536 : Cell := ⟨Source.page564.take 111, 111, by simp only [List.length_take, List.length_drop, Source.size564] <;> rfl⟩
theorem gap577647 : (Source.page564.drop 111).take 1 = [10] := by rfl
def cell577648 : Cell := ⟨(Source.page564.drop 112).take 435, 435, by simp only [List.length_take, List.length_drop, Source.size564] <;> rfl⟩
theorem gap578083 : (Source.page564.drop 547).take 1 = [10] := by rfl
def cell578084 : Cell := ⟨(Source.page564.drop 548).take 423, 423, by simp only [List.length_take, List.length_drop, Source.size564] <;> rfl⟩
theorem gap578507 : (Source.page564.drop 971).take 1 = [10] := by rfl
def cell578508 : Cell := ⟨(Source.page564.drop 972), 52, by simp only [List.length_take, List.length_drop, Source.size564] <;> rfl⟩
def coveredPage564 : Page := ⟨Source.page564, [cell577536, lf, cell577648, lf, cell578084, lf, cell578508], by
  have h := (cutBytes_cover [111, 1, 435, 1, 423, 1] Source.page564).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap577647, gap578083, gap578507] at h
  exact h⟩
def cell578560 : Cell := ⟨Source.page565.take 320, 320, by simp only [List.length_take, List.length_drop, Source.size565] <;> rfl⟩
theorem gap578880 : (Source.page565.drop 320).take 1 = [10] := by rfl
def cell578881 : Cell := ⟨(Source.page565.drop 321).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size565] <;> rfl⟩
theorem gap579388 : (Source.page565.drop 828).take 1 = [10] := by rfl
def cell579389 : Cell := ⟨(Source.page565.drop 829), 195, by simp only [List.length_take, List.length_drop, Source.size565] <;> rfl⟩
def coveredPage565 : Page := ⟨Source.page565, [cell578560, lf, cell578881, lf, cell579389], by
  have h := (cutBytes_cover [320, 1, 507, 1] Source.page565).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap578880, gap579388] at h
  exact h⟩
def cell579584 : Cell := ⟨Source.page566.take 306, 306, by simp only [List.length_take, List.length_drop, Source.size566] <;> rfl⟩
theorem gap579890 : (Source.page566.drop 306).take 1 = [10] := by rfl
def cell579891 : Cell := ⟨(Source.page566.drop 307).take 572, 572, by simp only [List.length_take, List.length_drop, Source.size566] <;> rfl⟩
theorem gap580463 : (Source.page566.drop 879).take 1 = [10] := by rfl
def cell580464 : Cell := ⟨(Source.page566.drop 880), 144, by simp only [List.length_take, List.length_drop, Source.size566] <;> rfl⟩
def coveredPage566 : Page := ⟨Source.page566, [cell579584, lf, cell579891, lf, cell580464], by
  have h := (cutBytes_cover [306, 1, 572, 1] Source.page566).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap579890, gap580463] at h
  exact h⟩
def cell580608 : Cell := ⟨Source.page567.take 318, 318, by simp only [List.length_take, List.length_drop, Source.size567] <;> rfl⟩
theorem gap580926 : (Source.page567.drop 318).take 1 = [10] := by rfl
def cell580927 : Cell := ⟨(Source.page567.drop 319).take 613, 613, by simp only [List.length_take, List.length_drop, Source.size567] <;> rfl⟩
theorem gap581540 : (Source.page567.drop 932).take 1 = [10] := by rfl
def cell581541 : Cell := ⟨(Source.page567.drop 933), 91, by simp only [List.length_take, List.length_drop, Source.size567] <;> rfl⟩
def coveredPage567 : Page := ⟨Source.page567, [cell580608, lf, cell580927, lf, cell581541], by
  have h := (cutBytes_cover [318, 1, 613, 1] Source.page567).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap580926, gap581540] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
