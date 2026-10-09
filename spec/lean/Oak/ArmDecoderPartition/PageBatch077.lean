import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch038

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell630784 : Cell := ⟨Source.page616.take 263, 263, by simp only [List.length_take, List.length_drop, Source.size616] <;> rfl⟩
theorem gap631047 : (Source.page616.drop 263).take 1 = [10] := by rfl
def cell631048 : Cell := ⟨(Source.page616.drop 264).take 512, 512, by simp only [List.length_take, List.length_drop, Source.size616] <;> rfl⟩
theorem gap631560 : (Source.page616.drop 776).take 1 = [10] := by rfl
def cell631561 : Cell := ⟨(Source.page616.drop 777), 247, by simp only [List.length_take, List.length_drop, Source.size616] <;> rfl⟩
def coveredPage616 : Page := ⟨Source.page616, [cell630784, lf, cell631048, lf, cell631561], by
  have h := (cutBytes_cover [263, 1, 512, 1] Source.page616).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap631047, gap631560] at h
  exact h⟩
def cell631808 : Cell := ⟨Source.page617.take 298, 298, by simp only [List.length_take, List.length_drop, Source.size617] <;> rfl⟩
theorem gap632106 : (Source.page617.drop 298).take 1 = [10] := by rfl
def cell632107 : Cell := ⟨(Source.page617.drop 299).take 496, 496, by simp only [List.length_take, List.length_drop, Source.size617] <;> rfl⟩
theorem gap632603 : (Source.page617.drop 795).take 1 = [10] := by rfl
def cell632604 : Cell := ⟨(Source.page617.drop 796), 228, by simp only [List.length_take, List.length_drop, Source.size617] <;> rfl⟩
def coveredPage617 : Page := ⟨Source.page617, [cell631808, lf, cell632107, lf, cell632604], by
  have h := (cutBytes_cover [298, 1, 496, 1] Source.page617).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap632106, gap632603] at h
  exact h⟩
def cell632832 : Cell := ⟨Source.page618.take 268, 268, by simp only [List.length_take, List.length_drop, Source.size618] <;> rfl⟩
theorem gap633100 : (Source.page618.drop 268).take 1 = [10] := by rfl
def cell633101 : Cell := ⟨(Source.page618.drop 269).take 463, 463, by simp only [List.length_take, List.length_drop, Source.size618] <;> rfl⟩
theorem gap633564 : (Source.page618.drop 732).take 1 = [10] := by rfl
def cell633565 : Cell := ⟨(Source.page618.drop 733), 291, by simp only [List.length_take, List.length_drop, Source.size618] <;> rfl⟩
def coveredPage618 : Page := ⟨Source.page618, [cell632832, lf, cell633101, lf, cell633565], by
  have h := (cutBytes_cover [268, 1, 463, 1] Source.page618).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap633100, gap633564] at h
  exact h⟩
def cell633856 : Cell := ⟨Source.page619.take 183, 183, by simp only [List.length_take, List.length_drop, Source.size619] <;> rfl⟩
theorem gap634039 : (Source.page619.drop 183).take 1 = [10] := by rfl
def cell634040 : Cell := ⟨(Source.page619.drop 184).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size619] <;> rfl⟩
theorem gap634511 : (Source.page619.drop 655).take 1 = [10] := by rfl
def cell634512 : Cell := ⟨(Source.page619.drop 656), 368, by simp only [List.length_take, List.length_drop, Source.size619] <;> rfl⟩
def coveredPage619 : Page := ⟨Source.page619, [cell633856, lf, cell634040, lf, cell634512], by
  have h := (cutBytes_cover [183, 1, 471, 1] Source.page619).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap634039, gap634511] at h
  exact h⟩
def cell634880 : Cell := ⟨Source.page620.take 151, 151, by simp only [List.length_take, List.length_drop, Source.size620] <;> rfl⟩
theorem gap635031 : (Source.page620.drop 151).take 1 = [10] := by rfl
def cell635032 : Cell := ⟨(Source.page620.drop 152).take 488, 488, by simp only [List.length_take, List.length_drop, Source.size620] <;> rfl⟩
theorem gap635520 : (Source.page620.drop 640).take 1 = [10] := by rfl
def cell635521 : Cell := ⟨(Source.page620.drop 641), 383, by simp only [List.length_take, List.length_drop, Source.size620] <;> rfl⟩
def coveredPage620 : Page := ⟨Source.page620, [cell634880, lf, cell635032, lf, cell635521], by
  have h := (cutBytes_cover [151, 1, 488, 1] Source.page620).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap635031, gap635520] at h
  exact h⟩
def cell635904 : Cell := ⟨Source.page621.take 120, 120, by simp only [List.length_take, List.length_drop, Source.size621] <;> rfl⟩
theorem gap636024 : (Source.page621.drop 120).take 1 = [10] := by rfl
def cell636025 : Cell := ⟨(Source.page621.drop 121).take 440, 440, by simp only [List.length_take, List.length_drop, Source.size621] <;> rfl⟩
theorem gap636465 : (Source.page621.drop 561).take 1 = [10] := by rfl
def cell636466 : Cell := ⟨(Source.page621.drop 562).take 418, 418, by simp only [List.length_take, List.length_drop, Source.size621] <;> rfl⟩
theorem gap636884 : (Source.page621.drop 980).take 1 = [10] := by rfl
def cell636885 : Cell := ⟨(Source.page621.drop 981), 43, by simp only [List.length_take, List.length_drop, Source.size621] <;> rfl⟩
def coveredPage621 : Page := ⟨Source.page621, [cell635904, lf, cell636025, lf, cell636466, lf, cell636885], by
  have h := (cutBytes_cover [120, 1, 440, 1, 418, 1] Source.page621).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap636024, gap636465, gap636884] at h
  exact h⟩
def cell636928 : Cell := ⟨Source.page622.take 497, 497, by simp only [List.length_take, List.length_drop, Source.size622] <;> rfl⟩
theorem gap637425 : (Source.page622.drop 497).take 1 = [10] := by rfl
def cell637426 : Cell := ⟨(Source.page622.drop 498).take 439, 439, by simp only [List.length_take, List.length_drop, Source.size622] <;> rfl⟩
theorem gap637865 : (Source.page622.drop 937).take 1 = [10] := by rfl
def cell637866 : Cell := ⟨(Source.page622.drop 938), 86, by simp only [List.length_take, List.length_drop, Source.size622] <;> rfl⟩
def coveredPage622 : Page := ⟨Source.page622, [cell636928, lf, cell637426, lf, cell637866], by
  have h := (cutBytes_cover [497, 1, 439, 1] Source.page622).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap637425, gap637865] at h
  exact h⟩
def cell637952 : Cell := ⟨Source.page623.take 207, 207, by simp only [List.length_take, List.length_drop, Source.size623] <;> rfl⟩
theorem gap638159 : (Source.page623.drop 207).take 1 = [10] := by rfl
def cell638160 : Cell := ⟨(Source.page623.drop 208).take 483, 483, by simp only [List.length_take, List.length_drop, Source.size623] <;> rfl⟩
theorem gap638643 : (Source.page623.drop 691).take 1 = [10] := by rfl
def cell638644 : Cell := ⟨(Source.page623.drop 692), 332, by simp only [List.length_take, List.length_drop, Source.size623] <;> rfl⟩
def coveredPage623 : Page := ⟨Source.page623, [cell637952, lf, cell638160, lf, cell638644], by
  have h := (cutBytes_cover [207, 1, 483, 1] Source.page623).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap638159, gap638643] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
