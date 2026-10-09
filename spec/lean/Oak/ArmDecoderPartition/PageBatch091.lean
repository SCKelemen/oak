import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch045

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell745472 : Cell := ⟨Source.page728.take 345, 345, by simp only [List.length_take, List.length_drop, Source.size728] <;> rfl⟩
theorem gap745817 : (Source.page728.drop 345).take 1 = [10] := by rfl
def cell745818 : Cell := ⟨(Source.page728.drop 346).take 540, 540, by simp only [List.length_take, List.length_drop, Source.size728] <;> rfl⟩
theorem gap746358 : (Source.page728.drop 886).take 1 = [10] := by rfl
def cell746359 : Cell := ⟨(Source.page728.drop 887), 137, by simp only [List.length_take, List.length_drop, Source.size728] <;> rfl⟩
def coveredPage728 : Page := ⟨Source.page728, [cell745472, lf, cell745818, lf, cell746359], by
  have h := (cutBytes_cover [345, 1, 540, 1] Source.page728).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap745817, gap746358] at h
  exact h⟩
def cell746496 : Cell := ⟨Source.page729.take 408, 408, by simp only [List.length_take, List.length_drop, Source.size729] <;> rfl⟩
theorem gap746904 : (Source.page729.drop 408).take 1 = [10] := by rfl
def cell746905 : Cell := ⟨(Source.page729.drop 409).take 459, 459, by simp only [List.length_take, List.length_drop, Source.size729] <;> rfl⟩
theorem gap747364 : (Source.page729.drop 868).take 1 = [10] := by rfl
def cell747365 : Cell := ⟨(Source.page729.drop 869), 155, by simp only [List.length_take, List.length_drop, Source.size729] <;> rfl⟩
def coveredPage729 : Page := ⟨Source.page729, [cell746496, lf, cell746905, lf, cell747365], by
  have h := (cutBytes_cover [408, 1, 459, 1] Source.page729).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap746904, gap747364] at h
  exact h⟩
def cell747520 : Cell := ⟨Source.page730.take 420, 420, by simp only [List.length_take, List.length_drop, Source.size730] <;> rfl⟩
theorem gap747940 : (Source.page730.drop 420).take 1 = [10] := by rfl
def cell747941 : Cell := ⟨(Source.page730.drop 421).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size730] <;> rfl⟩
theorem gap748442 : (Source.page730.drop 922).take 1 = [10] := by rfl
def cell748443 : Cell := ⟨(Source.page730.drop 923), 101, by simp only [List.length_take, List.length_drop, Source.size730] <;> rfl⟩
def coveredPage730 : Page := ⟨Source.page730, [cell747520, lf, cell747941, lf, cell748443], by
  have h := (cutBytes_cover [420, 1, 501, 1] Source.page730).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap747940, gap748442] at h
  exact h⟩
def cell748544 : Cell := ⟨Source.page731.take 339, 339, by simp only [List.length_take, List.length_drop, Source.size731] <;> rfl⟩
theorem gap748883 : (Source.page731.drop 339).take 1 = [10] := by rfl
def cell748884 : Cell := ⟨(Source.page731.drop 340).take 289, 289, by simp only [List.length_take, List.length_drop, Source.size731] <;> rfl⟩
theorem gap749173 : (Source.page731.drop 629).take 1 = [10] := by rfl
def cell749174 : Cell := ⟨(Source.page731.drop 630), 394, by simp only [List.length_take, List.length_drop, Source.size731] <;> rfl⟩
def coveredPage731 : Page := ⟨Source.page731, [cell748544, lf, cell748884, lf, cell749174], by
  have h := (cutBytes_cover [339, 1, 289, 1] Source.page731).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap748883, gap749173] at h
  exact h⟩
def cell749568 : Cell := ⟨Source.page732.take 18, 18, by simp only [List.length_take, List.length_drop, Source.size732] <;> rfl⟩
theorem gap749586 : (Source.page732.drop 18).take 1 = [10] := by rfl
def cell749587 : Cell := ⟨(Source.page732.drop 19).take 440, 440, by simp only [List.length_take, List.length_drop, Source.size732] <;> rfl⟩
theorem gap750027 : (Source.page732.drop 459).take 1 = [10] := by rfl
def cell750028 : Cell := ⟨(Source.page732.drop 460).take 546, 546, by simp only [List.length_take, List.length_drop, Source.size732] <;> rfl⟩
theorem gap750574 : (Source.page732.drop 1006).take 1 = [10] := by rfl
def cell750575 : Cell := ⟨(Source.page732.drop 1007), 17, by simp only [List.length_take, List.length_drop, Source.size732] <;> rfl⟩
def coveredPage732 : Page := ⟨Source.page732, [cell749568, lf, cell749587, lf, cell750028, lf, cell750575], by
  have h := (cutBytes_cover [18, 1, 440, 1, 546, 1] Source.page732).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap749586, gap750027, gap750574] at h
  exact h⟩
def cell750592 : Cell := ⟨Source.page733.take 391, 391, by simp only [List.length_take, List.length_drop, Source.size733] <;> rfl⟩
theorem gap750983 : (Source.page733.drop 391).take 1 = [10] := by rfl
def cell750984 : Cell := ⟨(Source.page733.drop 392).take 434, 434, by simp only [List.length_take, List.length_drop, Source.size733] <;> rfl⟩
theorem gap751418 : (Source.page733.drop 826).take 1 = [10] := by rfl
def cell751419 : Cell := ⟨(Source.page733.drop 827), 197, by simp only [List.length_take, List.length_drop, Source.size733] <;> rfl⟩
def coveredPage733 : Page := ⟨Source.page733, [cell750592, lf, cell750984, lf, cell751419], by
  have h := (cutBytes_cover [391, 1, 434, 1] Source.page733).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap750983, gap751418] at h
  exact h⟩
def cell751616 : Cell := ⟨Source.page734.take 235, 235, by simp only [List.length_take, List.length_drop, Source.size734] <;> rfl⟩
theorem gap751851 : (Source.page734.drop 235).take 1 = [10] := by rfl
def cell751852 : Cell := ⟨(Source.page734.drop 236).take 444, 444, by simp only [List.length_take, List.length_drop, Source.size734] <;> rfl⟩
theorem gap752296 : (Source.page734.drop 680).take 1 = [10] := by rfl
def cell752297 : Cell := ⟨(Source.page734.drop 681), 343, by simp only [List.length_take, List.length_drop, Source.size734] <;> rfl⟩
def coveredPage734 : Page := ⟨Source.page734, [cell751616, lf, cell751852, lf, cell752297], by
  have h := (cutBytes_cover [235, 1, 444, 1] Source.page734).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap751851, gap752296] at h
  exact h⟩
def cell752640 : Cell := ⟨Source.page735.take 164, 164, by simp only [List.length_take, List.length_drop, Source.size735] <;> rfl⟩
theorem gap752804 : (Source.page735.drop 164).take 1 = [10] := by rfl
def cell752805 : Cell := ⟨(Source.page735.drop 165).take 540, 540, by simp only [List.length_take, List.length_drop, Source.size735] <;> rfl⟩
theorem gap753345 : (Source.page735.drop 705).take 1 = [10] := by rfl
def cell753346 : Cell := ⟨(Source.page735.drop 706), 318, by simp only [List.length_take, List.length_drop, Source.size735] <;> rfl⟩
def coveredPage735 : Page := ⟨Source.page735, [cell752640, lf, cell752805, lf, cell753346], by
  have h := (cutBytes_cover [164, 1, 540, 1] Source.page735).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap752804, gap753345] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
