import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch043

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell712704 : Cell := ⟨Source.page696.take 329, 329, by simp only [List.length_take, List.length_drop, Source.size696] <;> rfl⟩
theorem gap713033 : (Source.page696.drop 329).take 1 = [10] := by rfl
def cell713034 : Cell := ⟨(Source.page696.drop 330).take 511, 511, by simp only [List.length_take, List.length_drop, Source.size696] <;> rfl⟩
theorem gap713545 : (Source.page696.drop 841).take 1 = [10] := by rfl
def cell713546 : Cell := ⟨(Source.page696.drop 842), 182, by simp only [List.length_take, List.length_drop, Source.size696] <;> rfl⟩
def coveredPage696 : Page := ⟨Source.page696, [cell712704, lf, cell713034, lf, cell713546], by
  have h := (cutBytes_cover [329, 1, 511, 1] Source.page696).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap713033, gap713545] at h
  exact h⟩
def cell713728 : Cell := ⟨Source.page697.take 280, 280, by simp only [List.length_take, List.length_drop, Source.size697] <;> rfl⟩
theorem gap714008 : (Source.page697.drop 280).take 1 = [10] := by rfl
def cell714009 : Cell := ⟨(Source.page697.drop 281).take 495, 495, by simp only [List.length_take, List.length_drop, Source.size697] <;> rfl⟩
theorem gap714504 : (Source.page697.drop 776).take 1 = [10] := by rfl
def cell714505 : Cell := ⟨(Source.page697.drop 777), 247, by simp only [List.length_take, List.length_drop, Source.size697] <;> rfl⟩
def coveredPage697 : Page := ⟨Source.page697, [cell713728, lf, cell714009, lf, cell714505], by
  have h := (cutBytes_cover [280, 1, 495, 1] Source.page697).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap714008, gap714504] at h
  exact h⟩
def cell714752 : Cell := ⟨Source.page698.take 167, 167, by simp only [List.length_take, List.length_drop, Source.size698] <;> rfl⟩
theorem gap714919 : (Source.page698.drop 167).take 1 = [10] := by rfl
def cell714920 : Cell := ⟨(Source.page698.drop 168).take 453, 453, by simp only [List.length_take, List.length_drop, Source.size698] <;> rfl⟩
theorem gap715373 : (Source.page698.drop 621).take 1 = [10] := by rfl
def cell715374 : Cell := ⟨(Source.page698.drop 622), 402, by simp only [List.length_take, List.length_drop, Source.size698] <;> rfl⟩
def coveredPage698 : Page := ⟨Source.page698, [cell714752, lf, cell714920, lf, cell715374], by
  have h := (cutBytes_cover [167, 1, 453, 1] Source.page698).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap714919, gap715373] at h
  exact h⟩
def cell715776 : Cell := ⟨Source.page699.take 256, 256, by simp only [List.length_take, List.length_drop, Source.size699] <;> rfl⟩
theorem gap716032 : (Source.page699.drop 256).take 1 = [10] := by rfl
def cell716033 : Cell := ⟨(Source.page699.drop 257).take 289, 289, by simp only [List.length_take, List.length_drop, Source.size699] <;> rfl⟩
theorem gap716322 : (Source.page699.drop 546).take 1 = [10] := by rfl
def cell716323 : Cell := ⟨(Source.page699.drop 547).take 434, 434, by simp only [List.length_take, List.length_drop, Source.size699] <;> rfl⟩
theorem gap716757 : (Source.page699.drop 981).take 1 = [10] := by rfl
def cell716758 : Cell := ⟨(Source.page699.drop 982), 42, by simp only [List.length_take, List.length_drop, Source.size699] <;> rfl⟩
def coveredPage699 : Page := ⟨Source.page699, [cell715776, lf, cell716033, lf, cell716323, lf, cell716758], by
  have h := (cutBytes_cover [256, 1, 289, 1, 434, 1] Source.page699).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap716032, gap716322, gap716757] at h
  exact h⟩
def cell716800 : Cell := ⟨Source.page700.take 496, 496, by simp only [List.length_take, List.length_drop, Source.size700] <;> rfl⟩
theorem gap717296 : (Source.page700.drop 496).take 1 = [10] := by rfl
def cell717297 : Cell := ⟨(Source.page700.drop 497), 527, by simp only [List.length_take, List.length_drop, Source.size700] <;> rfl⟩
def coveredPage700 : Page := ⟨Source.page700, [cell716800, lf, cell717297], by
  have h := (cutBytes_cover [496, 1] Source.page700).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap717296] at h
  exact h⟩
def cell717824 : Cell := ⟨Source.page701.take 128, 128, by simp only [List.length_take, List.length_drop, Source.size701] <;> rfl⟩
theorem gap717952 : (Source.page701.drop 128).take 1 = [10] := by rfl
def cell717953 : Cell := ⟨(Source.page701.drop 129).take 423, 423, by simp only [List.length_take, List.length_drop, Source.size701] <;> rfl⟩
theorem gap718376 : (Source.page701.drop 552).take 1 = [10] := by rfl
def cell718377 : Cell := ⟨(Source.page701.drop 553), 471, by simp only [List.length_take, List.length_drop, Source.size701] <;> rfl⟩
def coveredPage701 : Page := ⟨Source.page701, [cell717824, lf, cell717953, lf, cell718377], by
  have h := (cutBytes_cover [128, 1, 423, 1] Source.page701).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap717952, gap718376] at h
  exact h⟩
def cell718848 : Cell := ⟨Source.page702.take 3, 3, by simp only [List.length_take, List.length_drop, Source.size702] <;> rfl⟩
theorem gap718851 : (Source.page702.drop 3).take 1 = [10] := by rfl
def cell718852 : Cell := ⟨(Source.page702.drop 4).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size702] <;> rfl⟩
theorem gap719359 : (Source.page702.drop 511).take 1 = [10] := by rfl
def cell719360 : Cell := ⟨(Source.page702.drop 512).take 457, 457, by simp only [List.length_take, List.length_drop, Source.size702] <;> rfl⟩
theorem gap719817 : (Source.page702.drop 969).take 1 = [10] := by rfl
def cell719818 : Cell := ⟨(Source.page702.drop 970), 54, by simp only [List.length_take, List.length_drop, Source.size702] <;> rfl⟩
def coveredPage702 : Page := ⟨Source.page702, [cell718848, lf, cell718852, lf, cell719360, lf, cell719818], by
  have h := (cutBytes_cover [3, 1, 507, 1, 457, 1] Source.page702).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap718851, gap719359, gap719817] at h
  exact h⟩
def cell719872 : Cell := ⟨Source.page703.take 306, 306, by simp only [List.length_take, List.length_drop, Source.size703] <;> rfl⟩
theorem gap720178 : (Source.page703.drop 306).take 1 = [10] := by rfl
def cell720179 : Cell := ⟨(Source.page703.drop 307).take 360, 360, by simp only [List.length_take, List.length_drop, Source.size703] <;> rfl⟩
theorem gap720539 : (Source.page703.drop 667).take 1 = [10] := by rfl
def cell720540 : Cell := ⟨(Source.page703.drop 668), 356, by simp only [List.length_take, List.length_drop, Source.size703] <;> rfl⟩
def coveredPage703 : Page := ⟨Source.page703, [cell719872, lf, cell720179, lf, cell720540], by
  have h := (cutBytes_cover [306, 1, 360, 1] Source.page703).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap720178, gap720539] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
