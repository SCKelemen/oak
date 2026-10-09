import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch028

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell458752 : Cell := ⟨Source.page448.take 408, 408, by simp only [List.length_take, List.length_drop, Source.size448] <;> rfl⟩
theorem gap459160 : (Source.page448.drop 408).take 1 = [10] := by rfl
def cell459161 : Cell := ⟨(Source.page448.drop 409).take 500, 500, by simp only [List.length_take, List.length_drop, Source.size448] <;> rfl⟩
theorem gap459661 : (Source.page448.drop 909).take 1 = [10] := by rfl
def cell459662 : Cell := ⟨(Source.page448.drop 910), 114, by simp only [List.length_take, List.length_drop, Source.size448] <;> rfl⟩
def coveredPage448 : Page := ⟨Source.page448, [cell458752, lf, cell459161, lf, cell459662], by
  have h := (cutBytes_cover [408, 1, 500, 1] Source.page448).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap459160, gap459661] at h
  exact h⟩
def cell459776 : Cell := ⟨Source.page449.take 435, 435, by simp only [List.length_take, List.length_drop, Source.size449] <;> rfl⟩
theorem gap460211 : (Source.page449.drop 435).take 1 = [10] := by rfl
def cell460212 : Cell := ⟨(Source.page449.drop 436).take 419, 419, by simp only [List.length_take, List.length_drop, Source.size449] <;> rfl⟩
theorem gap460631 : (Source.page449.drop 855).take 1 = [10] := by rfl
def cell460632 : Cell := ⟨(Source.page449.drop 856), 168, by simp only [List.length_take, List.length_drop, Source.size449] <;> rfl⟩
def coveredPage449 : Page := ⟨Source.page449, [cell459776, lf, cell460212, lf, cell460632], by
  have h := (cutBytes_cover [435, 1, 419, 1] Source.page449).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap460211, gap460631] at h
  exact h⟩
def cell460800 : Cell := ⟨Source.page450.take 255, 255, by simp only [List.length_take, List.length_drop, Source.size450] <;> rfl⟩
theorem gap461055 : (Source.page450.drop 255).take 1 = [10] := by rfl
def cell461056 : Cell := ⟨(Source.page450.drop 256).take 478, 478, by simp only [List.length_take, List.length_drop, Source.size450] <;> rfl⟩
theorem gap461534 : (Source.page450.drop 734).take 1 = [10] := by rfl
def cell461535 : Cell := ⟨(Source.page450.drop 735), 289, by simp only [List.length_take, List.length_drop, Source.size450] <;> rfl⟩
def coveredPage450 : Page := ⟨Source.page450, [cell460800, lf, cell461056, lf, cell461535], by
  have h := (cutBytes_cover [255, 1, 478, 1] Source.page450).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap461055, gap461534] at h
  exact h⟩
def cell461824 : Cell := ⟨Source.page451.take 176, 176, by simp only [List.length_take, List.length_drop, Source.size451] <;> rfl⟩
theorem gap462000 : (Source.page451.drop 176).take 1 = [10] := by rfl
def cell462001 : Cell := ⟨(Source.page451.drop 177).take 477, 477, by simp only [List.length_take, List.length_drop, Source.size451] <;> rfl⟩
theorem gap462478 : (Source.page451.drop 654).take 1 = [10] := by rfl
def cell462479 : Cell := ⟨(Source.page451.drop 655), 369, by simp only [List.length_take, List.length_drop, Source.size451] <;> rfl⟩
def coveredPage451 : Page := ⟨Source.page451, [cell461824, lf, cell462001, lf, cell462479], by
  have h := (cutBytes_cover [176, 1, 477, 1] Source.page451).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap462000, gap462478] at h
  exact h⟩
def cell462848 : Cell := ⟨Source.page452.take 174, 174, by simp only [List.length_take, List.length_drop, Source.size452] <;> rfl⟩
theorem gap463022 : (Source.page452.drop 174).take 1 = [10] := by rfl
def cell463023 : Cell := ⟨(Source.page452.drop 175).take 393, 393, by simp only [List.length_take, List.length_drop, Source.size452] <;> rfl⟩
theorem gap463416 : (Source.page452.drop 568).take 1 = [10] := by rfl
def cell463417 : Cell := ⟨(Source.page452.drop 569), 455, by simp only [List.length_take, List.length_drop, Source.size452] <;> rfl⟩
def coveredPage452 : Page := ⟨Source.page452, [cell462848, lf, cell463023, lf, cell463417], by
  have h := (cutBytes_cover [174, 1, 393, 1] Source.page452).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap463022, gap463416] at h
  exact h⟩
def cell463872 : Cell := ⟨Source.page453.take 33, 33, by simp only [List.length_take, List.length_drop, Source.size453] <;> rfl⟩
theorem gap463905 : (Source.page453.drop 33).take 1 = [10] := by rfl
def cell463906 : Cell := ⟨(Source.page453.drop 34).take 448, 448, by simp only [List.length_take, List.length_drop, Source.size453] <;> rfl⟩
theorem gap464354 : (Source.page453.drop 482).take 1 = [10] := by rfl
def cell464355 : Cell := ⟨(Source.page453.drop 483).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size453] <;> rfl⟩
theorem gap464862 : (Source.page453.drop 990).take 1 = [10] := by rfl
def cell464863 : Cell := ⟨(Source.page453.drop 991), 33, by simp only [List.length_take, List.length_drop, Source.size453] <;> rfl⟩
def coveredPage453 : Page := ⟨Source.page453, [cell463872, lf, cell463906, lf, cell464355, lf, cell464863], by
  have h := (cutBytes_cover [33, 1, 448, 1, 507, 1] Source.page453).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap463905, gap464354, gap464862] at h
  exact h⟩
def cell464896 : Cell := ⟨Source.page454.take 431, 431, by simp only [List.length_take, List.length_drop, Source.size454] <;> rfl⟩
theorem gap465327 : (Source.page454.drop 431).take 1 = [10] := by rfl
def cell465328 : Cell := ⟨(Source.page454.drop 432).take 388, 388, by simp only [List.length_take, List.length_drop, Source.size454] <;> rfl⟩
theorem gap465716 : (Source.page454.drop 820).take 1 = [10] := by rfl
def cell465717 : Cell := ⟨(Source.page454.drop 821), 203, by simp only [List.length_take, List.length_drop, Source.size454] <;> rfl⟩
def coveredPage454 : Page := ⟨Source.page454, [cell464896, lf, cell465328, lf, cell465717], by
  have h := (cutBytes_cover [431, 1, 388, 1] Source.page454).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap465327, gap465716] at h
  exact h⟩
def cell465920 : Cell := ⟨Source.page455.take 194, 194, by simp only [List.length_take, List.length_drop, Source.size455] <;> rfl⟩
theorem gap466114 : (Source.page455.drop 194).take 1 = [10] := by rfl
def cell466115 : Cell := ⟨(Source.page455.drop 195).take 472, 472, by simp only [List.length_take, List.length_drop, Source.size455] <;> rfl⟩
theorem gap466587 : (Source.page455.drop 667).take 1 = [10] := by rfl
def cell466588 : Cell := ⟨(Source.page455.drop 668), 356, by simp only [List.length_take, List.length_drop, Source.size455] <;> rfl⟩
def coveredPage455 : Page := ⟨Source.page455, [cell465920, lf, cell466115, lf, cell466588], by
  have h := (cutBytes_cover [194, 1, 472, 1] Source.page455).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap466114, gap466587] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
