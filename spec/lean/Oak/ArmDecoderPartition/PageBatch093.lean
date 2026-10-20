import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch046

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell761856 : Cell := ⟨Source.page744.take 139, 139, by simp only [List.length_take, List.length_drop, Source.size744] <;> rfl⟩
theorem gap761995 : (Source.page744.drop 139).take 1 = [10] := by rfl
def cell761996 : Cell := ⟨(Source.page744.drop 140).take 465, 465, by simp only [List.length_take, List.length_drop, Source.size744] <;> rfl⟩
theorem gap762461 : (Source.page744.drop 605).take 1 = [10] := by rfl
def cell762462 : Cell := ⟨(Source.page744.drop 606), 418, by simp only [List.length_take, List.length_drop, Source.size744] <;> rfl⟩
def coveredPage744 : Page := ⟨Source.page744, [cell761856, lf, cell761996, lf, cell762462], by
  have h := (cutBytes_cover [139, 1, 465, 1] Source.page744).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap761995, gap762461] at h
  exact h⟩
def cell762880 : Cell := ⟨Source.page745.take 114, 114, by simp only [List.length_take, List.length_drop, Source.size745] <;> rfl⟩
theorem gap762994 : (Source.page745.drop 114).take 1 = [10] := by rfl
def cell762995 : Cell := ⟨(Source.page745.drop 115).take 397, 397, by simp only [List.length_take, List.length_drop, Source.size745] <;> rfl⟩
theorem gap763392 : (Source.page745.drop 512).take 1 = [10] := by rfl
def cell763393 : Cell := ⟨(Source.page745.drop 513).take 478, 478, by simp only [List.length_take, List.length_drop, Source.size745] <;> rfl⟩
theorem gap763871 : (Source.page745.drop 991).take 1 = [10] := by rfl
def cell763872 : Cell := ⟨(Source.page745.drop 992), 32, by simp only [List.length_take, List.length_drop, Source.size745] <;> rfl⟩
def coveredPage745 : Page := ⟨Source.page745, [cell762880, lf, cell762995, lf, cell763393, lf, cell763872], by
  have h := (cutBytes_cover [114, 1, 397, 1, 478, 1] Source.page745).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap762994, gap763392, gap763871] at h
  exact h⟩
def cell763904 : Cell := ⟨Source.page746.take 407, 407, by simp only [List.length_take, List.length_drop, Source.size746] <;> rfl⟩
theorem gap764311 : (Source.page746.drop 407).take 1 = [10] := by rfl
def cell764312 : Cell := ⟨(Source.page746.drop 408).take 397, 397, by simp only [List.length_take, List.length_drop, Source.size746] <;> rfl⟩
theorem gap764709 : (Source.page746.drop 805).take 1 = [10] := by rfl
def cell764710 : Cell := ⟨(Source.page746.drop 806), 218, by simp only [List.length_take, List.length_drop, Source.size746] <;> rfl⟩
def coveredPage746 : Page := ⟨Source.page746, [cell763904, lf, cell764312, lf, cell764710], by
  have h := (cutBytes_cover [407, 1, 397, 1] Source.page746).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap764311, gap764709] at h
  exact h⟩
def cell764928 : Cell := ⟨Source.page747.take 210, 210, by simp only [List.length_take, List.length_drop, Source.size747] <;> rfl⟩
theorem gap765138 : (Source.page747.drop 210).take 1 = [10] := by rfl
def cell765139 : Cell := ⟨(Source.page747.drop 211).take 427, 427, by simp only [List.length_take, List.length_drop, Source.size747] <;> rfl⟩
theorem gap765566 : (Source.page747.drop 638).take 1 = [10] := by rfl
def cell765567 : Cell := ⟨(Source.page747.drop 639), 385, by simp only [List.length_take, List.length_drop, Source.size747] <;> rfl⟩
def coveredPage747 : Page := ⟨Source.page747, [cell764928, lf, cell765139, lf, cell765567], by
  have h := (cutBytes_cover [210, 1, 427, 1] Source.page747).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap765138, gap765566] at h
  exact h⟩
def cell765952 : Cell := ⟨Source.page748.take 89, 89, by simp only [List.length_take, List.length_drop, Source.size748] <;> rfl⟩
theorem gap766041 : (Source.page748.drop 89).take 1 = [10] := by rfl
def cell766042 : Cell := ⟨(Source.page748.drop 90).take 413, 413, by simp only [List.length_take, List.length_drop, Source.size748] <;> rfl⟩
theorem gap766455 : (Source.page748.drop 503).take 1 = [10] := by rfl
def cell766456 : Cell := ⟨(Source.page748.drop 504).take 426, 426, by simp only [List.length_take, List.length_drop, Source.size748] <;> rfl⟩
theorem gap766882 : (Source.page748.drop 930).take 1 = [10] := by rfl
def cell766883 : Cell := ⟨(Source.page748.drop 931), 93, by simp only [List.length_take, List.length_drop, Source.size748] <;> rfl⟩
def coveredPage748 : Page := ⟨Source.page748, [cell765952, lf, cell766042, lf, cell766456, lf, cell766883], by
  have h := (cutBytes_cover [89, 1, 413, 1, 426, 1] Source.page748).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap766041, gap766455, gap766882] at h
  exact h⟩
def cell766976 : Cell := ⟨Source.page749.take 315, 315, by simp only [List.length_take, List.length_drop, Source.size749] <;> rfl⟩
theorem gap767291 : (Source.page749.drop 315).take 1 = [10] := by rfl
def cell767292 : Cell := ⟨(Source.page749.drop 316).take 517, 517, by simp only [List.length_take, List.length_drop, Source.size749] <;> rfl⟩
theorem gap767809 : (Source.page749.drop 833).take 1 = [10] := by rfl
def cell767810 : Cell := ⟨(Source.page749.drop 834), 190, by simp only [List.length_take, List.length_drop, Source.size749] <;> rfl⟩
def coveredPage749 : Page := ⟨Source.page749, [cell766976, lf, cell767292, lf, cell767810], by
  have h := (cutBytes_cover [315, 1, 517, 1] Source.page749).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap767291, gap767809] at h
  exact h⟩
def cell768000 : Cell := ⟨Source.page750.take 342, 342, by simp only [List.length_take, List.length_drop, Source.size750] <;> rfl⟩
theorem gap768342 : (Source.page750.drop 342).take 1 = [10] := by rfl
def cell768343 : Cell := ⟨(Source.page750.drop 343).take 369, 369, by simp only [List.length_take, List.length_drop, Source.size750] <;> rfl⟩
theorem gap768712 : (Source.page750.drop 712).take 1 = [10] := by rfl
def cell768713 : Cell := ⟨(Source.page750.drop 713), 311, by simp only [List.length_take, List.length_drop, Source.size750] <;> rfl⟩
def coveredPage750 : Page := ⟨Source.page750, [cell768000, lf, cell768343, lf, cell768713], by
  have h := (cutBytes_cover [342, 1, 369, 1] Source.page750).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap768342, gap768712] at h
  exact h⟩
def cell769024 : Cell := ⟨Source.page751.take 225, 225, by simp only [List.length_take, List.length_drop, Source.size751] <;> rfl⟩
theorem gap769249 : (Source.page751.drop 225).take 1 = [10] := by rfl
def cell769250 : Cell := ⟨(Source.page751.drop 226).take 514, 514, by simp only [List.length_take, List.length_drop, Source.size751] <;> rfl⟩
theorem gap769764 : (Source.page751.drop 740).take 1 = [10] := by rfl
def cell769765 : Cell := ⟨(Source.page751.drop 741), 283, by simp only [List.length_take, List.length_drop, Source.size751] <;> rfl⟩
def coveredPage751 : Page := ⟨Source.page751, [cell769024, lf, cell769250, lf, cell769765], by
  have h := (cutBytes_cover [225, 1, 514, 1] Source.page751).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap769249, gap769764] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
