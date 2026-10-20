import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch039

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell638976 : Cell := ⟨Source.page624.take 81, 81, by simp only [List.length_take, List.length_drop, Source.size624] <;> rfl⟩
theorem gap639057 : (Source.page624.drop 81).take 1 = [10] := by rfl
def cell639058 : Cell := ⟨(Source.page624.drop 82).take 507, 507, by simp only [List.length_take, List.length_drop, Source.size624] <;> rfl⟩
theorem gap639565 : (Source.page624.drop 589).take 1 = [10] := by rfl
def cell639566 : Cell := ⟨(Source.page624.drop 590), 434, by simp only [List.length_take, List.length_drop, Source.size624] <;> rfl⟩
def coveredPage624 : Page := ⟨Source.page624, [cell638976, lf, cell639058, lf, cell639566], by
  have h := (cutBytes_cover [81, 1, 507, 1] Source.page624).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap639057, gap639565] at h
  exact h⟩
def cell640000 : Cell := ⟨Source.page625.take 43, 43, by simp only [List.length_take, List.length_drop, Source.size625] <;> rfl⟩
theorem gap640043 : (Source.page625.drop 43).take 1 = [10] := by rfl
def cell640044 : Cell := ⟨(Source.page625.drop 44).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size625] <;> rfl⟩
theorem gap640545 : (Source.page625.drop 545).take 1 = [10] := by rfl
def cell640546 : Cell := ⟨(Source.page625.drop 546), 478, by simp only [List.length_take, List.length_drop, Source.size625] <;> rfl⟩
def coveredPage625 : Page := ⟨Source.page625, [cell640000, lf, cell640044, lf, cell640546], by
  have h := (cutBytes_cover [43, 1, 501, 1] Source.page625).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap640043, gap640545] at h
  exact h⟩
def cell641024 : Cell := ⟨Source.page626.take 132, 132, by simp only [List.length_take, List.length_drop, Source.size626] <;> rfl⟩
theorem gap641156 : (Source.page626.drop 132).take 1 = [10] := by rfl
def cell641157 : Cell := ⟨(Source.page626.drop 133).take 531, 531, by simp only [List.length_take, List.length_drop, Source.size626] <;> rfl⟩
theorem gap641688 : (Source.page626.drop 664).take 1 = [10] := by rfl
def cell641689 : Cell := ⟨(Source.page626.drop 665), 359, by simp only [List.length_take, List.length_drop, Source.size626] <;> rfl⟩
def coveredPage626 : Page := ⟨Source.page626, [cell641024, lf, cell641157, lf, cell641689], by
  have h := (cutBytes_cover [132, 1, 531, 1] Source.page626).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap641156, gap641688] at h
  exact h⟩
def cell642048 : Cell := ⟨Source.page627.take 246, 246, by simp only [List.length_take, List.length_drop, Source.size627] <;> rfl⟩
theorem gap642294 : (Source.page627.drop 246).take 1 = [10] := by rfl
def cell642295 : Cell := ⟨(Source.page627.drop 247).take 462, 462, by simp only [List.length_take, List.length_drop, Source.size627] <;> rfl⟩
theorem gap642757 : (Source.page627.drop 709).take 1 = [10] := by rfl
def cell642758 : Cell := ⟨(Source.page627.drop 710), 314, by simp only [List.length_take, List.length_drop, Source.size627] <;> rfl⟩
def coveredPage627 : Page := ⟨Source.page627, [cell642048, lf, cell642295, lf, cell642758], by
  have h := (cutBytes_cover [246, 1, 462, 1] Source.page627).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap642294, gap642757] at h
  exact h⟩
def cell643072 : Cell := ⟨Source.page628.take 307, 307, by simp only [List.length_take, List.length_drop, Source.size628] <;> rfl⟩
theorem gap643379 : (Source.page628.drop 307).take 1 = [10] := by rfl
def cell643380 : Cell := ⟨(Source.page628.drop 308).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size628] <;> rfl⟩
theorem gap643881 : (Source.page628.drop 809).take 1 = [10] := by rfl
def cell643882 : Cell := ⟨(Source.page628.drop 810), 214, by simp only [List.length_take, List.length_drop, Source.size628] <;> rfl⟩
def coveredPage628 : Page := ⟨Source.page628, [cell643072, lf, cell643380, lf, cell643882], by
  have h := (cutBytes_cover [307, 1, 501, 1] Source.page628).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap643379, gap643881] at h
  exact h⟩
def cell644096 : Cell := ⟨Source.page629.take 307, 307, by simp only [List.length_take, List.length_drop, Source.size629] <;> rfl⟩
theorem gap644403 : (Source.page629.drop 307).take 1 = [10] := by rfl
def cell644404 : Cell := ⟨(Source.page629.drop 308).take 496, 496, by simp only [List.length_take, List.length_drop, Source.size629] <;> rfl⟩
theorem gap644900 : (Source.page629.drop 804).take 1 = [10] := by rfl
def cell644901 : Cell := ⟨(Source.page629.drop 805), 219, by simp only [List.length_take, List.length_drop, Source.size629] <;> rfl⟩
def coveredPage629 : Page := ⟨Source.page629, [cell644096, lf, cell644404, lf, cell644901], by
  have h := (cutBytes_cover [307, 1, 496, 1] Source.page629).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap644403, gap644900] at h
  exact h⟩
def cell645120 : Cell := ⟨Source.page630.take 270, 270, by simp only [List.length_take, List.length_drop, Source.size630] <;> rfl⟩
theorem gap645390 : (Source.page630.drop 270).take 1 = [10] := by rfl
def cell645391 : Cell := ⟨(Source.page630.drop 271).take 370, 370, by simp only [List.length_take, List.length_drop, Source.size630] <;> rfl⟩
theorem gap645761 : (Source.page630.drop 641).take 1 = [10] := by rfl
def cell645762 : Cell := ⟨(Source.page630.drop 642), 382, by simp only [List.length_take, List.length_drop, Source.size630] <;> rfl⟩
def coveredPage630 : Page := ⟨Source.page630, [cell645120, lf, cell645391, lf, cell645762], by
  have h := (cutBytes_cover [270, 1, 370, 1] Source.page630).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap645390, gap645761] at h
  exact h⟩
def cell646144 : Cell := ⟨Source.page631.take 119, 119, by simp only [List.length_take, List.length_drop, Source.size631] <;> rfl⟩
theorem gap646263 : (Source.page631.drop 119).take 1 = [10] := by rfl
def cell646264 : Cell := ⟨(Source.page631.drop 120).take 483, 483, by simp only [List.length_take, List.length_drop, Source.size631] <;> rfl⟩
theorem gap646747 : (Source.page631.drop 603).take 1 = [10] := by rfl
def cell646748 : Cell := ⟨(Source.page631.drop 604).take 334, 334, by simp only [List.length_take, List.length_drop, Source.size631] <;> rfl⟩
theorem gap647082 : (Source.page631.drop 938).take 1 = [10] := by rfl
def cell647083 : Cell := ⟨(Source.page631.drop 939), 85, by simp only [List.length_take, List.length_drop, Source.size631] <;> rfl⟩
def coveredPage631 : Page := ⟨Source.page631, [cell646144, lf, cell646264, lf, cell646748, lf, cell647083], by
  have h := (cutBytes_cover [119, 1, 483, 1, 334, 1] Source.page631).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap646263, gap646747, gap647082] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
