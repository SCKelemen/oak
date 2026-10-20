import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch031

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell516096 : Cell := ⟨Source.page504.take 376, 376, by simp only [List.length_take, List.length_drop, Source.size504] <;> rfl⟩
theorem gap516472 : (Source.page504.drop 376).take 1 = [10] := by rfl
def cell516473 : Cell := ⟨(Source.page504.drop 377).take 524, 524, by simp only [List.length_take, List.length_drop, Source.size504] <;> rfl⟩
theorem gap516997 : (Source.page504.drop 901).take 1 = [10] := by rfl
def cell516998 : Cell := ⟨(Source.page504.drop 902), 122, by simp only [List.length_take, List.length_drop, Source.size504] <;> rfl⟩
def coveredPage504 : Page := ⟨Source.page504, [cell516096, lf, cell516473, lf, cell516998], by
  have h := (cutBytes_cover [376, 1, 524, 1] Source.page504).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap516472, gap516997] at h
  exact h⟩
def cell517120 : Cell := ⟨Source.page505.take 359, 359, by simp only [List.length_take, List.length_drop, Source.size505] <;> rfl⟩
theorem gap517479 : (Source.page505.drop 359).take 1 = [10] := by rfl
def cell517480 : Cell := ⟨(Source.page505.drop 360).take 504, 504, by simp only [List.length_take, List.length_drop, Source.size505] <;> rfl⟩
theorem gap517984 : (Source.page505.drop 864).take 1 = [10] := by rfl
def cell517985 : Cell := ⟨(Source.page505.drop 865), 159, by simp only [List.length_take, List.length_drop, Source.size505] <;> rfl⟩
def coveredPage505 : Page := ⟨Source.page505, [cell517120, lf, cell517480, lf, cell517985], by
  have h := (cutBytes_cover [359, 1, 504, 1] Source.page505).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap517479, gap517984] at h
  exact h⟩
def cell518144 : Cell := ⟨Source.page506.take 342, 342, by simp only [List.length_take, List.length_drop, Source.size506] <;> rfl⟩
theorem gap518486 : (Source.page506.drop 342).take 1 = [10] := by rfl
def cell518487 : Cell := ⟨(Source.page506.drop 343).take 481, 481, by simp only [List.length_take, List.length_drop, Source.size506] <;> rfl⟩
theorem gap518968 : (Source.page506.drop 824).take 1 = [10] := by rfl
def cell518969 : Cell := ⟨(Source.page506.drop 825), 199, by simp only [List.length_take, List.length_drop, Source.size506] <;> rfl⟩
def coveredPage506 : Page := ⟨Source.page506, [cell518144, lf, cell518487, lf, cell518969], by
  have h := (cutBytes_cover [342, 1, 481, 1] Source.page506).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap518486, gap518968] at h
  exact h⟩
def cell519168 : Cell := ⟨Source.page507.take 214, 214, by simp only [List.length_take, List.length_drop, Source.size507] <;> rfl⟩
theorem gap519382 : (Source.page507.drop 214).take 1 = [10] := by rfl
def cell519383 : Cell := ⟨(Source.page507.drop 215).take 477, 477, by simp only [List.length_take, List.length_drop, Source.size507] <;> rfl⟩
theorem gap519860 : (Source.page507.drop 692).take 1 = [10] := by rfl
def cell519861 : Cell := ⟨(Source.page507.drop 693), 331, by simp only [List.length_take, List.length_drop, Source.size507] <;> rfl⟩
def coveredPage507 : Page := ⟨Source.page507, [cell519168, lf, cell519383, lf, cell519861], by
  have h := (cutBytes_cover [214, 1, 477, 1] Source.page507).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap519382, gap519860] at h
  exact h⟩
def cell520192 : Cell := ⟨Source.page508.take 149, 149, by simp only [List.length_take, List.length_drop, Source.size508] <;> rfl⟩
theorem gap520341 : (Source.page508.drop 149).take 1 = [10] := by rfl
def cell520342 : Cell := ⟨(Source.page508.drop 150).take 572, 572, by simp only [List.length_take, List.length_drop, Source.size508] <;> rfl⟩
theorem gap520914 : (Source.page508.drop 722).take 1 = [10] := by rfl
def cell520915 : Cell := ⟨(Source.page508.drop 723), 301, by simp only [List.length_take, List.length_drop, Source.size508] <;> rfl⟩
def coveredPage508 : Page := ⟨Source.page508, [cell520192, lf, cell520342, lf, cell520915], by
  have h := (cutBytes_cover [149, 1, 572, 1] Source.page508).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap520341, gap520914] at h
  exact h⟩
def cell521216 : Cell := ⟨Source.page509.take 200, 200, by simp only [List.length_take, List.length_drop, Source.size509] <;> rfl⟩
theorem gap521416 : (Source.page509.drop 200).take 1 = [10] := by rfl
def cell521417 : Cell := ⟨(Source.page509.drop 201).take 447, 447, by simp only [List.length_take, List.length_drop, Source.size509] <;> rfl⟩
theorem gap521864 : (Source.page509.drop 648).take 1 = [10] := by rfl
def cell521865 : Cell := ⟨(Source.page509.drop 649), 375, by simp only [List.length_take, List.length_drop, Source.size509] <;> rfl⟩
def coveredPage509 : Page := ⟨Source.page509, [cell521216, lf, cell521417, lf, cell521865], by
  have h := (cutBytes_cover [200, 1, 447, 1] Source.page509).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap521416, gap521864] at h
  exact h⟩
def cell522240 : Cell := ⟨Source.page510.take 132, 132, by simp only [List.length_take, List.length_drop, Source.size510] <;> rfl⟩
theorem gap522372 : (Source.page510.drop 132).take 1 = [10] := by rfl
def cell522373 : Cell := ⟨(Source.page510.drop 133).take 462, 462, by simp only [List.length_take, List.length_drop, Source.size510] <;> rfl⟩
theorem gap522835 : (Source.page510.drop 595).take 1 = [10] := by rfl
def cell522836 : Cell := ⟨(Source.page510.drop 596), 428, by simp only [List.length_take, List.length_drop, Source.size510] <;> rfl⟩
def coveredPage510 : Page := ⟨Source.page510, [cell522240, lf, cell522373, lf, cell522836], by
  have h := (cutBytes_cover [132, 1, 462, 1] Source.page510).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap522372, gap522835] at h
  exact h⟩
def cell523264 : Cell := ⟨Source.page511.take 173, 173, by simp only [List.length_take, List.length_drop, Source.size511] <;> rfl⟩
theorem gap523437 : (Source.page511.drop 173).take 1 = [10] := by rfl
def cell523438 : Cell := ⟨(Source.page511.drop 174).take 379, 379, by simp only [List.length_take, List.length_drop, Source.size511] <;> rfl⟩
theorem gap523817 : (Source.page511.drop 553).take 1 = [10] := by rfl
def cell523818 : Cell := ⟨(Source.page511.drop 554), 470, by simp only [List.length_take, List.length_drop, Source.size511] <;> rfl⟩
def coveredPage511 : Page := ⟨Source.page511, [cell523264, lf, cell523438, lf, cell523818], by
  have h := (cutBytes_cover [173, 1, 379, 1] Source.page511).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap523437, gap523817] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
