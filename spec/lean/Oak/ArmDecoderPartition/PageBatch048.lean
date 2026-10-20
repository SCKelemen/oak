import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch024

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell393216 : Cell := ⟨Source.page384, 1024, by simp only [List.length_take, List.length_drop, Source.size384] <;> rfl⟩
def coveredPage384 : Page := ⟨Source.page384, [cell393216], by
  rfl⟩
def cell394240 : Cell := ⟨Source.page385, 1024, by simp only [List.length_take, List.length_drop, Source.size385] <;> rfl⟩
def coveredPage385 : Page := ⟨Source.page385, [cell394240], by
  rfl⟩
def cell395264 : Cell := ⟨Source.page386, 1024, by simp only [List.length_take, List.length_drop, Source.size386] <;> rfl⟩
def coveredPage386 : Page := ⟨Source.page386, [cell395264], by
  rfl⟩
def cell396288 : Cell := ⟨Source.page387, 1024, by simp only [List.length_take, List.length_drop, Source.size387] <;> rfl⟩
def coveredPage387 : Page := ⟨Source.page387, [cell396288], by
  rfl⟩
def cell397312 : Cell := ⟨Source.page388, 1024, by simp only [List.length_take, List.length_drop, Source.size388] <;> rfl⟩
def coveredPage388 : Page := ⟨Source.page388, [cell397312], by
  rfl⟩
def cell398336 : Cell := ⟨Source.page389, 1024, by simp only [List.length_take, List.length_drop, Source.size389] <;> rfl⟩
def coveredPage389 : Page := ⟨Source.page389, [cell398336], by
  rfl⟩
def cell399360 : Cell := ⟨Source.page390, 1024, by simp only [List.length_take, List.length_drop, Source.size390] <;> rfl⟩
def coveredPage390 : Page := ⟨Source.page390, [cell399360], by
  rfl⟩
def cell400384 : Cell := ⟨Source.page391.take 591, 591, by simp only [List.length_take, List.length_drop, Source.size391] <;> rfl⟩
def cell400975 : Cell := ⟨(Source.page391.drop 591), 433, by simp only [List.length_take, List.length_drop, Source.size391] <;> rfl⟩
def coveredPage391 : Page := ⟨Source.page391, [cell400384, cell400975], by
  have h := (cutBytes_cover [591] Source.page391).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
