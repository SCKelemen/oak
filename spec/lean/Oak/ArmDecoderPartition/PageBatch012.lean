import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch006

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell98304 : Cell := ⟨Source.page96, 1024, by simp only [List.length_take, List.length_drop, Source.size96] <;> rfl⟩
def coveredPage96 : Page := ⟨Source.page96, [cell98304], by
  rfl⟩
def cell99328 : Cell := ⟨Source.page97, 1024, by simp only [List.length_take, List.length_drop, Source.size97] <;> rfl⟩
def coveredPage97 : Page := ⟨Source.page97, [cell99328], by
  rfl⟩
def cell100352 : Cell := ⟨Source.page98, 1024, by simp only [List.length_take, List.length_drop, Source.size98] <;> rfl⟩
def coveredPage98 : Page := ⟨Source.page98, [cell100352], by
  rfl⟩
def cell101376 : Cell := ⟨Source.page99, 1024, by simp only [List.length_take, List.length_drop, Source.size99] <;> rfl⟩
def coveredPage99 : Page := ⟨Source.page99, [cell101376], by
  rfl⟩
def cell102400 : Cell := ⟨Source.page100, 1024, by simp only [List.length_take, List.length_drop, Source.size100] <;> rfl⟩
def coveredPage100 : Page := ⟨Source.page100, [cell102400], by
  rfl⟩
def cell103424 : Cell := ⟨Source.page101, 1024, by simp only [List.length_take, List.length_drop, Source.size101] <;> rfl⟩
def coveredPage101 : Page := ⟨Source.page101, [cell103424], by
  rfl⟩
def cell104448 : Cell := ⟨Source.page102, 1024, by simp only [List.length_take, List.length_drop, Source.size102] <;> rfl⟩
def coveredPage102 : Page := ⟨Source.page102, [cell104448], by
  rfl⟩
def cell105472 : Cell := ⟨Source.page103, 1024, by simp only [List.length_take, List.length_drop, Source.size103] <;> rfl⟩
def coveredPage103 : Page := ⟨Source.page103, [cell105472], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
