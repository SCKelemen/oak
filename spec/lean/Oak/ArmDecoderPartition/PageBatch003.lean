import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch001

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell24576 : Cell := ⟨Source.page24, 1024, by simp only [List.length_take, List.length_drop, Source.size24] <;> rfl⟩
def coveredPage24 : Page := ⟨Source.page24, [cell24576], by
  rfl⟩
def cell25600 : Cell := ⟨Source.page25, 1024, by simp only [List.length_take, List.length_drop, Source.size25] <;> rfl⟩
def coveredPage25 : Page := ⟨Source.page25, [cell25600], by
  rfl⟩
def cell26624 : Cell := ⟨Source.page26, 1024, by simp only [List.length_take, List.length_drop, Source.size26] <;> rfl⟩
def coveredPage26 : Page := ⟨Source.page26, [cell26624], by
  rfl⟩
def cell27648 : Cell := ⟨Source.page27, 1024, by simp only [List.length_take, List.length_drop, Source.size27] <;> rfl⟩
def coveredPage27 : Page := ⟨Source.page27, [cell27648], by
  rfl⟩
def cell28672 : Cell := ⟨Source.page28, 1024, by simp only [List.length_take, List.length_drop, Source.size28] <;> rfl⟩
def coveredPage28 : Page := ⟨Source.page28, [cell28672], by
  rfl⟩
def cell29696 : Cell := ⟨Source.page29, 1024, by simp only [List.length_take, List.length_drop, Source.size29] <;> rfl⟩
def coveredPage29 : Page := ⟨Source.page29, [cell29696], by
  rfl⟩
def cell30720 : Cell := ⟨Source.page30, 1024, by simp only [List.length_take, List.length_drop, Source.size30] <;> rfl⟩
def coveredPage30 : Page := ⟨Source.page30, [cell30720], by
  rfl⟩
def cell31744 : Cell := ⟨Source.page31, 1024, by simp only [List.length_take, List.length_drop, Source.size31] <;> rfl⟩
def coveredPage31 : Page := ⟨Source.page31, [cell31744], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
