import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch000

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell8192 : Cell := ⟨Source.page8, 1024, by simp only [List.length_take, List.length_drop, Source.size8] <;> rfl⟩
def coveredPage8 : Page := ⟨Source.page8, [cell8192], by
  rfl⟩
def cell9216 : Cell := ⟨Source.page9, 1024, by simp only [List.length_take, List.length_drop, Source.size9] <;> rfl⟩
def coveredPage9 : Page := ⟨Source.page9, [cell9216], by
  rfl⟩
def cell10240 : Cell := ⟨Source.page10, 1024, by simp only [List.length_take, List.length_drop, Source.size10] <;> rfl⟩
def coveredPage10 : Page := ⟨Source.page10, [cell10240], by
  rfl⟩
def cell11264 : Cell := ⟨Source.page11, 1024, by simp only [List.length_take, List.length_drop, Source.size11] <;> rfl⟩
def coveredPage11 : Page := ⟨Source.page11, [cell11264], by
  rfl⟩
def cell12288 : Cell := ⟨Source.page12, 1024, by simp only [List.length_take, List.length_drop, Source.size12] <;> rfl⟩
def coveredPage12 : Page := ⟨Source.page12, [cell12288], by
  rfl⟩
def cell13312 : Cell := ⟨Source.page13, 1024, by simp only [List.length_take, List.length_drop, Source.size13] <;> rfl⟩
def coveredPage13 : Page := ⟨Source.page13, [cell13312], by
  rfl⟩
def cell14336 : Cell := ⟨Source.page14, 1024, by simp only [List.length_take, List.length_drop, Source.size14] <;> rfl⟩
def coveredPage14 : Page := ⟨Source.page14, [cell14336], by
  rfl⟩
def cell15360 : Cell := ⟨Source.page15, 1024, by simp only [List.length_take, List.length_drop, Source.size15] <;> rfl⟩
def coveredPage15 : Page := ⟨Source.page15, [cell15360], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
