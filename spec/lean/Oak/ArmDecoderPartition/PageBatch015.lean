import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch007

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell122880 : Cell := ⟨Source.page120, 1024, by simp only [List.length_take, List.length_drop, Source.size120] <;> rfl⟩
def coveredPage120 : Page := ⟨Source.page120, [cell122880], by
  rfl⟩
def cell123904 : Cell := ⟨Source.page121, 1024, by simp only [List.length_take, List.length_drop, Source.size121] <;> rfl⟩
def coveredPage121 : Page := ⟨Source.page121, [cell123904], by
  rfl⟩
def cell124928 : Cell := ⟨Source.page122, 1024, by simp only [List.length_take, List.length_drop, Source.size122] <;> rfl⟩
def coveredPage122 : Page := ⟨Source.page122, [cell124928], by
  rfl⟩
def cell125952 : Cell := ⟨Source.page123, 1024, by simp only [List.length_take, List.length_drop, Source.size123] <;> rfl⟩
def coveredPage123 : Page := ⟨Source.page123, [cell125952], by
  rfl⟩
def cell126976 : Cell := ⟨Source.page124, 1024, by simp only [List.length_take, List.length_drop, Source.size124] <;> rfl⟩
def coveredPage124 : Page := ⟨Source.page124, [cell126976], by
  rfl⟩
def cell128000 : Cell := ⟨Source.page125, 1024, by simp only [List.length_take, List.length_drop, Source.size125] <;> rfl⟩
def coveredPage125 : Page := ⟨Source.page125, [cell128000], by
  rfl⟩
def cell129024 : Cell := ⟨Source.page126, 1024, by simp only [List.length_take, List.length_drop, Source.size126] <;> rfl⟩
def coveredPage126 : Page := ⟨Source.page126, [cell129024], by
  rfl⟩
def cell130048 : Cell := ⟨Source.page127, 1024, by simp only [List.length_take, List.length_drop, Source.size127] <;> rfl⟩
def coveredPage127 : Page := ⟨Source.page127, [cell130048], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
