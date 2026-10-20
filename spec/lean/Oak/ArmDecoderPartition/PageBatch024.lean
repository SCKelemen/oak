import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch012

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell196608 : Cell := ⟨Source.page192, 1024, by simp only [List.length_take, List.length_drop, Source.size192] <;> rfl⟩
def coveredPage192 : Page := ⟨Source.page192, [cell196608], by
  rfl⟩
def cell197632 : Cell := ⟨Source.page193, 1024, by simp only [List.length_take, List.length_drop, Source.size193] <;> rfl⟩
def coveredPage193 : Page := ⟨Source.page193, [cell197632], by
  rfl⟩
def cell198656 : Cell := ⟨Source.page194, 1024, by simp only [List.length_take, List.length_drop, Source.size194] <;> rfl⟩
def coveredPage194 : Page := ⟨Source.page194, [cell198656], by
  rfl⟩
def cell199680 : Cell := ⟨Source.page195, 1024, by simp only [List.length_take, List.length_drop, Source.size195] <;> rfl⟩
def coveredPage195 : Page := ⟨Source.page195, [cell199680], by
  rfl⟩
def cell200704 : Cell := ⟨Source.page196, 1024, by simp only [List.length_take, List.length_drop, Source.size196] <;> rfl⟩
def coveredPage196 : Page := ⟨Source.page196, [cell200704], by
  rfl⟩
def cell201728 : Cell := ⟨Source.page197, 1024, by simp only [List.length_take, List.length_drop, Source.size197] <;> rfl⟩
def coveredPage197 : Page := ⟨Source.page197, [cell201728], by
  rfl⟩
def cell202752 : Cell := ⟨Source.page198, 1024, by simp only [List.length_take, List.length_drop, Source.size198] <;> rfl⟩
def coveredPage198 : Page := ⟨Source.page198, [cell202752], by
  rfl⟩
def cell203776 : Cell := ⟨Source.page199, 1024, by simp only [List.length_take, List.length_drop, Source.size199] <;> rfl⟩
def coveredPage199 : Page := ⟨Source.page199, [cell203776], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
