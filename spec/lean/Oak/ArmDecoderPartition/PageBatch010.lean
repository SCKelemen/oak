import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch005

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell81920 : Cell := ⟨Source.page80, 1024, by simp only [List.length_take, List.length_drop, Source.size80] <;> rfl⟩
def coveredPage80 : Page := ⟨Source.page80, [cell81920], by
  rfl⟩
def cell82944 : Cell := ⟨Source.page81, 1024, by simp only [List.length_take, List.length_drop, Source.size81] <;> rfl⟩
def coveredPage81 : Page := ⟨Source.page81, [cell82944], by
  rfl⟩
def cell83968 : Cell := ⟨Source.page82, 1024, by simp only [List.length_take, List.length_drop, Source.size82] <;> rfl⟩
def coveredPage82 : Page := ⟨Source.page82, [cell83968], by
  rfl⟩
def cell84992 : Cell := ⟨Source.page83, 1024, by simp only [List.length_take, List.length_drop, Source.size83] <;> rfl⟩
def coveredPage83 : Page := ⟨Source.page83, [cell84992], by
  rfl⟩
def cell86016 : Cell := ⟨Source.page84, 1024, by simp only [List.length_take, List.length_drop, Source.size84] <;> rfl⟩
def coveredPage84 : Page := ⟨Source.page84, [cell86016], by
  rfl⟩
def cell87040 : Cell := ⟨Source.page85, 1024, by simp only [List.length_take, List.length_drop, Source.size85] <;> rfl⟩
def coveredPage85 : Page := ⟨Source.page85, [cell87040], by
  rfl⟩
def cell88064 : Cell := ⟨Source.page86, 1024, by simp only [List.length_take, List.length_drop, Source.size86] <;> rfl⟩
def coveredPage86 : Page := ⟨Source.page86, [cell88064], by
  rfl⟩
def cell89088 : Cell := ⟨Source.page87, 1024, by simp only [List.length_take, List.length_drop, Source.size87] <;> rfl⟩
def coveredPage87 : Page := ⟨Source.page87, [cell89088], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
