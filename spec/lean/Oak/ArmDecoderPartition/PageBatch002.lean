import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch001

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell16384 : Cell := ⟨Source.page16, 1024, by simp only [List.length_take, List.length_drop, Source.size16] <;> rfl⟩
def coveredPage16 : Page := ⟨Source.page16, [cell16384], by
  rfl⟩
def cell17408 : Cell := ⟨Source.page17, 1024, by simp only [List.length_take, List.length_drop, Source.size17] <;> rfl⟩
def coveredPage17 : Page := ⟨Source.page17, [cell17408], by
  rfl⟩
def cell18432 : Cell := ⟨Source.page18, 1024, by simp only [List.length_take, List.length_drop, Source.size18] <;> rfl⟩
def coveredPage18 : Page := ⟨Source.page18, [cell18432], by
  rfl⟩
def cell19456 : Cell := ⟨Source.page19, 1024, by simp only [List.length_take, List.length_drop, Source.size19] <;> rfl⟩
def coveredPage19 : Page := ⟨Source.page19, [cell19456], by
  rfl⟩
def cell20480 : Cell := ⟨Source.page20, 1024, by simp only [List.length_take, List.length_drop, Source.size20] <;> rfl⟩
def coveredPage20 : Page := ⟨Source.page20, [cell20480], by
  rfl⟩
def cell21504 : Cell := ⟨Source.page21, 1024, by simp only [List.length_take, List.length_drop, Source.size21] <;> rfl⟩
def coveredPage21 : Page := ⟨Source.page21, [cell21504], by
  rfl⟩
def cell22528 : Cell := ⟨Source.page22, 1024, by simp only [List.length_take, List.length_drop, Source.size22] <;> rfl⟩
def coveredPage22 : Page := ⟨Source.page22, [cell22528], by
  rfl⟩
def cell23552 : Cell := ⟨Source.page23, 1024, by simp only [List.length_take, List.length_drop, Source.size23] <;> rfl⟩
def coveredPage23 : Page := ⟨Source.page23, [cell23552], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
