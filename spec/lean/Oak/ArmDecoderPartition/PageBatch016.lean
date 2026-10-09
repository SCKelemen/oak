import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch008

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell131072 : Cell := ⟨Source.page128, 1024, by simp only [List.length_take, List.length_drop, Source.size128] <;> rfl⟩
def coveredPage128 : Page := ⟨Source.page128, [cell131072], by
  rfl⟩
def cell132096 : Cell := ⟨Source.page129, 1024, by simp only [List.length_take, List.length_drop, Source.size129] <;> rfl⟩
def coveredPage129 : Page := ⟨Source.page129, [cell132096], by
  rfl⟩
def cell133120 : Cell := ⟨Source.page130, 1024, by simp only [List.length_take, List.length_drop, Source.size130] <;> rfl⟩
def coveredPage130 : Page := ⟨Source.page130, [cell133120], by
  rfl⟩
def cell134144 : Cell := ⟨Source.page131, 1024, by simp only [List.length_take, List.length_drop, Source.size131] <;> rfl⟩
def coveredPage131 : Page := ⟨Source.page131, [cell134144], by
  rfl⟩
def cell135168 : Cell := ⟨Source.page132, 1024, by simp only [List.length_take, List.length_drop, Source.size132] <;> rfl⟩
def coveredPage132 : Page := ⟨Source.page132, [cell135168], by
  rfl⟩
def cell136192 : Cell := ⟨Source.page133, 1024, by simp only [List.length_take, List.length_drop, Source.size133] <;> rfl⟩
def coveredPage133 : Page := ⟨Source.page133, [cell136192], by
  rfl⟩
def cell137216 : Cell := ⟨Source.page134, 1024, by simp only [List.length_take, List.length_drop, Source.size134] <;> rfl⟩
def coveredPage134 : Page := ⟨Source.page134, [cell137216], by
  rfl⟩
def cell138240 : Cell := ⟨Source.page135, 1024, by simp only [List.length_take, List.length_drop, Source.size135] <;> rfl⟩
def coveredPage135 : Page := ⟨Source.page135, [cell138240], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
