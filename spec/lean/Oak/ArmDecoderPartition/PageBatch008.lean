import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch004

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell65536 : Cell := ⟨Source.page64, 1024, by simp only [List.length_take, List.length_drop, Source.size64] <;> rfl⟩
def coveredPage64 : Page := ⟨Source.page64, [cell65536], by
  rfl⟩
def cell66560 : Cell := ⟨Source.page65, 1024, by simp only [List.length_take, List.length_drop, Source.size65] <;> rfl⟩
def coveredPage65 : Page := ⟨Source.page65, [cell66560], by
  rfl⟩
def cell67584 : Cell := ⟨Source.page66, 1024, by simp only [List.length_take, List.length_drop, Source.size66] <;> rfl⟩
def coveredPage66 : Page := ⟨Source.page66, [cell67584], by
  rfl⟩
def cell68608 : Cell := ⟨Source.page67, 1024, by simp only [List.length_take, List.length_drop, Source.size67] <;> rfl⟩
def coveredPage67 : Page := ⟨Source.page67, [cell68608], by
  rfl⟩
def cell69632 : Cell := ⟨Source.page68, 1024, by simp only [List.length_take, List.length_drop, Source.size68] <;> rfl⟩
def coveredPage68 : Page := ⟨Source.page68, [cell69632], by
  rfl⟩
def cell70656 : Cell := ⟨Source.page69, 1024, by simp only [List.length_take, List.length_drop, Source.size69] <;> rfl⟩
def coveredPage69 : Page := ⟨Source.page69, [cell70656], by
  rfl⟩
def cell71680 : Cell := ⟨Source.page70, 1024, by simp only [List.length_take, List.length_drop, Source.size70] <;> rfl⟩
def coveredPage70 : Page := ⟨Source.page70, [cell71680], by
  rfl⟩
def cell72704 : Cell := ⟨Source.page71, 1024, by simp only [List.length_take, List.length_drop, Source.size71] <;> rfl⟩
def coveredPage71 : Page := ⟨Source.page71, [cell72704], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
