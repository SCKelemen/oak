import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch000

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell0 : Cell := ⟨Source.page0, 1024, by simp only [List.length_take, List.length_drop, Source.size0] <;> rfl⟩
def coveredPage0 : Page := ⟨Source.page0, [cell0], by
  rfl⟩
def cell1024 : Cell := ⟨Source.page1, 1024, by simp only [List.length_take, List.length_drop, Source.size1] <;> rfl⟩
def coveredPage1 : Page := ⟨Source.page1, [cell1024], by
  rfl⟩
def cell2048 : Cell := ⟨Source.page2, 1024, by simp only [List.length_take, List.length_drop, Source.size2] <;> rfl⟩
def coveredPage2 : Page := ⟨Source.page2, [cell2048], by
  rfl⟩
def cell3072 : Cell := ⟨Source.page3, 1024, by simp only [List.length_take, List.length_drop, Source.size3] <;> rfl⟩
def coveredPage3 : Page := ⟨Source.page3, [cell3072], by
  rfl⟩
def cell4096 : Cell := ⟨Source.page4, 1024, by simp only [List.length_take, List.length_drop, Source.size4] <;> rfl⟩
def coveredPage4 : Page := ⟨Source.page4, [cell4096], by
  rfl⟩
def cell5120 : Cell := ⟨Source.page5, 1024, by simp only [List.length_take, List.length_drop, Source.size5] <;> rfl⟩
def coveredPage5 : Page := ⟨Source.page5, [cell5120], by
  rfl⟩
def cell6144 : Cell := ⟨Source.page6, 1024, by simp only [List.length_take, List.length_drop, Source.size6] <;> rfl⟩
def coveredPage6 : Page := ⟨Source.page6, [cell6144], by
  rfl⟩
def cell7168 : Cell := ⟨Source.page7, 1024, by simp only [List.length_take, List.length_drop, Source.size7] <;> rfl⟩
def coveredPage7 : Page := ⟨Source.page7, [cell7168], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
