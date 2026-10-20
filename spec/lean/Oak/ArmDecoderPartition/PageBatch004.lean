import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch002

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell32768 : Cell := ⟨Source.page32, 1024, by simp only [List.length_take, List.length_drop, Source.size32] <;> rfl⟩
def coveredPage32 : Page := ⟨Source.page32, [cell32768], by
  rfl⟩
def cell33792 : Cell := ⟨Source.page33, 1024, by simp only [List.length_take, List.length_drop, Source.size33] <;> rfl⟩
def coveredPage33 : Page := ⟨Source.page33, [cell33792], by
  rfl⟩
def cell34816 : Cell := ⟨Source.page34, 1024, by simp only [List.length_take, List.length_drop, Source.size34] <;> rfl⟩
def coveredPage34 : Page := ⟨Source.page34, [cell34816], by
  rfl⟩
def cell35840 : Cell := ⟨Source.page35, 1024, by simp only [List.length_take, List.length_drop, Source.size35] <;> rfl⟩
def coveredPage35 : Page := ⟨Source.page35, [cell35840], by
  rfl⟩
def cell36864 : Cell := ⟨Source.page36, 1024, by simp only [List.length_take, List.length_drop, Source.size36] <;> rfl⟩
def coveredPage36 : Page := ⟨Source.page36, [cell36864], by
  rfl⟩
def cell37888 : Cell := ⟨Source.page37, 1024, by simp only [List.length_take, List.length_drop, Source.size37] <;> rfl⟩
def coveredPage37 : Page := ⟨Source.page37, [cell37888], by
  rfl⟩
def cell38912 : Cell := ⟨Source.page38, 1024, by simp only [List.length_take, List.length_drop, Source.size38] <;> rfl⟩
def coveredPage38 : Page := ⟨Source.page38, [cell38912], by
  rfl⟩
def cell39936 : Cell := ⟨Source.page39, 1024, by simp only [List.length_take, List.length_drop, Source.size39] <;> rfl⟩
def coveredPage39 : Page := ⟨Source.page39, [cell39936], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
