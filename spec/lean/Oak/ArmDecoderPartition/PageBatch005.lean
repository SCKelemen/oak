import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch002

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell40960 : Cell := ⟨Source.page40, 1024, by simp only [List.length_take, List.length_drop, Source.size40] <;> rfl⟩
def coveredPage40 : Page := ⟨Source.page40, [cell40960], by
  rfl⟩
def cell41984 : Cell := ⟨Source.page41, 1024, by simp only [List.length_take, List.length_drop, Source.size41] <;> rfl⟩
def coveredPage41 : Page := ⟨Source.page41, [cell41984], by
  rfl⟩
def cell43008 : Cell := ⟨Source.page42, 1024, by simp only [List.length_take, List.length_drop, Source.size42] <;> rfl⟩
def coveredPage42 : Page := ⟨Source.page42, [cell43008], by
  rfl⟩
def cell44032 : Cell := ⟨Source.page43, 1024, by simp only [List.length_take, List.length_drop, Source.size43] <;> rfl⟩
def coveredPage43 : Page := ⟨Source.page43, [cell44032], by
  rfl⟩
def cell45056 : Cell := ⟨Source.page44, 1024, by simp only [List.length_take, List.length_drop, Source.size44] <;> rfl⟩
def coveredPage44 : Page := ⟨Source.page44, [cell45056], by
  rfl⟩
def cell46080 : Cell := ⟨Source.page45, 1024, by simp only [List.length_take, List.length_drop, Source.size45] <;> rfl⟩
def coveredPage45 : Page := ⟨Source.page45, [cell46080], by
  rfl⟩
def cell47104 : Cell := ⟨Source.page46, 1024, by simp only [List.length_take, List.length_drop, Source.size46] <;> rfl⟩
def coveredPage46 : Page := ⟨Source.page46, [cell47104], by
  rfl⟩
def cell48128 : Cell := ⟨Source.page47, 1024, by simp only [List.length_take, List.length_drop, Source.size47] <;> rfl⟩
def coveredPage47 : Page := ⟨Source.page47, [cell48128], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
