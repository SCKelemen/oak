import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch010

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell163840 : Cell := ⟨Source.page160, 1024, by simp only [List.length_take, List.length_drop, Source.size160] <;> rfl⟩
def coveredPage160 : Page := ⟨Source.page160, [cell163840], by
  rfl⟩
def cell164864 : Cell := ⟨Source.page161, 1024, by simp only [List.length_take, List.length_drop, Source.size161] <;> rfl⟩
def coveredPage161 : Page := ⟨Source.page161, [cell164864], by
  rfl⟩
def cell165888 : Cell := ⟨Source.page162, 1024, by simp only [List.length_take, List.length_drop, Source.size162] <;> rfl⟩
def coveredPage162 : Page := ⟨Source.page162, [cell165888], by
  rfl⟩
def cell166912 : Cell := ⟨Source.page163, 1024, by simp only [List.length_take, List.length_drop, Source.size163] <;> rfl⟩
def coveredPage163 : Page := ⟨Source.page163, [cell166912], by
  rfl⟩
def cell167936 : Cell := ⟨Source.page164, 1024, by simp only [List.length_take, List.length_drop, Source.size164] <;> rfl⟩
def coveredPage164 : Page := ⟨Source.page164, [cell167936], by
  rfl⟩
def cell168960 : Cell := ⟨Source.page165, 1024, by simp only [List.length_take, List.length_drop, Source.size165] <;> rfl⟩
def coveredPage165 : Page := ⟨Source.page165, [cell168960], by
  rfl⟩
def cell169984 : Cell := ⟨Source.page166, 1024, by simp only [List.length_take, List.length_drop, Source.size166] <;> rfl⟩
def coveredPage166 : Page := ⟨Source.page166, [cell169984], by
  rfl⟩
def cell171008 : Cell := ⟨Source.page167, 1024, by simp only [List.length_take, List.length_drop, Source.size167] <;> rfl⟩
def coveredPage167 : Page := ⟨Source.page167, [cell171008], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
