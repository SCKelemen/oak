import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch011

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell180224 : Cell := ⟨Source.page176, 1024, by simp only [List.length_take, List.length_drop, Source.size176] <;> rfl⟩
def coveredPage176 : Page := ⟨Source.page176, [cell180224], by
  rfl⟩
def cell181248 : Cell := ⟨Source.page177, 1024, by simp only [List.length_take, List.length_drop, Source.size177] <;> rfl⟩
def coveredPage177 : Page := ⟨Source.page177, [cell181248], by
  rfl⟩
def cell182272 : Cell := ⟨Source.page178, 1024, by simp only [List.length_take, List.length_drop, Source.size178] <;> rfl⟩
def coveredPage178 : Page := ⟨Source.page178, [cell182272], by
  rfl⟩
def cell183296 : Cell := ⟨Source.page179, 1024, by simp only [List.length_take, List.length_drop, Source.size179] <;> rfl⟩
def coveredPage179 : Page := ⟨Source.page179, [cell183296], by
  rfl⟩
def cell184320 : Cell := ⟨Source.page180, 1024, by simp only [List.length_take, List.length_drop, Source.size180] <;> rfl⟩
def coveredPage180 : Page := ⟨Source.page180, [cell184320], by
  rfl⟩
def cell185344 : Cell := ⟨Source.page181, 1024, by simp only [List.length_take, List.length_drop, Source.size181] <;> rfl⟩
def coveredPage181 : Page := ⟨Source.page181, [cell185344], by
  rfl⟩
def cell186368 : Cell := ⟨Source.page182, 1024, by simp only [List.length_take, List.length_drop, Source.size182] <;> rfl⟩
def coveredPage182 : Page := ⟨Source.page182, [cell186368], by
  rfl⟩
def cell187392 : Cell := ⟨Source.page183, 1024, by simp only [List.length_take, List.length_drop, Source.size183] <;> rfl⟩
def coveredPage183 : Page := ⟨Source.page183, [cell187392], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
