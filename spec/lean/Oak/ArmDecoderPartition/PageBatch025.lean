import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch012

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell204800 : Cell := ⟨Source.page200, 1024, by simp only [List.length_take, List.length_drop, Source.size200] <;> rfl⟩
def coveredPage200 : Page := ⟨Source.page200, [cell204800], by
  rfl⟩
def cell205824 : Cell := ⟨Source.page201, 1024, by simp only [List.length_take, List.length_drop, Source.size201] <;> rfl⟩
def coveredPage201 : Page := ⟨Source.page201, [cell205824], by
  rfl⟩
def cell206848 : Cell := ⟨Source.page202, 1024, by simp only [List.length_take, List.length_drop, Source.size202] <;> rfl⟩
def coveredPage202 : Page := ⟨Source.page202, [cell206848], by
  rfl⟩
def cell207872 : Cell := ⟨Source.page203, 1024, by simp only [List.length_take, List.length_drop, Source.size203] <;> rfl⟩
def coveredPage203 : Page := ⟨Source.page203, [cell207872], by
  rfl⟩
def cell208896 : Cell := ⟨Source.page204, 1024, by simp only [List.length_take, List.length_drop, Source.size204] <;> rfl⟩
def coveredPage204 : Page := ⟨Source.page204, [cell208896], by
  rfl⟩
def cell209920 : Cell := ⟨Source.page205, 1024, by simp only [List.length_take, List.length_drop, Source.size205] <;> rfl⟩
def coveredPage205 : Page := ⟨Source.page205, [cell209920], by
  rfl⟩
def cell210944 : Cell := ⟨Source.page206, 1024, by simp only [List.length_take, List.length_drop, Source.size206] <;> rfl⟩
def coveredPage206 : Page := ⟨Source.page206, [cell210944], by
  rfl⟩
def cell211968 : Cell := ⟨Source.page207, 1024, by simp only [List.length_take, List.length_drop, Source.size207] <;> rfl⟩
def coveredPage207 : Page := ⟨Source.page207, [cell211968], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
