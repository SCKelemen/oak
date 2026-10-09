import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch016

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell262144 : Cell := ⟨Source.page256, 1024, by simp only [List.length_take, List.length_drop, Source.size256] <;> rfl⟩
def coveredPage256 : Page := ⟨Source.page256, [cell262144], by
  rfl⟩
def cell263168 : Cell := ⟨Source.page257, 1024, by simp only [List.length_take, List.length_drop, Source.size257] <;> rfl⟩
def coveredPage257 : Page := ⟨Source.page257, [cell263168], by
  rfl⟩
def cell264192 : Cell := ⟨Source.page258, 1024, by simp only [List.length_take, List.length_drop, Source.size258] <;> rfl⟩
def coveredPage258 : Page := ⟨Source.page258, [cell264192], by
  rfl⟩
def cell265216 : Cell := ⟨Source.page259, 1024, by simp only [List.length_take, List.length_drop, Source.size259] <;> rfl⟩
def coveredPage259 : Page := ⟨Source.page259, [cell265216], by
  rfl⟩
def cell266240 : Cell := ⟨Source.page260, 1024, by simp only [List.length_take, List.length_drop, Source.size260] <;> rfl⟩
def coveredPage260 : Page := ⟨Source.page260, [cell266240], by
  rfl⟩
def cell267264 : Cell := ⟨Source.page261, 1024, by simp only [List.length_take, List.length_drop, Source.size261] <;> rfl⟩
def coveredPage261 : Page := ⟨Source.page261, [cell267264], by
  rfl⟩
def cell268288 : Cell := ⟨Source.page262, 1024, by simp only [List.length_take, List.length_drop, Source.size262] <;> rfl⟩
def coveredPage262 : Page := ⟨Source.page262, [cell268288], by
  rfl⟩
def cell269312 : Cell := ⟨Source.page263, 1024, by simp only [List.length_take, List.length_drop, Source.size263] <;> rfl⟩
def coveredPage263 : Page := ⟨Source.page263, [cell269312], by
  rfl⟩
end Oak.ArmDecoderPartition.Data
