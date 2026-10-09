import Oak.ArmDecoderPartition.PageBatch023
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage184 : scan cell188416.bytes ([98, 105, 116, 115, 40, 53, 41], 0) = ([32, 98, 105, 116, 115, 40, 51], 0) := by rfl
theorem scanPage185 : scan cell189440.bytes ([32, 86, 67, 76, 90, 95, 84], 0) = ([98, 105, 116, 115, 40, 53, 41], 0) := by rfl
theorem scanPage186 : scan cell190464.bytes ([32, 64, 32, 95, 32, 58, 32], 0) = ([32, 86, 67, 76, 90, 95, 84], 0) := by rfl
theorem scanPage187 : scan cell191488.bytes ([48, 98, 49, 32, 64, 32, 95], 0) = ([32, 64, 32, 95, 32, 58, 32], 0) := by rfl
theorem scanPage188 : scan cell192512.bytes ([116, 115, 40, 49, 41, 32, 61], 0) = ([48, 98, 49, 32, 64, 32, 95], 0) := by rfl
theorem scanPage189 : scan cell193536.bytes ([98, 105, 116, 115, 40, 49, 41], 0) = ([116, 115, 40, 49, 41, 32, 61], 0) := by rfl
theorem scanPage190 : scan cell194560.bytes ([93, 59, 10, 32, 32, 32, 32], 0) = ([98, 105, 116, 115, 40, 49, 41], 0) := by rfl
theorem scanPage191 : scan cell195584.bytes ([10, 102, 117, 110, 99, 116, 105], 0) = ([93, 59, 10, 32, 32, 32, 32], 0) := by rfl
end Oak.ArmDecoderPartition.Data
