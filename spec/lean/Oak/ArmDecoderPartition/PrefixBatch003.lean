import Oak.ArmDecoderPartition.PageBatch003
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage24 : scan cell24576.bytes ([91, 51, 32, 46, 46, 32, 48], 0) = ([10, 32, 32, 32, 32, 105, 109], 0) := by rfl
theorem scanPage25 : scan cell25600.bytes ([86, 65, 67, 71, 69, 95, 84], 0) = ([91, 51, 32, 46, 46, 32, 48], 0) := by rfl
theorem scanPage26 : scan cell26624.bytes ([58, 32, 98, 105, 116, 115, 40], 0) = ([86, 65, 67, 71, 69, 95, 84], 0) := by rfl
theorem scanPage27 : scan cell27648.bytes ([110, 44, 32, 86, 100, 44, 32], 0) = ([58, 32, 98, 105, 116, 115, 40], 0) := by rfl
theorem scanPage28 : scan cell28672.bytes ([41, 32, 64, 32, 48, 98, 48], 0) = ([110, 44, 32, 86, 100, 44, 32], 0) := by rfl
theorem scanPage29 : scan cell29696.bytes ([32, 32, 68, 32, 58, 32, 98], 0) = ([41, 32, 64, 32, 48, 98, 48], 0) := by rfl
theorem scanPage30 : scan cell30720.bytes ([59, 10, 32, 32, 32, 32, 77], 0) = ([32, 32, 68, 32, 58, 32, 98], 0) := by rfl
theorem scanPage31 : scan cell31744.bytes ([58, 32, 98, 105, 116, 115, 40], 0) = ([59, 10, 32, 32, 32, 32, 77], 0) := by rfl
end Oak.ArmDecoderPartition.Data
