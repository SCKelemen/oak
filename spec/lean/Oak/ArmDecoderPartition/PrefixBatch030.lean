import Oak.ArmDecoderPartition.PageBatch030
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage240 : scan cell245760.bytes ([115, 40, 53, 41, 32, 61, 32], 0) = ([32, 32, 32, 32, 81, 32, 58], 0) := by rfl
theorem scanPage241 : scan cell246784.bytes ([91, 111, 112, 95, 99, 111, 100], 0) = ([115, 40, 53, 41, 32, 61, 32], 0) := by rfl
theorem scanPage242 : scan cell247808.bytes ([99, 111, 100, 101, 91, 50, 50], 0) = ([91, 111, 112, 95, 99, 111, 100], 0) := by rfl
theorem scanPage243 : scan cell248832.bytes ([49, 41, 32, 61, 32, 91, 111], 0) = ([99, 111, 100, 101, 91, 50, 50], 0) := by rfl
theorem scanPage244 : scan cell249856.bytes ([58, 32, 98, 105, 116, 115, 40], 0) = ([49, 41, 32, 61, 32, 91, 111], 0) := by rfl
theorem scanPage245 : scan cell250880.bytes ([64, 32, 48, 98, 48, 49, 49], 0) = ([58, 32, 98, 105, 116, 115, 40], 0) := by rfl
theorem scanPage246 : scan cell251904.bytes ([99, 108, 97, 117, 115, 101, 32], 0) = ([64, 32, 48, 98, 48, 49, 49], 0) := by rfl
theorem scanPage247 : scan cell252928.bytes ([105, 116, 115, 40, 52, 41, 32], 0) = ([99, 108, 97, 117, 115, 101, 32], 0) := by rfl
end Oak.ArmDecoderPartition.Data
