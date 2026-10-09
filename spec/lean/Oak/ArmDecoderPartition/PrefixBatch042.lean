import Oak.ArmDecoderPartition.PageBatch042
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage336 : scan cell344064.bytes ([111, 100, 101, 41, 32, 105, 102], 0) = ([50, 93, 59, 10, 32, 32, 32], 0) := by rfl
theorem scanPage337 : scan cell345088.bytes ([61, 32, 91, 111, 112, 95, 99], 0) = ([111, 100, 101, 41, 32, 105, 102], 0) := by rfl
theorem scanPage338 : scan cell346112.bytes ([41, 32, 64, 32, 48, 98, 49], 0) = ([61, 32, 91, 111, 112, 95, 99], 0) := by rfl
theorem scanPage339 : scan cell347136.bytes ([32, 98, 105, 116, 115, 40, 52], 0) = ([41, 32, 64, 32, 48, 98, 49], 0) := by rfl
theorem scanPage340 : scan cell348160.bytes ([61, 32, 111, 112, 95, 99, 111], 0) = ([32, 98, 105, 116, 115, 40, 52], 0) := by rfl
theorem scanPage341 : scan cell349184.bytes ([95, 99, 111, 100, 101, 91, 53], 0) = ([61, 32, 111, 112, 95, 99, 111], 0) := by rfl
theorem scanPage342 : scan cell350208.bytes ([98, 105, 116, 115, 40, 49, 41], 0) = ([95, 99, 111, 100, 101, 91, 53], 0) := by rfl
theorem scanPage343 : scan cell351232.bytes ([111, 100, 101, 41, 32, 105, 102], 0) = ([98, 105, 116, 115, 40, 49, 41], 0) := by rfl
end Oak.ArmDecoderPartition.Data
