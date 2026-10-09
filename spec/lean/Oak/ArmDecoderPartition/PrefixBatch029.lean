import Oak.ArmDecoderPartition.PageBatch029
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage232 : scan cell237568.bytes ([49, 48, 32, 64, 32, 95, 32], 0) = ([32, 61, 32, 54, 49, 50, 59], 0) := by rfl
theorem scanPage233 : scan cell238592.bytes ([32, 98, 105, 116, 115, 40, 52], 0) = ([49, 48, 32, 64, 32, 95, 32], 0) := by rfl
theorem scanPage234 : scan cell239616.bytes ([32, 54, 50, 48, 59, 10, 32], 0) = ([32, 98, 105, 116, 115, 40, 52], 0) := by rfl
theorem scanPage235 : scan cell240640.bytes ([46, 46, 32, 49, 54, 93, 59], 0) = ([32, 54, 50, 48, 59, 10, 32], 0) := by rfl
theorem scanPage236 : scan cell241664.bytes ([69, 32, 61, 32, 54, 50, 54], 0) = ([46, 46, 32, 49, 54, 93, 59], 0) := by rfl
theorem scanPage237 : scan cell242688.bytes ([115, 40, 52, 41, 32, 64, 32], 0) = ([69, 32, 61, 32, 54, 50, 54], 0) := by rfl
theorem scanPage238 : scan cell243712.bytes ([61, 32, 91, 111, 112, 95, 99], 0) = ([115, 40, 52, 41, 32, 64, 32], 0) := by rfl
theorem scanPage239 : scan cell244736.bytes ([32, 32, 32, 32, 81, 32, 58], 0) = ([61, 32, 91, 111, 112, 95, 99], 0) := by rfl
end Oak.ArmDecoderPartition.Data
