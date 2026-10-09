import Oak.ArmDecoderPartition.PageBatch015
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage120 : scan cell122880.bytes ([32, 32, 99, 111, 110, 100, 32], 0) = ([105, 102, 32, 83, 69, 69, 32], 0) := by rfl
theorem scanPage121 : scan cell123904.bytes ([32, 60, 32, 51, 49, 55, 41], 0) = ([32, 32, 99, 111, 110, 100, 32], 0) := by rfl
theorem scanPage122 : scan cell124928.bytes ([69, 32, 60, 32, 51, 49, 57], 0) = ([32, 60, 32, 51, 49, 55, 41], 0) := by rfl
theorem scanPage123 : scan cell125952.bytes ([59, 10, 32, 32, 32, 32, 82], 0) = ([69, 32, 60, 32, 51, 49, 57], 0) := by rfl
theorem scanPage124 : scan cell126976.bytes ([49, 49, 32, 46, 46, 32, 49], 0) = ([59, 10, 32, 32, 32, 32, 82], 0) := by rfl
theorem scanPage125 : scan cell128000.bytes ([101, 41, 32, 105, 102, 32, 83], 0) = ([49, 49, 32, 46, 46, 32, 49], 0) := by rfl
theorem scanPage126 : scan cell129024.bytes ([100, 44, 32, 116, 121, 112, 44], 0) = ([101, 41, 32, 105, 102, 32, 83], 0) := by rfl
theorem scanPage127 : scan cell130048.bytes ([95, 65, 95, 100, 101, 99, 111], 0) = ([100, 44, 32, 116, 121, 112, 44], 0) := by rfl
end Oak.ArmDecoderPartition.Data
