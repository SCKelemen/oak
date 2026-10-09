import Oak.ArmDecoderPartition.PageBatch017
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage136 : scan cell139264.bytes ([32, 51, 93, 59, 10, 32, 32], 0) = ([83, 69, 69, 32, 61, 32, 51], 0) := by rfl
theorem scanPage137 : scan cell140288.bytes ([32, 111, 112, 95, 99, 111, 100], 0) = ([32, 51, 93, 59, 10, 32, 32], 0) := by rfl
theorem scanPage138 : scan cell141312.bytes ([100, 101, 99, 111, 100, 101, 51], 0) = ([32, 111, 112, 95, 99, 111, 100], 0) := by rfl
theorem scanPage139 : scan cell142336.bytes ([46, 32, 50, 56, 93, 59, 10], 0) = ([100, 101, 99, 111, 100, 101, 51], 0) := by rfl
theorem scanPage140 : scan cell143360.bytes ([49, 32, 64, 32, 95, 32, 58], 0) = ([46, 32, 50, 56, 93, 59, 10], 0) := by rfl
theorem scanPage141 : scan cell144384.bytes ([100, 101, 91, 49, 56, 32, 46], 0) = ([49, 32, 64, 32, 95, 32, 58], 0) := by rfl
theorem scanPage142 : scan cell145408.bytes ([32, 82, 100, 32, 58, 32, 98], 0) = ([100, 101, 91, 49, 56, 32, 46], 0) := by rfl
theorem scanPage143 : scan cell146432.bytes ([32, 91, 111, 112, 95, 99, 111], 0) = ([32, 82, 100, 32, 58, 32, 98], 0) := by rfl
end Oak.ArmDecoderPartition.Data
