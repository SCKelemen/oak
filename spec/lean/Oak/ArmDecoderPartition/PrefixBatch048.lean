import Oak.ArmDecoderPartition.PageBatch048
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage384 : scan cell393216.bytes ([95, 32, 58, 32, 98, 105, 116], 0) = ([101, 91, 51, 32, 46, 46, 32], 0) := by rfl
theorem scanPage385 : scan cell394240.bytes ([32, 111, 112, 95, 99, 111, 100], 0) = ([95, 32, 58, 32, 98, 105, 116], 0) := by rfl
theorem scanPage386 : scan cell395264.bytes ([10, 32, 32, 32, 32, 67, 77], 0) = ([32, 111, 112, 95, 99, 111, 100], 0) := by rfl
theorem scanPage387 : scan cell396288.bytes ([32, 116, 121, 112, 32, 58, 32], 0) = ([10, 32, 32, 32, 32, 67, 77], 0) := by rfl
theorem scanPage388 : scan cell397312.bytes ([51, 50, 32, 40, 40, 48, 98], 0) = ([32, 116, 121, 112, 32, 58, 32], 0) := by rfl
theorem scanPage389 : scan cell398336.bytes ([52, 41, 32, 97, 115, 32, 111], 0) = ([51, 50, 32, 40, 40, 48, 98], 0) := by rfl
theorem scanPage390 : scan cell399360.bytes ([111, 112, 95, 99, 111, 100, 101], 0) = ([52, 41, 32, 97, 115, 32, 111], 0) := by rfl
theorem scanPage391 : scan cell400384.bytes ([], 0) = ([111, 112, 95, 99, 111, 100, 101], 0) := by rfl
end Oak.ArmDecoderPartition.Data
