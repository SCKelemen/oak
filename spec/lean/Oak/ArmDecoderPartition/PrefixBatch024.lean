import Oak.ArmDecoderPartition.PageBatch024
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage192 : scan cell196608.bytes ([101, 91, 53, 93, 93, 59, 10], 0) = ([10, 102, 117, 110, 99, 116, 105], 0) := by rfl
theorem scanPage193 : scan cell197632.bytes ([91, 53, 32, 46, 46, 32, 51], 0) = ([101, 91, 53, 93, 93, 59, 10], 0) := by rfl
theorem scanPage194 : scan cell198656.bytes ([41, 32, 61, 32, 111, 112, 95], 0) = ([91, 53, 32, 46, 46, 32, 51], 0) := by rfl
theorem scanPage195 : scan cell199680.bytes ([111, 112, 95, 99, 111, 100, 101], 0) = ([41, 32, 61, 32, 111, 112, 95], 0) := by rfl
theorem scanPage196 : scan cell200704.bytes ([101, 91, 55, 93, 93, 59, 10], 0) = ([111, 112, 95, 99, 111, 100, 101], 0) := by rfl
theorem scanPage197 : scan cell201728.bytes ([41, 32, 61, 32, 111, 112, 95], 0) = ([101, 91, 55, 93, 93, 59, 10], 0) := by rfl
theorem scanPage198 : scan cell202752.bytes ([32, 100, 101, 99, 111, 100, 101], 0) = ([41, 32, 61, 32, 111, 112, 95], 0) := by rfl
theorem scanPage199 : scan cell203776.bytes ([52, 41, 32, 61, 32, 111, 112], 0) = ([32, 100, 101, 99, 111, 100, 101], 0) := by rfl
end Oak.ArmDecoderPartition.Data
