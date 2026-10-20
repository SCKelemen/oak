import Oak.ArmDecoderPartition.PageBatch001
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage8 : scan cell8192.bytes ([111, 100, 101, 41, 32, 105, 102], 0) = ([111, 112, 95, 99, 111, 100, 101], 0) := by rfl
theorem scanPage9 : scan cell9216.bytes ([84, 49, 65, 49, 95, 65, 95], 0) = ([111, 100, 101, 41, 32, 105, 102], 0) := by rfl
theorem scanPage10 : scan cell10240.bytes ([32, 32, 32, 32, 116, 121, 112], 0) = ([84, 49, 65, 49, 95, 65, 95], 0) := by rfl
theorem scanPage11 : scan cell11264.bytes ([55, 93, 93, 59, 10, 32, 32], 0) = ([32, 32, 32, 32, 116, 121, 112], 0) := by rfl
theorem scanPage12 : scan cell12288.bytes ([50, 53, 59, 10, 32, 32, 32], 0) = ([55, 93, 93, 59, 10, 32, 32], 0) := by rfl
theorem scanPage13 : scan cell13312.bytes ([44, 32, 83, 44, 32, 82, 100], 0) = ([50, 53, 59, 10, 32, 32, 32], 0) := by rfl
theorem scanPage14 : scan cell14336.bytes ([55, 32, 46, 46, 32, 48, 93], 0) = ([44, 32, 83, 44, 32, 82, 100], 0) := by rfl
theorem scanPage15 : scan cell15360.bytes ([100, 101, 99, 111, 100, 101, 40], 0) = ([55, 32, 46, 46, 32, 48, 93], 0) := by rfl
end Oak.ArmDecoderPartition.Data
