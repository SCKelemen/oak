import Oak.ArmDecoderPartition.PageBatch016
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage128 : scan cell131072.bytes ([115, 40, 52, 41, 32, 61, 32], 0) = ([95, 65, 95, 100, 101, 99, 111], 0) := by rfl
theorem scanPage129 : scan cell132096.bytes ([32, 85, 44, 32, 87, 44, 32], 0) = ([115, 40, 52, 41, 32, 61, 32], 0) := by rfl
theorem scanPage130 : scan cell133120.bytes ([10, 32, 32, 32, 32, 68, 32], 0) = ([32, 85, 44, 32, 87, 44, 32], 0) := by rfl
theorem scanPage131 : scan cell134144.bytes ([116, 105, 111, 110, 32, 99, 108], 0) = ([10, 32, 32, 32, 32, 68, 32], 0) := by rfl
theorem scanPage132 : scan cell135168.bytes ([83, 69, 69, 32, 61, 32, 51], 0) = ([116, 105, 111, 110, 32, 99, 108], 0) := by rfl
theorem scanPage133 : scan cell136192.bytes ([111, 100, 101, 91, 53, 93, 93], 0) = ([83, 69, 69, 32, 61, 32, 51], 0) := by rfl
theorem scanPage134 : scan cell137216.bytes ([41, 32, 64, 32, 48, 98, 48], 0) = ([111, 100, 101, 91, 53, 93, 93], 0) := by rfl
theorem scanPage135 : scan cell138240.bytes ([83, 69, 69, 32, 61, 32, 51], 0) = ([41, 32, 64, 32, 48, 98, 48], 0) := by rfl
end Oak.ArmDecoderPartition.Data
