import Oak.ArmDecoderPartition.PageBatch014
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage112 : scan cell114688.bytes ([111, 112, 95, 99, 111, 100, 101], 0) = ([52, 41, 32, 61, 32, 111, 112], 0) := by rfl
theorem scanPage113 : scan cell115712.bytes ([61, 32, 123, 10, 32, 32, 32], 0) = ([111, 112, 95, 99, 111, 100, 101], 0) := by rfl
theorem scanPage114 : scan cell116736.bytes ([41, 32, 61, 32, 111, 112, 95], 0) = ([61, 32, 123, 10, 32, 32, 32], 0) := by rfl
theorem scanPage115 : scan cell117760.bytes ([32, 81, 44, 32, 77, 44, 32], 0) = ([41, 32, 61, 32, 111, 112, 95], 0) := by rfl
theorem scanPage116 : scan cell118784.bytes ([51, 48, 52, 41, 32, 61, 32], 0) = ([32, 81, 44, 32, 77, 44, 32], 0) := by rfl
theorem scanPage117 : scan cell119808.bytes ([48, 48, 48, 49, 49, 48, 49], 0) = ([51, 48, 52, 41, 32, 61, 32], 0) := by rfl
theorem scanPage118 : scan cell120832.bytes ([51, 48, 57, 41, 32, 61, 32], 0) = ([48, 48, 48, 49, 49, 48, 49], 0) := by rfl
theorem scanPage119 : scan cell121856.bytes ([105, 102, 32, 83, 69, 69, 32], 0) = ([51, 48, 57, 41, 32, 61, 32], 0) := by rfl
end Oak.ArmDecoderPartition.Data
