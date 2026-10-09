import Oak.ArmDecoderPartition.PageBatch025
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage200 : scan cell204800.bytes ([10, 32, 32, 32, 32, 78, 79], 0) = ([52, 41, 32, 61, 32, 111, 112], 0) := by rfl
theorem scanPage201 : scan cell205824.bytes ([68, 32, 58, 32, 98, 105, 116], 0) = ([10, 32, 32, 32, 32, 78, 79], 0) := by rfl
theorem scanPage202 : scan cell206848.bytes ([111, 112, 95, 99, 111, 100, 101], 0) = ([68, 32, 58, 32, 98, 105, 116], 0) := by rfl
theorem scanPage203 : scan cell207872.bytes ([32, 32, 32, 86, 100, 32, 58], 0) = ([111, 112, 95, 99, 111, 100, 101], 0) := by rfl
theorem scanPage204 : scan cell208896.bytes ([32, 64, 32, 95, 32, 58, 32], 0) = ([32, 32, 32, 86, 100, 32, 58], 0) := by rfl
theorem scanPage205 : scan cell209920.bytes ([10, 32, 32, 32, 32, 82, 109], 0) = ([32, 64, 32, 95, 32, 58, 32], 0) := by rfl
theorem scanPage206 : scan cell210944.bytes ([84, 50, 95, 65, 83, 95, 100], 0) = ([10, 32, 32, 32, 32, 82, 109], 0) := by rfl
theorem scanPage207 : scan cell211968.bytes ([77, 44, 32, 86, 109, 41, 10], 0) = ([84, 50, 95, 65, 83, 95, 100], 0) := by rfl
end Oak.ArmDecoderPartition.Data
