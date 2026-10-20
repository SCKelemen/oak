import Oak.ArmDecoderPartition.PageBatch036
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage288 : scan cell294912.bytes ([112, 95, 99, 111, 100, 101, 91], 0) = ([10, 10, 102, 117, 110, 99, 116], 0) := by rfl
theorem scanPage289 : scan cell295936.bytes ([116, 50, 44, 32, 105, 109, 109], 0) = ([112, 95, 99, 111, 100, 101, 91], 0) := by rfl
theorem scanPage290 : scan cell296960.bytes ([32, 46, 46, 32, 49, 50, 93], 0) = ([116, 50, 44, 32, 105, 109, 109], 0) := by rfl
theorem scanPage291 : scan cell297984.bytes ([116, 115, 40, 49, 49, 41, 32], 0) = ([32, 46, 46, 32, 49, 50, 93], 0) := by rfl
theorem scanPage292 : scan cell299008.bytes ([82, 110, 44, 32, 82, 100, 44], 0) = ([116, 115, 40, 49, 49, 41, 32], 0) := by rfl
theorem scanPage293 : scan cell300032.bytes ([41, 32, 61, 32, 111, 112, 95], 0) = ([82, 110, 44, 32, 82, 100, 44], 0) := by rfl
theorem scanPage294 : scan cell301056.bytes ([100, 101, 44, 32, 81, 44, 32], 0) = ([41, 32, 61, 32, 111, 112, 95], 0) := by rfl
theorem scanPage295 : scan cell302080.bytes ([32, 58, 32, 98, 105, 116, 115], 0) = ([100, 101, 44, 32, 81, 44, 32], 0) := by rfl
end Oak.ArmDecoderPartition.Data
