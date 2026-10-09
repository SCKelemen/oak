import Oak.ArmDecoderPartition.PageBatch035
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage280 : scan cell286720.bytes ([101, 32, 100, 101, 99, 111, 100], 0) = ([61, 32, 111, 112, 95, 99, 111], 0) := by rfl
theorem scanPage281 : scan cell287744.bytes ([115, 40, 49, 41, 32, 61, 32], 0) = ([101, 32, 100, 101, 99, 111, 100], 0) := by rfl
theorem scanPage282 : scan cell288768.bytes ([32, 32, 32, 32, 86, 81, 77], 0) = ([115, 40, 49, 41, 32, 61, 32], 0) := by rfl
theorem scanPage283 : scan cell289792.bytes ([61, 32, 111, 112, 95, 99, 111], 0) = ([32, 32, 32, 32, 86, 81, 77], 0) := by rfl
theorem scanPage284 : scan cell290816.bytes ([48, 98, 48, 32, 64, 32, 95], 0) = ([61, 32, 111, 112, 95, 99, 111], 0) := by rfl
theorem scanPage285 : scan cell291840.bytes ([58, 32, 98, 105, 116, 115, 40], 0) = ([48, 98, 48, 32, 64, 32, 95], 0) := by rfl
theorem scanPage286 : scan cell292864.bytes ([61, 32, 111, 112, 95, 99, 111], 0) = ([58, 32, 98, 105, 116, 115, 40], 0) := by rfl
theorem scanPage287 : scan cell293888.bytes ([10, 10, 102, 117, 110, 99, 116], 0) = ([61, 32, 111, 112, 95, 99, 111], 0) := by rfl
end Oak.ArmDecoderPartition.Data
