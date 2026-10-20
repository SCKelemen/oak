import Oak.ArmDecoderPartition.PageBatch032
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage256 : scan cell262144.bytes ([49, 49, 32, 46, 46, 32, 56], 0) = ([41, 32, 97, 115, 32, 111, 112], 0) := by rfl
theorem scanPage257 : scan cell263168.bytes ([10, 32, 32, 32, 32, 83, 69], 0) = ([49, 49, 32, 46, 46, 32, 56], 0) := by rfl
theorem scanPage258 : scan cell264192.bytes ([112, 95, 99, 111, 100, 101, 91], 0) = ([10, 32, 32, 32, 32, 83, 69], 0) := by rfl
theorem scanPage259 : scan cell265216.bytes ([48, 32, 64, 32, 95, 32, 58], 0) = ([112, 95, 99, 111, 100, 101, 91], 0) := by rfl
theorem scanPage260 : scan cell266240.bytes ([54, 56, 55, 41, 32, 61, 32], 0) = ([48, 32, 64, 32, 95, 32, 58], 0) := by rfl
theorem scanPage261 : scan cell267264.bytes ([32, 95, 32, 58, 32, 98, 105], 0) = ([54, 56, 55, 41, 32, 61, 32], 0) := by rfl
theorem scanPage262 : scan cell268288.bytes ([61, 32, 123, 10, 32, 32, 32], 0) = ([32, 95, 32, 58, 32, 98, 105], 0) := by rfl
theorem scanPage263 : scan cell269312.bytes ([49, 48, 48, 49, 48, 32, 64], 0) = ([61, 32, 123, 10, 32, 32, 32], 0) := by rfl
end Oak.ArmDecoderPartition.Data
