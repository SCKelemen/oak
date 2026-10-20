import Oak.ArmDecoderPartition.PageBatch004
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage32 : scan cell32768.bytes ([32, 55, 55, 59, 10, 32, 32], 0) = ([58, 32, 98, 105, 116, 115, 40], 0) := by rfl
theorem scanPage33 : scan cell33792.bytes ([40, 52, 41, 32, 61, 32, 111], 0) = ([32, 55, 55, 59, 10, 32, 32], 0) := by rfl
theorem scanPage34 : scan cell34816.bytes ([99, 108, 97, 117, 115, 101, 32], 0) = ([40, 52, 41, 32, 61, 32, 111], 0) := by rfl
theorem scanPage35 : scan cell35840.bytes ([44, 32, 82, 116, 44, 32, 105], 0) = ([99, 108, 97, 117, 115, 101, 32], 0) := by rfl
theorem scanPage36 : scan cell36864.bytes ([52, 41, 32, 61, 32, 111, 112], 0) = ([44, 32, 82, 116, 44, 32, 105], 0) := by rfl
theorem scanPage37 : scan cell37888.bytes ([93, 59, 10, 32, 32, 32, 32], 0) = ([52, 41, 32, 61, 32, 111, 112], 0) := by rfl
theorem scanPage38 : scan cell38912.bytes ([56, 41, 32, 64, 32, 48, 98], 0) = ([93, 59, 10, 32, 32, 32, 32], 0) := by rfl
theorem scanPage39 : scan cell39936.bytes ([58, 32, 98, 105, 116, 115, 40], 0) = ([56, 41, 32, 64, 32, 48, 98], 0) := by rfl
end Oak.ArmDecoderPartition.Data
