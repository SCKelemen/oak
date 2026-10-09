import Oak.ArmDecoderPartition.PageBatch040
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage320 : scan cell327680.bytes ([93, 93, 59, 10, 32, 32, 32], 0) = ([56, 93, 59, 10, 32, 32, 32], 0) := by rfl
theorem scanPage321 : scan cell328704.bytes ([101, 91, 49, 57, 32, 46, 46], 0) = ([93, 93, 59, 10, 32, 32, 32], 0) := by rfl
theorem scanPage322 : scan cell329728.bytes ([53, 49, 59, 10, 32, 32, 32], 0) = ([101, 91, 49, 57, 32, 46, 46], 0) := by rfl
theorem scanPage323 : scan cell330752.bytes ([48, 98, 48, 48, 48, 32, 64], 0) = ([53, 49, 59, 10, 32, 32, 32], 0) := by rfl
theorem scanPage324 : scan cell331776.bytes ([112, 95, 99, 111, 100, 101, 91], 0) = ([48, 98, 48, 48, 48, 32, 64], 0) := by rfl
theorem scanPage325 : scan cell332800.bytes ([68, 72, 78, 95, 84, 49, 65], 0) = ([112, 95, 99, 111, 100, 101, 91], 0) := by rfl
theorem scanPage326 : scan cell333824.bytes ([40, 52, 41, 32, 97, 115, 32], 0) = ([68, 72, 78, 95, 84, 49, 65], 0) := by rfl
theorem scanPage327 : scan cell334848.bytes ([58, 32, 98, 105, 116, 115, 40], 0) = ([40, 52, 41, 32, 97, 115, 32], 0) := by rfl
end Oak.ArmDecoderPartition.Data
