import Oak.ArmDecoderPartition.PageBatch045
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage360 : scan cell368640.bytes ([32, 32, 32, 32, 86, 76, 68], 0) = ([105, 116, 115, 40, 49, 41, 32], 0) := by rfl
theorem scanPage361 : scan cell369664.bytes ([40, 99, 111, 110, 100, 44, 32], 0) = ([32, 32, 32, 32, 86, 76, 68], 0) := by rfl
theorem scanPage362 : scan cell370688.bytes ([61, 32, 111, 112, 95, 99, 111], 0) = ([40, 99, 111, 110, 100, 44, 32], 0) := by rfl
theorem scanPage363 : scan cell371712.bytes ([32, 111, 112, 95, 99, 111, 100], 0) = ([61, 32, 111, 112, 95, 99, 111], 0) := by rfl
theorem scanPage364 : scan cell372736.bytes ([105, 111, 110, 32, 99, 108, 97], 0) = ([32, 111, 112, 95, 99, 111, 100], 0) := by rfl
theorem scanPage365 : scan cell373760.bytes ([91, 50, 32, 46, 46, 32, 48], 0) = ([105, 111, 110, 32, 99, 108, 97], 0) := by rfl
theorem scanPage366 : scan cell374784.bytes ([99, 111, 100, 101, 91, 49, 57], 0) = ([91, 50, 32, 46, 46, 32, 48], 0) := by rfl
theorem scanPage367 : scan cell375808.bytes ([101, 41, 32, 105, 102, 32, 83], 0) = ([99, 111, 100, 101, 91, 49, 57], 0) := by rfl
end Oak.ArmDecoderPartition.Data
