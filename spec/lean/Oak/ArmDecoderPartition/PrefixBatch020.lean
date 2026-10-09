import Oak.ArmDecoderPartition.PageBatch020
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage160 : scan cell163840.bytes ([32, 32, 32, 32, 68, 32, 58], 0) = ([112, 44, 32, 82, 109, 41, 10], 0) := by rfl
theorem scanPage161 : scan cell164864.bytes ([61, 32, 111, 112, 95, 99, 111], 0) = ([32, 32, 32, 32, 68, 32, 58], 0) := by rfl
theorem scanPage162 : scan cell165888.bytes ([32, 32, 32, 68, 32, 58, 32], 0) = ([61, 32, 111, 112, 95, 99, 111], 0) := by rfl
theorem scanPage163 : scan cell166912.bytes ([100, 101, 91, 49, 57, 32, 46], 0) = ([32, 32, 32, 68, 32, 58, 32], 0) := by rfl
theorem scanPage164 : scan cell167936.bytes ([109, 109, 56, 32, 58, 32, 98], 0) = ([100, 101, 91, 49, 57, 32, 46], 0) := by rfl
theorem scanPage165 : scan cell168960.bytes ([32, 61, 32, 123, 10, 32, 32], 0) = ([109, 109, 56, 32, 58, 32, 98], 0) := by rfl
theorem scanPage166 : scan cell169984.bytes ([50, 41, 32, 61, 32, 111, 112], 0) = ([32, 61, 32, 123, 10, 32, 32], 0) := by rfl
theorem scanPage167 : scan cell171008.bytes ([32, 50, 56, 93, 59, 10, 32], 0) = ([50, 41, 32, 61, 32, 111, 112], 0) := by rfl
end Oak.ArmDecoderPartition.Data
