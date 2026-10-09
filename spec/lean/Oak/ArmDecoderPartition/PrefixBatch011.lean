import Oak.ArmDecoderPartition.PageBatch011
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage88 : scan cell90112.bytes ([10, 32, 32, 32, 32, 82, 109], 0) = ([32, 54, 93, 59, 10, 32, 32], 0) := by rfl
theorem scanPage89 : scan cell91136.bytes ([115, 101, 32, 100, 101, 99, 111], 0) = ([10, 32, 32, 32, 32, 82, 109], 0) := by rfl
theorem scanPage90 : scan cell92160.bytes ([32, 60, 32, 50, 51, 53, 41], 0) = ([115, 101, 32, 100, 101, 99, 111], 0) := by rfl
theorem scanPage91 : scan cell93184.bytes ([32, 91, 111, 112, 95, 99, 111], 0) = ([32, 60, 32, 50, 51, 53, 41], 0) := by rfl
theorem scanPage92 : scan cell94208.bytes ([32, 81, 32, 58, 32, 98, 105], 0) = ([32, 91, 111, 112, 95, 99, 111], 0) := by rfl
theorem scanPage93 : scan cell95232.bytes ([32, 32, 32, 32, 83, 32, 58], 0) = ([32, 81, 32, 58, 32, 98, 105], 0) := by rfl
theorem scanPage94 : scan cell96256.bytes ([32, 91, 111, 112, 95, 99, 111], 0) = ([32, 32, 32, 32, 83, 32, 58], 0) := by rfl
theorem scanPage95 : scan cell97280.bytes ([69, 32, 60, 32, 50, 52, 55], 0) = ([32, 91, 111, 112, 95, 99, 111], 0) := by rfl
end Oak.ArmDecoderPartition.Data
