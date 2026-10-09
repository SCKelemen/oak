import Oak.ArmDecoderPartition.PageBatch008
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage64 : scan cell65536.bytes ([91, 111, 112, 95, 99, 111, 100], 0) = ([53, 57, 59, 10, 32, 32, 32], 0) := by rfl
theorem scanPage65 : scan cell66560.bytes ([32, 61, 32, 49, 54, 54, 59], 0) = ([91, 111, 112, 95, 99, 111, 100], 0) := by rfl
theorem scanPage66 : scan cell67584.bytes ([101, 40, 68, 44, 32, 86, 110], 0) = ([32, 61, 32, 49, 54, 54, 59], 0) := by rfl
theorem scanPage67 : scan cell68608.bytes ([52, 41, 32, 64, 32, 48, 98], 0) = ([101, 40, 68, 44, 32, 86, 110], 0) := by rfl
theorem scanPage68 : scan cell69632.bytes ([32, 32, 32, 32, 86, 82, 73], 0) = ([52, 41, 32, 64, 32, 48, 98], 0) := by rfl
theorem scanPage69 : scan cell70656.bytes ([40, 40, 95, 32, 58, 32, 98], 0) = ([32, 32, 32, 32, 86, 82, 73], 0) := by rfl
theorem scanPage70 : scan cell71680.bytes ([40, 52, 41, 32, 61, 32, 111], 0) = ([40, 40, 95, 32, 58, 32, 98], 0) := by rfl
theorem scanPage71 : scan cell72704.bytes ([116, 115, 40, 53, 41, 32, 97], 0) = ([40, 52, 41, 32, 61, 32, 111], 0) := by rfl
end Oak.ArmDecoderPartition.Data
