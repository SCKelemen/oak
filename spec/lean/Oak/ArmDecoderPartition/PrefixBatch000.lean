import Oak.ArmDecoderPartition.PageBatch000
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage0 : scan cell0.bytes ([32, 32, 32, 32, 32, 32, 32], 1) = ([47, 42, 42, 42, 42, 42, 42], 1) := by rfl
theorem scanPage1 : scan cell1024.bytes ([99, 116, 115, 32, 32, 32, 32], 1) = ([32, 32, 32, 32, 32, 32, 32], 1) := by rfl
theorem scanPage2 : scan cell2048.bytes ([69, 82, 32, 73, 78, 32, 67], 1) = ([99, 116, 115, 32, 32, 32, 32], 1) := by rfl
theorem scanPage3 : scan cell3072.bytes ([32, 32, 83, 69, 69, 32, 61], 0) = ([69, 82, 32, 73, 78, 32, 67], 1) := by rfl
theorem scanPage4 : scan cell4096.bytes ([41, 10, 125, 10, 10, 102, 117], 0) = ([32, 32, 83, 69, 69, 32, 61], 0) := by rfl
theorem scanPage5 : scan cell5120.bytes ([58, 32, 98, 105, 116, 115, 40], 0) = ([41, 10, 125, 10, 10, 102, 117], 0) := by rfl
theorem scanPage6 : scan cell6144.bytes ([49, 112, 114, 101, 95, 65, 95], 0) = ([58, 32, 98, 105, 116, 115, 40], 0) := by rfl
theorem scanPage7 : scan cell7168.bytes ([111, 112, 95, 99, 111, 100, 101], 0) = ([49, 112, 114, 101, 95, 65, 95], 0) := by rfl
end Oak.ArmDecoderPartition.Data
