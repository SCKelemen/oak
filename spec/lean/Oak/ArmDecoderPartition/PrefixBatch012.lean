import Oak.ArmDecoderPartition.PageBatch012
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage96 : scan cell98304.bytes ([59, 10, 32, 32, 32, 32, 84], 0) = ([69, 32, 60, 32, 50, 52, 55], 0) := by rfl
theorem scanPage97 : scan cell99328.bytes ([82, 109, 32, 58, 32, 98, 105], 0) = ([59, 10, 32, 32, 32, 32, 84], 0) := by rfl
theorem scanPage98 : scan cell100352.bytes ([99, 111, 100, 101, 51, 50, 32], 0) = ([82, 109, 32, 58, 32, 98, 105], 0) := by rfl
theorem scanPage99 : scan cell101376.bytes ([111, 100, 101, 91, 49, 53, 32], 0) = ([99, 111, 100, 101, 51, 50, 32], 0) := by rfl
theorem scanPage100 : scan cell102400.bytes ([116, 115, 40, 52, 41, 32, 61], 0) = ([111, 100, 101, 91, 49, 53, 32], 0) := by rfl
theorem scanPage101 : scan cell103424.bytes ([46, 46, 32, 49, 50, 93, 59], 0) = ([116, 115, 40, 52, 41, 32, 61], 0) := by rfl
theorem scanPage102 : scan cell104448.bytes ([64, 32, 48, 98, 49, 48, 32], 0) = ([46, 46, 32, 49, 50, 93, 59], 0) := by rfl
theorem scanPage103 : scan cell105472.bytes ([49, 41, 32, 61, 32, 91, 111], 0) = ([64, 32, 48, 98, 49, 48, 32], 0) := by rfl
end Oak.ArmDecoderPartition.Data
