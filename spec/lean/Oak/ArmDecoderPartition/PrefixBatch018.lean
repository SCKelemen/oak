import Oak.ArmDecoderPartition.PageBatch018
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage144 : scan cell147456.bytes ([41, 10, 125, 10, 10, 102, 117], 0) = ([32, 91, 111, 112, 95, 99, 111], 0) := by rfl
theorem scanPage145 : scan cell148480.bytes ([49, 49, 49, 49, 49, 48, 48], 0) = ([41, 10, 125, 10, 10, 102, 117], 0) := by rfl
theorem scanPage146 : scan cell149504.bytes ([48, 32, 64, 32, 95, 32, 58], 0) = ([49, 49, 49, 49, 49, 48, 48], 0) := by rfl
theorem scanPage147 : scan cell150528.bytes ([32, 111, 112, 95, 99, 111, 100], 0) = ([48, 32, 64, 32, 95, 32, 58], 0) := by rfl
theorem scanPage148 : scan cell151552.bytes ([78, 44, 32, 81, 44, 32, 77], 0) = ([32, 111, 112, 95, 99, 111, 100], 0) := by rfl
theorem scanPage149 : scan cell152576.bytes ([111, 100, 101, 91, 50, 32, 46], 0) = ([78, 44, 32, 81, 44, 32, 77], 0) := by rfl
theorem scanPage150 : scan cell153600.bytes ([91, 49, 57, 32, 46, 46, 32], 0) = ([111, 100, 101, 91, 50, 32, 46], 0) := by rfl
theorem scanPage151 : scan cell154624.bytes ([10, 32, 32, 32, 32, 86, 110], 0) = ([91, 49, 57, 32, 46, 46, 32], 0) := by rfl
end Oak.ArmDecoderPartition.Data
