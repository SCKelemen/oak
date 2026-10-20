import Oak.ArmDecoderPartition.PageBatch033
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage264 : scan cell270336.bytes ([95, 99, 111, 100, 101, 91, 49], 0) = ([49, 48, 48, 49, 48, 32, 64], 0) := by rfl
theorem scanPage265 : scan cell271360.bytes ([32, 32, 32, 86, 110, 32, 58], 0) = ([95, 99, 111, 100, 101, 91, 49], 0) := by rfl
theorem scanPage266 : scan cell272384.bytes ([10, 32, 32, 32, 32, 115, 105], 0) = ([32, 32, 32, 86, 110, 32, 58], 0) := by rfl
theorem scanPage267 : scan cell273408.bytes ([46, 32, 52, 93, 59, 10, 32], 0) = ([10, 32, 32, 32, 32, 115, 105], 0) := by rfl
theorem scanPage268 : scan cell274432.bytes ([44, 32, 82, 100, 44, 32, 82], 0) = ([46, 32, 52, 93, 59, 10, 32], 0) := by rfl
theorem scanPage269 : scan cell275456.bytes ([99, 111, 100, 101, 40, 68, 44], 0) = ([44, 32, 82, 100, 44, 32, 82], 0) := by rfl
theorem scanPage270 : scan cell276480.bytes ([10, 32, 32, 32, 32, 82, 110], 0) = ([99, 111, 100, 101, 40, 68, 44], 0) := by rfl
theorem scanPage271 : scan cell277504.bytes ([76, 68, 65, 69, 88, 95, 84], 0) = ([10, 32, 32, 32, 32, 82, 110], 0) := by rfl
end Oak.ArmDecoderPartition.Data
