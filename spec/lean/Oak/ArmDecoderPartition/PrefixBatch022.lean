import Oak.ArmDecoderPartition.PageBatch022
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage176 : scan cell180224.bytes ([93, 93, 59, 10, 32, 32, 32], 0) = ([98, 105, 116, 115, 40, 49, 41], 0) := by rfl
theorem scanPage177 : scan cell181248.bytes ([99, 111, 100, 101, 40, 68, 44], 0) = ([93, 93, 59, 10, 32, 32, 32], 0) := by rfl
theorem scanPage178 : scan cell182272.bytes ([68, 66, 95, 84, 49, 95, 65], 0) = ([99, 111, 100, 101, 40, 68, 44], 0) := by rfl
theorem scanPage179 : scan cell183296.bytes ([32, 52, 55, 50, 59, 10, 32], 0) = ([68, 66, 95, 84, 49, 95, 65], 0) := by rfl
theorem scanPage180 : scan cell184320.bytes ([46, 32, 48, 93, 59, 10, 32], 0) = ([32, 52, 55, 50, 59, 10, 32], 0) := by rfl
theorem scanPage181 : scan cell185344.bytes ([46, 32, 48, 93, 59, 10, 32], 0) = ([46, 32, 48, 93, 59, 10, 32], 0) := by rfl
theorem scanPage182 : scan cell186368.bytes ([32, 61, 32, 111, 112, 95, 99], 0) = ([46, 32, 48, 93, 59, 10, 32], 0) := by rfl
theorem scanPage183 : scan cell187392.bytes ([32, 98, 105, 116, 115, 40, 51], 0) = ([32, 61, 32, 111, 112, 95, 99], 0) := by rfl
end Oak.ArmDecoderPartition.Data
