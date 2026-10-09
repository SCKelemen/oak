import Oak.ArmDecoderPartition.PageBatch043
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage344 : scan cell352256.bytes ([32, 111, 112, 95, 99, 111, 100], 0) = ([111, 100, 101, 41, 32, 105, 102], 0) := by rfl
theorem scanPage345 : scan cell353280.bytes ([86, 100, 44, 32, 115, 105, 122], 0) = ([32, 111, 112, 95, 99, 111, 100], 0) := by rfl
theorem scanPage346 : scan cell354304.bytes ([32, 32, 32, 105, 32, 58, 32], 0) = ([86, 100, 44, 32, 115, 105, 122], 0) := by rfl
theorem scanPage347 : scan cell355328.bytes ([49, 55, 32, 46, 46, 32, 49], 0) = ([32, 32, 32, 105, 32, 58, 32], 0) := by rfl
theorem scanPage348 : scan cell356352.bytes ([110, 99, 116, 105, 111, 110, 32], 0) = ([49, 55, 32, 46, 46, 32, 49], 0) := by rfl
theorem scanPage349 : scan cell357376.bytes ([52, 41, 32, 61, 32, 111, 112], 0) = ([110, 99, 116, 105, 111, 110, 32], 0) := by rfl
theorem scanPage350 : scan cell358400.bytes ([98, 105, 116, 115, 40, 49, 41], 0) = ([52, 41, 32, 61, 32, 111, 112], 0) := by rfl
theorem scanPage351 : scan cell359424.bytes ([32, 98, 105, 116, 115, 40, 50], 0) = ([98, 105, 116, 115, 40, 49, 41], 0) := by rfl
end Oak.ArmDecoderPartition.Data
