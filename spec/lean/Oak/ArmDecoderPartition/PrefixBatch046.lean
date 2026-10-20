import Oak.ArmDecoderPartition.PageBatch046
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage368 : scan cell376832.bytes ([32, 32, 32, 32, 86, 100, 32], 0) = ([101, 41, 32, 105, 102, 32, 83], 0) := by rfl
theorem scanPage369 : scan cell377856.bytes ([86, 109, 32, 58, 32, 98, 105], 0) = ([32, 32, 32, 32, 86, 100, 32], 0) := by rfl
theorem scanPage370 : scan cell378880.bytes ([32, 58, 32, 98, 105, 116, 115], 0) = ([86, 109, 32, 58, 32, 98, 105], 0) := by rfl
theorem scanPage371 : scan cell379904.bytes ([32, 61, 32, 111, 112, 95, 99], 0) = ([32, 58, 32, 98, 105, 116, 115], 0) := by rfl
theorem scanPage372 : scan cell380928.bytes ([69, 69, 32, 60, 32, 57, 55], 0) = ([32, 61, 32, 111, 112, 95, 99], 0) := by rfl
theorem scanPage373 : scan cell381952.bytes ([110, 32, 99, 108, 97, 117, 115], 0) = ([69, 69, 32, 60, 32, 57, 55], 0) := by rfl
theorem scanPage374 : scan cell382976.bytes ([32, 82, 100, 32, 58, 32, 98], 0) = ([110, 32, 99, 108, 97, 117, 115], 0) := by rfl
theorem scanPage375 : scan cell384000.bytes ([40, 41, 10, 125, 10, 10, 102], 0) = ([32, 82, 100, 32, 58, 32, 98], 0) := by rfl
end Oak.ArmDecoderPartition.Data
