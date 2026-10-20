import Oak.ArmDecoderPartition.PageBatch013
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage104 : scan cell106496.bytes ([32, 32, 32, 115, 105, 122, 101], 0) = ([49, 41, 32, 61, 32, 91, 111], 0) := by rfl
theorem scanPage105 : scan cell107520.bytes ([101, 120, 95, 97, 108, 105, 103], 0) = ([32, 32, 32, 115, 105, 122, 101], 0) := by rfl
theorem scanPage106 : scan cell108544.bytes ([32, 95, 32, 58, 32, 98, 105], 0) = ([101, 120, 95, 97, 108, 105, 103], 0) := by rfl
theorem scanPage107 : scan cell109568.bytes ([49, 49, 49, 48, 48, 48, 48], 0) = ([32, 95, 32, 58, 32, 98, 105], 0) := by rfl
theorem scanPage108 : scan cell110592.bytes ([32, 98, 105, 116, 115, 40, 50], 0) = ([49, 49, 49, 48, 48, 48, 48], 0) := by rfl
theorem scanPage109 : scan cell111616.bytes ([48, 48, 32, 64, 32, 95, 32], 0) = ([32, 98, 105, 116, 115, 40, 50], 0) := by rfl
theorem scanPage110 : scan cell112640.bytes ([95, 99, 111, 100, 101, 91, 49], 0) = ([48, 48, 32, 64, 32, 95, 32], 0) := by rfl
theorem scanPage111 : scan cell113664.bytes ([52, 41, 32, 61, 32, 111, 112], 0) = ([95, 99, 111, 100, 101, 91, 49], 0) := by rfl
end Oak.ArmDecoderPartition.Data
