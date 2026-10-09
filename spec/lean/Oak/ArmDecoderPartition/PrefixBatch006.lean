import Oak.ArmDecoderPartition.PageBatch006
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage48 : scan cell49152.bytes ([95, 65, 95, 100, 101, 99, 111], 0) = ([69, 32, 61, 32, 49, 49, 55], 0) := by rfl
theorem scanPage49 : scan cell50176.bytes ([111, 100, 101, 40, 82, 110, 44], 0) = ([95, 65, 95, 100, 101, 99, 111], 0) := by rfl
theorem scanPage50 : scan cell51200.bytes ([111, 112, 95, 99, 111, 100, 101], 0) = ([111, 100, 101, 40, 82, 110, 44], 0) := by rfl
theorem scanPage51 : scan cell52224.bytes ([115, 40, 52, 41, 32, 61, 32], 0) = ([111, 112, 95, 99, 111, 100, 101], 0) := by rfl
theorem scanPage52 : scan cell53248.bytes ([65, 49, 95, 65, 95, 100, 101], 0) = ([115, 40, 52, 41, 32, 61, 32], 0) := by rfl
theorem scanPage53 : scan cell54272.bytes ([49, 49, 49, 49, 48, 48, 48], 0) = ([65, 49, 95, 65, 95, 100, 101], 0) := by rfl
theorem scanPage54 : scan cell55296.bytes ([105, 116, 115, 40, 49, 41, 32], 0) = ([49, 49, 49, 49, 48, 48, 48], 0) := by rfl
theorem scanPage55 : scan cell56320.bytes ([52, 93, 59, 10, 32, 32, 32], 0) = ([105, 116, 115, 40, 49, 41, 32], 0) := by rfl
end Oak.ArmDecoderPartition.Data
