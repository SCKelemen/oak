import Oak.ArmDecoderPartition.PageBatch031
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage248 : scan cell253952.bytes ([99, 111, 100, 101, 91, 50, 48], 0) = ([105, 116, 115, 40, 52, 41, 32], 0) := by rfl
theorem scanPage249 : scan cell254976.bytes ([32, 86, 109, 32, 58, 32, 98], 0) = ([99, 111, 100, 101, 91, 50, 48], 0) := by rfl
theorem scanPage250 : scan cell256000.bytes ([58, 32, 98, 105, 116, 115, 40], 0) = ([32, 86, 109, 32, 58, 32, 98], 0) := by rfl
theorem scanPage251 : scan cell257024.bytes ([105, 116, 115, 40, 52, 41, 32], 0) = ([58, 32, 98, 105, 116, 115, 40], 0) := by rfl
theorem scanPage252 : scan cell258048.bytes ([99, 111, 100, 101, 91, 49, 49], 0) = ([105, 116, 115, 40, 52, 41, 32], 0) := by rfl
theorem scanPage253 : scan cell259072.bytes ([101, 99, 111, 100, 101, 40, 68], 0) = ([99, 111, 100, 101, 91, 49, 49], 0) := by rfl
theorem scanPage254 : scan cell260096.bytes ([84, 51, 95, 49, 95, 84, 50], 0) = ([101, 99, 111, 100, 101, 40, 68], 0) := by rfl
theorem scanPage255 : scan cell261120.bytes ([41, 32, 97, 115, 32, 111, 112], 0) = ([84, 51, 95, 49, 95, 84, 50], 0) := by rfl
end Oak.ArmDecoderPartition.Data
