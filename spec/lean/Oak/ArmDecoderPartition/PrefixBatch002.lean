import Oak.ArmDecoderPartition.PageBatch002
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage16 : scan cell16384.bytes ([95, 32, 58, 32, 98, 105, 116], 0) = ([100, 101, 99, 111, 100, 101, 40], 0) := by rfl
theorem scanPage17 : scan cell17408.bytes ([61, 32, 91, 111, 112, 95, 99], 0) = ([95, 32, 58, 32, 98, 105, 116], 0) := by rfl
theorem scanPage18 : scan cell18432.bytes ([49, 49, 49, 49, 49, 48, 48], 0) = ([61, 32, 91, 111, 112, 95, 99], 0) := by rfl
theorem scanPage19 : scan cell19456.bytes ([69, 32, 61, 32, 52, 52, 59], 0) = ([49, 49, 49, 49, 49, 48, 48], 0) := by rfl
theorem scanPage20 : scan cell20480.bytes ([111, 112, 95, 99, 111, 100, 101], 0) = ([69, 32, 61, 32, 52, 52, 59], 0) := by rfl
theorem scanPage21 : scan cell21504.bytes ([48, 49, 48, 48, 32, 64, 32], 0) = ([111, 112, 95, 99, 111, 100, 101], 0) := by rfl
theorem scanPage22 : scan cell22528.bytes ([58, 32, 98, 105, 116, 115, 40], 0) = ([48, 49, 48, 48, 32, 64, 32], 0) := by rfl
theorem scanPage23 : scan cell23552.bytes ([10, 32, 32, 32, 32, 105, 109], 0) = ([58, 32, 98, 105, 116, 115, 40], 0) := by rfl
end Oak.ArmDecoderPartition.Data
