import Oak.ArmDecoderPartition.PageBatch010
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage80 : scan cell81920.bytes ([46, 32, 49, 54, 93, 59, 10], 0) = ([112, 95, 99, 111, 100, 101, 91], 0) := by rfl
theorem scanPage81 : scan cell82944.bytes ([115, 40, 50, 41, 32, 61, 32], 0) = ([46, 32, 49, 54, 93, 59, 10], 0) := by rfl
theorem scanPage82 : scan cell83968.bytes ([32, 32, 32, 32, 111, 112, 32], 0) = ([115, 40, 50, 41, 32, 61, 32], 0) := by rfl
theorem scanPage83 : scan cell84992.bytes ([69, 32, 61, 32, 50, 49, 55], 0) = ([32, 32, 32, 32, 111, 112, 32], 0) := by rfl
theorem scanPage84 : scan cell86016.bytes ([100, 101, 91, 50, 52, 93, 93], 0) = ([69, 32, 61, 32, 50, 49, 55], 0) := by rfl
theorem scanPage85 : scan cell87040.bytes ([41, 32, 97, 115, 32, 111, 112], 0) = ([100, 101, 91, 50, 52, 93, 93], 0) := by rfl
theorem scanPage86 : scan cell88064.bytes ([59, 10, 32, 32, 32, 32, 81], 0) = ([41, 32, 97, 115, 32, 111, 112], 0) := by rfl
theorem scanPage87 : scan cell89088.bytes ([32, 54, 93, 59, 10, 32, 32], 0) = ([59, 10, 32, 32, 32, 32, 81], 0) := by rfl
end Oak.ArmDecoderPartition.Data
