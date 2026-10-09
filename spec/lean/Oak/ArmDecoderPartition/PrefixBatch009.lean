import Oak.ArmDecoderPartition.PageBatch009
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage72 : scan cell73728.bytes ([61, 32, 91, 111, 112, 95, 99], 0) = ([116, 115, 40, 53, 41, 32, 97], 0) := by rfl
theorem scanPage73 : scan cell74752.bytes ([32, 99, 108, 97, 117, 115, 101], 0) = ([61, 32, 91, 111, 112, 95, 99], 0) := by rfl
theorem scanPage74 : scan cell75776.bytes ([105, 109, 109, 52, 32, 58, 32], 0) = ([32, 99, 108, 97, 117, 115, 101], 0) := by rfl
theorem scanPage75 : scan cell76800.bytes ([32, 32, 105, 109, 109, 53, 32], 0) = ([105, 109, 109, 52, 32, 58, 32], 0) := by rfl
theorem scanPage76 : scan cell77824.bytes ([95, 32, 58, 32, 98, 105, 116], 0) = ([32, 32, 105, 109, 109, 53, 32], 0) := by rfl
theorem scanPage77 : scan cell78848.bytes ([99, 111, 100, 101, 91, 51, 49], 0) = ([95, 32, 58, 32, 98, 105, 116], 0) := by rfl
theorem scanPage78 : scan cell79872.bytes ([64, 32, 95, 32, 58, 32, 98], 0) = ([99, 111, 100, 101, 91, 51, 49], 0) := by rfl
theorem scanPage79 : scan cell80896.bytes ([112, 95, 99, 111, 100, 101, 91], 0) = ([64, 32, 95, 32, 58, 32, 98], 0) := by rfl
end Oak.ArmDecoderPartition.Data
