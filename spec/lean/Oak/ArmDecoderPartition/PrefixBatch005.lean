import Oak.ArmDecoderPartition.PageBatch005
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage40 : scan cell40960.bytes ([82, 109, 44, 32, 77, 44, 32], 0) = ([58, 32, 98, 105, 116, 115, 40], 0) := by rfl
theorem scanPage41 : scan cell41984.bytes ([110, 32, 99, 108, 97, 117, 115], 0) = ([82, 109, 44, 32, 77, 44, 32], 0) := by rfl
theorem scanPage42 : scan cell43008.bytes ([116, 115, 40, 49, 41, 32, 61], 0) = ([110, 32, 99, 108, 97, 117, 115], 0) := by rfl
theorem scanPage43 : scan cell44032.bytes ([52, 41, 32, 61, 32, 111, 112], 0) = ([116, 115, 40, 49, 41, 32, 61], 0) := by rfl
theorem scanPage44 : scan cell45056.bytes ([100, 44, 32, 116, 121, 112, 44], 0) = ([52, 41, 32, 61, 32, 111, 112], 0) := by rfl
theorem scanPage45 : scan cell46080.bytes ([100, 101, 91, 50, 50, 93, 93], 0) = ([100, 44, 32, 116, 121, 112, 44], 0) := by rfl
theorem scanPage46 : scan cell47104.bytes ([49, 49, 48, 49, 49, 49, 48], 0) = ([100, 101, 91, 50, 50, 93, 93], 0) := by rfl
theorem scanPage47 : scan cell48128.bytes ([69, 32, 61, 32, 49, 49, 55], 0) = ([49, 49, 48, 49, 49, 49, 48], 0) := by rfl
end Oak.ArmDecoderPartition.Data
