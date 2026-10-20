import Oak.ArmDecoderPartition.PageBatch021
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage168 : scan cell172032.bytes ([32, 95, 32, 58, 32, 98, 105], 0) = ([32, 50, 56, 93, 59, 10, 32], 0) := by rfl
theorem scanPage169 : scan cell173056.bytes ([116, 115, 40, 52, 41, 32, 61], 0) = ([32, 95, 32, 58, 32, 98, 105], 0) := by rfl
theorem scanPage170 : scan cell174080.bytes ([125, 10, 10, 102, 117, 110, 99], 0) = ([116, 115, 40, 52, 41, 32, 61], 0) := by rfl
theorem scanPage171 : scan cell175104.bytes ([111, 100, 101, 51, 50, 32, 40], 0) = ([125, 10, 10, 102, 117, 110, 99], 0) := by rfl
theorem scanPage172 : scan cell176128.bytes ([10, 125, 10, 10, 102, 117, 110], 0) = ([111, 100, 101, 51, 50, 32, 40], 0) := by rfl
theorem scanPage173 : scan cell177152.bytes ([52, 41, 32, 61, 32, 111, 112], 0) = ([10, 125, 10, 10, 102, 117, 110], 0) := by rfl
theorem scanPage174 : scan cell178176.bytes ([32, 32, 32, 32, 70, 32, 58], 0) = ([52, 41, 32, 61, 32, 111, 112], 0) := by rfl
theorem scanPage175 : scan cell179200.bytes ([98, 105, 116, 115, 40, 49, 41], 0) = ([32, 32, 32, 32, 70, 32, 58], 0) := by rfl
end Oak.ArmDecoderPartition.Data
