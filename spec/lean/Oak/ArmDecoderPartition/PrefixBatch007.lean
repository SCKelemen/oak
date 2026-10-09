import Oak.ArmDecoderPartition.PageBatch007
import Oak.ArmDecoderPartition.Prefix

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
theorem scanPage56 : scan cell57344.bytes ([32, 95, 32, 58, 32, 98, 105], 0) = ([52, 93, 59, 10, 32, 32, 32], 0) := by rfl
theorem scanPage57 : scan cell58368.bytes ([61, 32, 111, 112, 95, 99, 111], 0) = ([32, 95, 32, 58, 32, 98, 105], 0) := by rfl
theorem scanPage58 : scan cell59392.bytes ([100, 101, 91, 53, 93, 93, 59], 0) = ([61, 32, 111, 112, 95, 99, 111], 0) := by rfl
theorem scanPage59 : scan cell60416.bytes ([98, 49, 49, 49, 49, 48, 48], 0) = ([100, 101, 91, 53, 93, 93, 59], 0) := by rfl
theorem scanPage60 : scan cell61440.bytes ([32, 32, 32, 78, 32, 58, 32], 0) = ([98, 49, 49, 49, 49, 48, 48], 0) := by rfl
theorem scanPage61 : scan cell62464.bytes ([64, 32, 95, 32, 58, 32, 98], 0) = ([32, 32, 32, 78, 32, 58, 32], 0) := by rfl
theorem scanPage62 : scan cell63488.bytes ([32, 100, 101, 99, 111, 100, 101], 0) = ([64, 32, 95, 32, 58, 32, 98], 0) := by rfl
theorem scanPage63 : scan cell64512.bytes ([53, 57, 59, 10, 32, 32, 32], 0) = ([32, 100, 101, 99, 111, 100, 101], 0) := by rfl
end Oak.ArmDecoderPartition.Data
