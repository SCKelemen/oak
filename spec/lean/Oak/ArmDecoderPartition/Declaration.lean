import Oak.ArmDecoderPartition.SourceBatch000
import Oak.ArmDecoderPartition.PageBatch048

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def declaration : Bytes := rawBytes
  ["\nval decode64 : bits(32) -> unit ", "effect {configuration, escape, ",
   "undef, wreg, rreg, rmem, wmem}\n"]

theorem declaration_at : (Source.page3.drop 415).take 95 = declaration := by rfl

theorem declaration_in_page : declaration <:+: Source.page3 := by
  rw [← declaration_at]
  exact (List.take_prefix 95 (Source.page3.drop 415)).isInfix.trans
    (List.drop_suffix 415 Source.page3).isInfix

theorem prefix_last_lf : ([10] : Bytes) <:+ cell400384.bytes := by
  exact ⟨cell400384.bytes.take 590, by rfl⟩

end Oak.ArmDecoderPartition.Data
