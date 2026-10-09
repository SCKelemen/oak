import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch046

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell753664 : Cell := ⟨Source.page736.take 102, 102, by simp only [List.length_take, List.length_drop, Source.size736] <;> rfl⟩
theorem gap753766 : (Source.page736.drop 102).take 1 = [10] := by rfl
def cell753767 : Cell := ⟨(Source.page736.drop 103).take 499, 499, by simp only [List.length_take, List.length_drop, Source.size736] <;> rfl⟩
theorem gap754266 : (Source.page736.drop 602).take 1 = [10] := by rfl
def cell754267 : Cell := ⟨(Source.page736.drop 603), 421, by simp only [List.length_take, List.length_drop, Source.size736] <;> rfl⟩
def coveredPage736 : Page := ⟨Source.page736, [cell753664, lf, cell753767, lf, cell754267], by
  have h := (cutBytes_cover [102, 1, 499, 1] Source.page736).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap753766, gap754266] at h
  exact h⟩
def cell754688 : Cell := ⟨Source.page737.take 116, 116, by simp only [List.length_take, List.length_drop, Source.size737] <;> rfl⟩
theorem gap754804 : (Source.page737.drop 116).take 1 = [10] := by rfl
def cell754805 : Cell := ⟨(Source.page737.drop 117).take 459, 459, by simp only [List.length_take, List.length_drop, Source.size737] <;> rfl⟩
theorem gap755264 : (Source.page737.drop 576).take 1 = [10] := by rfl
def cell755265 : Cell := ⟨(Source.page737.drop 577), 447, by simp only [List.length_take, List.length_drop, Source.size737] <;> rfl⟩
def coveredPage737 : Page := ⟨Source.page737, [cell754688, lf, cell754805, lf, cell755265], by
  have h := (cutBytes_cover [116, 1, 459, 1] Source.page737).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap754804, gap755264] at h
  exact h⟩
def cell755712 : Cell := ⟨Source.page738.take 27, 27, by simp only [List.length_take, List.length_drop, Source.size738] <;> rfl⟩
theorem gap755739 : (Source.page738.drop 27).take 1 = [10] := by rfl
def cell755740 : Cell := ⟨(Source.page738.drop 28).take 398, 398, by simp only [List.length_take, List.length_drop, Source.size738] <;> rfl⟩
theorem gap756138 : (Source.page738.drop 426).take 1 = [10] := by rfl
def cell756139 : Cell := ⟨(Source.page738.drop 427).take 417, 417, by simp only [List.length_take, List.length_drop, Source.size738] <;> rfl⟩
theorem gap756556 : (Source.page738.drop 844).take 1 = [10] := by rfl
def cell756557 : Cell := ⟨(Source.page738.drop 845), 179, by simp only [List.length_take, List.length_drop, Source.size738] <;> rfl⟩
def coveredPage738 : Page := ⟨Source.page738, [cell755712, lf, cell755740, lf, cell756139, lf, cell756557], by
  have h := (cutBytes_cover [27, 1, 398, 1, 417, 1] Source.page738).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap755739, gap756138, gap756556] at h
  exact h⟩
def cell756736 : Cell := ⟨Source.page739.take 332, 332, by simp only [List.length_take, List.length_drop, Source.size739] <;> rfl⟩
theorem gap757068 : (Source.page739.drop 332).take 1 = [10] := by rfl
def cell757069 : Cell := ⟨(Source.page739.drop 333).take 447, 447, by simp only [List.length_take, List.length_drop, Source.size739] <;> rfl⟩
theorem gap757516 : (Source.page739.drop 780).take 1 = [10] := by rfl
def cell757517 : Cell := ⟨(Source.page739.drop 781), 243, by simp only [List.length_take, List.length_drop, Source.size739] <;> rfl⟩
def coveredPage739 : Page := ⟨Source.page739, [cell756736, lf, cell757069, lf, cell757517], by
  have h := (cutBytes_cover [332, 1, 447, 1] Source.page739).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap757068, gap757516] at h
  exact h⟩
def cell757760 : Cell := ⟨Source.page740.take 204, 204, by simp only [List.length_take, List.length_drop, Source.size740] <;> rfl⟩
theorem gap757964 : (Source.page740.drop 204).take 1 = [10] := by rfl
def cell757965 : Cell := ⟨(Source.page740.drop 205).take 413, 413, by simp only [List.length_take, List.length_drop, Source.size740] <;> rfl⟩
theorem gap758378 : (Source.page740.drop 618).take 1 = [10] := by rfl
def cell758379 : Cell := ⟨(Source.page740.drop 619).take 300, 300, by simp only [List.length_take, List.length_drop, Source.size740] <;> rfl⟩
theorem gap758679 : (Source.page740.drop 919).take 1 = [10] := by rfl
def cell758680 : Cell := ⟨(Source.page740.drop 920), 104, by simp only [List.length_take, List.length_drop, Source.size740] <;> rfl⟩
def coveredPage740 : Page := ⟨Source.page740, [cell757760, lf, cell757965, lf, cell758379, lf, cell758680], by
  have h := (cutBytes_cover [204, 1, 413, 1, 300, 1] Source.page740).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap757964, gap758378, gap758679] at h
  exact h⟩
def cell758784 : Cell := ⟨Source.page741.take 344, 344, by simp only [List.length_take, List.length_drop, Source.size741] <;> rfl⟩
theorem gap759128 : (Source.page741.drop 344).take 1 = [10] := by rfl
def cell759129 : Cell := ⟨(Source.page741.drop 345).take 532, 532, by simp only [List.length_take, List.length_drop, Source.size741] <;> rfl⟩
theorem gap759661 : (Source.page741.drop 877).take 1 = [10] := by rfl
def cell759662 : Cell := ⟨(Source.page741.drop 878), 146, by simp only [List.length_take, List.length_drop, Source.size741] <;> rfl⟩
def coveredPage741 : Page := ⟨Source.page741, [cell758784, lf, cell759129, lf, cell759662], by
  have h := (cutBytes_cover [344, 1, 532, 1] Source.page741).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap759128, gap759661] at h
  exact h⟩
def cell759808 : Cell := ⟨Source.page742.take 361, 361, by simp only [List.length_take, List.length_drop, Source.size742] <;> rfl⟩
theorem gap760169 : (Source.page742.drop 361).take 1 = [10] := by rfl
def cell760170 : Cell := ⟨(Source.page742.drop 362).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size742] <;> rfl⟩
theorem gap760650 : (Source.page742.drop 842).take 1 = [10] := by rfl
def cell760651 : Cell := ⟨(Source.page742.drop 843), 181, by simp only [List.length_take, List.length_drop, Source.size742] <;> rfl⟩
def coveredPage742 : Page := ⟨Source.page742, [cell759808, lf, cell760170, lf, cell760651], by
  have h := (cutBytes_cover [361, 1, 480, 1] Source.page742).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap760169, gap760650] at h
  exact h⟩
def cell760832 : Cell := ⟨Source.page743.take 350, 350, by simp only [List.length_take, List.length_drop, Source.size743] <;> rfl⟩
theorem gap761182 : (Source.page743.drop 350).take 1 = [10] := by rfl
def cell761183 : Cell := ⟨(Source.page743.drop 351).take 489, 489, by simp only [List.length_take, List.length_drop, Source.size743] <;> rfl⟩
theorem gap761672 : (Source.page743.drop 840).take 1 = [10] := by rfl
def cell761673 : Cell := ⟨(Source.page743.drop 841), 183, by simp only [List.length_take, List.length_drop, Source.size743] <;> rfl⟩
def coveredPage743 : Page := ⟨Source.page743, [cell760832, lf, cell761183, lf, cell761673], by
  have h := (cutBytes_cover [350, 1, 489, 1] Source.page743).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap761182, gap761672] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
