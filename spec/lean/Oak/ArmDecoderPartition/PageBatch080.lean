import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch040

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell655360 : Cell := ⟨Source.page640.take 210, 210, by simp only [List.length_take, List.length_drop, Source.size640] <;> rfl⟩
theorem gap655570 : (Source.page640.drop 210).take 1 = [10] := by rfl
def cell655571 : Cell := ⟨(Source.page640.drop 211).take 504, 504, by simp only [List.length_take, List.length_drop, Source.size640] <;> rfl⟩
theorem gap656075 : (Source.page640.drop 715).take 1 = [10] := by rfl
def cell656076 : Cell := ⟨(Source.page640.drop 716), 308, by simp only [List.length_take, List.length_drop, Source.size640] <;> rfl⟩
def coveredPage640 : Page := ⟨Source.page640, [cell655360, lf, cell655571, lf, cell656076], by
  have h := (cutBytes_cover [210, 1, 504, 1] Source.page640).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap655570, gap656075] at h
  exact h⟩
def cell656384 : Cell := ⟨Source.page641.take 288, 288, by simp only [List.length_take, List.length_drop, Source.size641] <;> rfl⟩
theorem gap656672 : (Source.page641.drop 288).take 1 = [10] := by rfl
def cell656673 : Cell := ⟨(Source.page641.drop 289).take 555, 555, by simp only [List.length_take, List.length_drop, Source.size641] <;> rfl⟩
theorem gap657228 : (Source.page641.drop 844).take 1 = [10] := by rfl
def cell657229 : Cell := ⟨(Source.page641.drop 845), 179, by simp only [List.length_take, List.length_drop, Source.size641] <;> rfl⟩
def coveredPage641 : Page := ⟨Source.page641, [cell656384, lf, cell656673, lf, cell657229], by
  have h := (cutBytes_cover [288, 1, 555, 1] Source.page641).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap656672, gap657228] at h
  exact h⟩
def cell657408 : Cell := ⟨Source.page642.take 318, 318, by simp only [List.length_take, List.length_drop, Source.size642] <;> rfl⟩
theorem gap657726 : (Source.page642.drop 318).take 1 = [10] := by rfl
def cell657727 : Cell := ⟨(Source.page642.drop 319).take 480, 480, by simp only [List.length_take, List.length_drop, Source.size642] <;> rfl⟩
theorem gap658207 : (Source.page642.drop 799).take 1 = [10] := by rfl
def cell658208 : Cell := ⟨(Source.page642.drop 800), 224, by simp only [List.length_take, List.length_drop, Source.size642] <;> rfl⟩
def coveredPage642 : Page := ⟨Source.page642, [cell657408, lf, cell657727, lf, cell658208], by
  have h := (cutBytes_cover [318, 1, 480, 1] Source.page642).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap657726, gap658207] at h
  exact h⟩
def cell658432 : Cell := ⟨Source.page643.take 300, 300, by simp only [List.length_take, List.length_drop, Source.size643] <;> rfl⟩
theorem gap658732 : (Source.page643.drop 300).take 1 = [10] := by rfl
def cell658733 : Cell := ⟨(Source.page643.drop 301).take 483, 483, by simp only [List.length_take, List.length_drop, Source.size643] <;> rfl⟩
theorem gap659216 : (Source.page643.drop 784).take 1 = [10] := by rfl
def cell659217 : Cell := ⟨(Source.page643.drop 785), 239, by simp only [List.length_take, List.length_drop, Source.size643] <;> rfl⟩
def coveredPage643 : Page := ⟨Source.page643, [cell658432, lf, cell658733, lf, cell659217], by
  have h := (cutBytes_cover [300, 1, 483, 1] Source.page643).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap658732, gap659216] at h
  exact h⟩
def cell659456 : Cell := ⟨Source.page644.take 238, 238, by simp only [List.length_take, List.length_drop, Source.size644] <;> rfl⟩
theorem gap659694 : (Source.page644.drop 238).take 1 = [10] := by rfl
def cell659695 : Cell := ⟨(Source.page644.drop 239).take 499, 499, by simp only [List.length_take, List.length_drop, Source.size644] <;> rfl⟩
theorem gap660194 : (Source.page644.drop 738).take 1 = [10] := by rfl
def cell660195 : Cell := ⟨(Source.page644.drop 739), 285, by simp only [List.length_take, List.length_drop, Source.size644] <;> rfl⟩
def coveredPage644 : Page := ⟨Source.page644, [cell659456, lf, cell659695, lf, cell660195], by
  have h := (cutBytes_cover [238, 1, 499, 1] Source.page644).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap659694, gap660194] at h
  exact h⟩
def cell660480 : Cell := ⟨Source.page645.take 180, 180, by simp only [List.length_take, List.length_drop, Source.size645] <;> rfl⟩
theorem gap660660 : (Source.page645.drop 180).take 1 = [10] := by rfl
def cell660661 : Cell := ⟨(Source.page645.drop 181).take 432, 432, by simp only [List.length_take, List.length_drop, Source.size645] <;> rfl⟩
theorem gap661093 : (Source.page645.drop 613).take 1 = [10] := by rfl
def cell661094 : Cell := ⟨(Source.page645.drop 614), 410, by simp only [List.length_take, List.length_drop, Source.size645] <;> rfl⟩
def coveredPage645 : Page := ⟨Source.page645, [cell660480, lf, cell660661, lf, cell661094], by
  have h := (cutBytes_cover [180, 1, 432, 1] Source.page645).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap660660, gap661093] at h
  exact h⟩
def cell661504 : Cell := ⟨Source.page646.take 14, 14, by simp only [List.length_take, List.length_drop, Source.size646] <;> rfl⟩
theorem gap661518 : (Source.page646.drop 14).take 1 = [10] := by rfl
def cell661519 : Cell := ⟨(Source.page646.drop 15).take 435, 435, by simp only [List.length_take, List.length_drop, Source.size646] <;> rfl⟩
theorem gap661954 : (Source.page646.drop 450).take 1 = [10] := by rfl
def cell661955 : Cell := ⟨(Source.page646.drop 451).take 478, 478, by simp only [List.length_take, List.length_drop, Source.size646] <;> rfl⟩
theorem gap662433 : (Source.page646.drop 929).take 1 = [10] := by rfl
def cell662434 : Cell := ⟨(Source.page646.drop 930), 94, by simp only [List.length_take, List.length_drop, Source.size646] <;> rfl⟩
def coveredPage646 : Page := ⟨Source.page646, [cell661504, lf, cell661519, lf, cell661955, lf, cell662434], by
  have h := (cutBytes_cover [14, 1, 435, 1, 478, 1] Source.page646).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap661518, gap661954, gap662433] at h
  exact h⟩
def cell662528 : Cell := ⟨Source.page647.take 337, 337, by simp only [List.length_take, List.length_drop, Source.size647] <;> rfl⟩
theorem gap662865 : (Source.page647.drop 337).take 1 = [10] := by rfl
def cell662866 : Cell := ⟨(Source.page647.drop 338).take 443, 443, by simp only [List.length_take, List.length_drop, Source.size647] <;> rfl⟩
theorem gap663309 : (Source.page647.drop 781).take 1 = [10] := by rfl
def cell663310 : Cell := ⟨(Source.page647.drop 782), 242, by simp only [List.length_take, List.length_drop, Source.size647] <;> rfl⟩
def coveredPage647 : Page := ⟨Source.page647, [cell662528, lf, cell662866, lf, cell663310], by
  have h := (cutBytes_cover [337, 1, 443, 1] Source.page647).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap662865, gap663309] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
