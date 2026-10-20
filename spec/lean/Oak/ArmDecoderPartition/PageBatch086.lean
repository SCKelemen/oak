import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch043

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell704512 : Cell := ⟨Source.page688.take 332, 332, by simp only [List.length_take, List.length_drop, Source.size688] <;> rfl⟩
theorem gap704844 : (Source.page688.drop 332).take 1 = [10] := by rfl
def cell704845 : Cell := ⟨(Source.page688.drop 333).take 554, 554, by simp only [List.length_take, List.length_drop, Source.size688] <;> rfl⟩
theorem gap705399 : (Source.page688.drop 887).take 1 = [10] := by rfl
def cell705400 : Cell := ⟨(Source.page688.drop 888), 136, by simp only [List.length_take, List.length_drop, Source.size688] <;> rfl⟩
def coveredPage688 : Page := ⟨Source.page688, [cell704512, lf, cell704845, lf, cell705400], by
  have h := (cutBytes_cover [332, 1, 554, 1] Source.page688).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap704844, gap705399] at h
  exact h⟩
def cell705536 : Cell := ⟨Source.page689.take 284, 284, by simp only [List.length_take, List.length_drop, Source.size689] <;> rfl⟩
theorem gap705820 : (Source.page689.drop 284).take 1 = [10] := by rfl
def cell705821 : Cell := ⟨(Source.page689.drop 285).take 499, 499, by simp only [List.length_take, List.length_drop, Source.size689] <;> rfl⟩
theorem gap706320 : (Source.page689.drop 784).take 1 = [10] := by rfl
def cell706321 : Cell := ⟨(Source.page689.drop 785), 239, by simp only [List.length_take, List.length_drop, Source.size689] <;> rfl⟩
def coveredPage689 : Page := ⟨Source.page689, [cell705536, lf, cell705821, lf, cell706321], by
  have h := (cutBytes_cover [284, 1, 499, 1] Source.page689).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap705820, gap706320] at h
  exact h⟩
def cell706560 : Cell := ⟨Source.page690.take 149, 149, by simp only [List.length_take, List.length_drop, Source.size690] <;> rfl⟩
theorem gap706709 : (Source.page690.drop 149).take 1 = [10] := by rfl
def cell706710 : Cell := ⟨(Source.page690.drop 150).take 465, 465, by simp only [List.length_take, List.length_drop, Source.size690] <;> rfl⟩
theorem gap707175 : (Source.page690.drop 615).take 1 = [10] := by rfl
def cell707176 : Cell := ⟨(Source.page690.drop 616), 408, by simp only [List.length_take, List.length_drop, Source.size690] <;> rfl⟩
def coveredPage690 : Page := ⟨Source.page690, [cell706560, lf, cell706710, lf, cell707176], by
  have h := (cutBytes_cover [149, 1, 465, 1] Source.page690).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap706709, gap707175] at h
  exact h⟩
def cell707584 : Cell := ⟨Source.page691.take 51, 51, by simp only [List.length_take, List.length_drop, Source.size691] <;> rfl⟩
theorem gap707635 : (Source.page691.drop 51).take 1 = [10] := by rfl
def cell707636 : Cell := ⟨(Source.page691.drop 52).take 604, 604, by simp only [List.length_take, List.length_drop, Source.size691] <;> rfl⟩
theorem gap708240 : (Source.page691.drop 656).take 1 = [10] := by rfl
def cell708241 : Cell := ⟨(Source.page691.drop 657), 367, by simp only [List.length_take, List.length_drop, Source.size691] <;> rfl⟩
def coveredPage691 : Page := ⟨Source.page691, [cell707584, lf, cell707636, lf, cell708241], by
  have h := (cutBytes_cover [51, 1, 604, 1] Source.page691).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap707635, gap708240] at h
  exact h⟩
def cell708608 : Cell := ⟨Source.page692.take 27, 27, by simp only [List.length_take, List.length_drop, Source.size692] <;> rfl⟩
theorem gap708635 : (Source.page692.drop 27).take 1 = [10] := by rfl
def cell708636 : Cell := ⟨(Source.page692.drop 28).take 530, 530, by simp only [List.length_take, List.length_drop, Source.size692] <;> rfl⟩
theorem gap709166 : (Source.page692.drop 558).take 1 = [10] := by rfl
def cell709167 : Cell := ⟨(Source.page692.drop 559), 465, by simp only [List.length_take, List.length_drop, Source.size692] <;> rfl⟩
def coveredPage692 : Page := ⟨Source.page692, [cell708608, lf, cell708636, lf, cell709167], by
  have h := (cutBytes_cover [27, 1, 530, 1] Source.page692).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap708635, gap709166] at h
  exact h⟩
def cell709632 : Cell := ⟨Source.page693.take 107, 107, by simp only [List.length_take, List.length_drop, Source.size693] <;> rfl⟩
theorem gap709739 : (Source.page693.drop 107).take 1 = [10] := by rfl
def cell709740 : Cell := ⟨(Source.page693.drop 108).take 532, 532, by simp only [List.length_take, List.length_drop, Source.size693] <;> rfl⟩
theorem gap710272 : (Source.page693.drop 640).take 1 = [10] := by rfl
def cell710273 : Cell := ⟨(Source.page693.drop 641), 383, by simp only [List.length_take, List.length_drop, Source.size693] <;> rfl⟩
def coveredPage693 : Page := ⟨Source.page693, [cell709632, lf, cell709740, lf, cell710273], by
  have h := (cutBytes_cover [107, 1, 532, 1] Source.page693).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap709739, gap710272] at h
  exact h⟩
def cell710656 : Cell := ⟨Source.page694.take 108, 108, by simp only [List.length_take, List.length_drop, Source.size694] <;> rfl⟩
theorem gap710764 : (Source.page694.drop 108).take 1 = [10] := by rfl
def cell710765 : Cell := ⟨(Source.page694.drop 109).take 185, 185, by simp only [List.length_take, List.length_drop, Source.size694] <;> rfl⟩
theorem gap710950 : (Source.page694.drop 294).take 1 = [10] := by rfl
def cell710951 : Cell := ⟨(Source.page694.drop 295).take 374, 374, by simp only [List.length_take, List.length_drop, Source.size694] <;> rfl⟩
theorem gap711325 : (Source.page694.drop 669).take 1 = [10] := by rfl
def cell711326 : Cell := ⟨(Source.page694.drop 670), 354, by simp only [List.length_take, List.length_drop, Source.size694] <;> rfl⟩
def coveredPage694 : Page := ⟨Source.page694, [cell710656, lf, cell710765, lf, cell710951, lf, cell711326], by
  have h := (cutBytes_cover [108, 1, 185, 1, 374, 1] Source.page694).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap710764, gap710950, gap711325] at h
  exact h⟩
def cell711680 : Cell := ⟨Source.page695.take 129, 129, by simp only [List.length_take, List.length_drop, Source.size695] <;> rfl⟩
theorem gap711809 : (Source.page695.drop 129).take 1 = [10] := by rfl
def cell711810 : Cell := ⟨(Source.page695.drop 130).take 501, 501, by simp only [List.length_take, List.length_drop, Source.size695] <;> rfl⟩
theorem gap712311 : (Source.page695.drop 631).take 1 = [10] := by rfl
def cell712312 : Cell := ⟨(Source.page695.drop 632).take 294, 294, by simp only [List.length_take, List.length_drop, Source.size695] <;> rfl⟩
theorem gap712606 : (Source.page695.drop 926).take 1 = [10] := by rfl
def cell712607 : Cell := ⟨(Source.page695.drop 927), 97, by simp only [List.length_take, List.length_drop, Source.size695] <;> rfl⟩
def coveredPage695 : Page := ⟨Source.page695, [cell711680, lf, cell711810, lf, cell712312, lf, cell712607], by
  have h := (cutBytes_cover [129, 1, 501, 1, 294, 1] Source.page695).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap711809, gap712311, gap712606] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
