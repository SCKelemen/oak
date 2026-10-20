import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch045

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell737280 : Cell := ⟨Source.page720.take 365, 365, by simp only [List.length_take, List.length_drop, Source.size720] <;> rfl⟩
theorem gap737645 : (Source.page720.drop 365).take 1 = [10] := by rfl
def cell737646 : Cell := ⟨(Source.page720.drop 366).take 396, 396, by simp only [List.length_take, List.length_drop, Source.size720] <;> rfl⟩
theorem gap738042 : (Source.page720.drop 762).take 1 = [10] := by rfl
def cell738043 : Cell := ⟨(Source.page720.drop 763), 261, by simp only [List.length_take, List.length_drop, Source.size720] <;> rfl⟩
def coveredPage720 : Page := ⟨Source.page720, [cell737280, lf, cell737646, lf, cell738043], by
  have h := (cutBytes_cover [365, 1, 396, 1] Source.page720).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap737645, gap738042] at h
  exact h⟩
def cell738304 : Cell := ⟨Source.page721.take 213, 213, by simp only [List.length_take, List.length_drop, Source.size721] <;> rfl⟩
theorem gap738517 : (Source.page721.drop 213).take 1 = [10] := by rfl
def cell738518 : Cell := ⟨(Source.page721.drop 214).take 407, 407, by simp only [List.length_take, List.length_drop, Source.size721] <;> rfl⟩
theorem gap738925 : (Source.page721.drop 621).take 1 = [10] := by rfl
def cell738926 : Cell := ⟨(Source.page721.drop 622), 402, by simp only [List.length_take, List.length_drop, Source.size721] <;> rfl⟩
def coveredPage721 : Page := ⟨Source.page721, [cell738304, lf, cell738518, lf, cell738926], by
  have h := (cutBytes_cover [213, 1, 407, 1] Source.page721).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap738517, gap738925] at h
  exact h⟩
def cell739328 : Cell := ⟨Source.page722.take 60, 60, by simp only [List.length_take, List.length_drop, Source.size722] <;> rfl⟩
theorem gap739388 : (Source.page722.drop 60).take 1 = [10] := by rfl
def cell739389 : Cell := ⟨(Source.page722.drop 61).take 444, 444, by simp only [List.length_take, List.length_drop, Source.size722] <;> rfl⟩
theorem gap739833 : (Source.page722.drop 505).take 1 = [10] := by rfl
def cell739834 : Cell := ⟨(Source.page722.drop 506), 518, by simp only [List.length_take, List.length_drop, Source.size722] <;> rfl⟩
def coveredPage722 : Page := ⟨Source.page722, [cell739328, lf, cell739389, lf, cell739834], by
  have h := (cutBytes_cover [60, 1, 444, 1] Source.page722).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap739388, gap739833] at h
  exact h⟩
def cell740352 : Cell := ⟨Source.page723.take 29, 29, by simp only [List.length_take, List.length_drop, Source.size723] <;> rfl⟩
theorem gap740381 : (Source.page723.drop 29).take 1 = [10] := by rfl
def cell740382 : Cell := ⟨(Source.page723.drop 30).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size723] <;> rfl⟩
theorem gap740853 : (Source.page723.drop 501).take 1 = [10] := by rfl
def cell740854 : Cell := ⟨(Source.page723.drop 502).take 335, 335, by simp only [List.length_take, List.length_drop, Source.size723] <;> rfl⟩
theorem gap741189 : (Source.page723.drop 837).take 1 = [10] := by rfl
def cell741190 : Cell := ⟨(Source.page723.drop 838), 186, by simp only [List.length_take, List.length_drop, Source.size723] <;> rfl⟩
def coveredPage723 : Page := ⟨Source.page723, [cell740352, lf, cell740382, lf, cell740854, lf, cell741190], by
  have h := (cutBytes_cover [29, 1, 471, 1, 335, 1] Source.page723).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap740381, gap740853, gap741189] at h
  exact h⟩
def cell741376 : Cell := ⟨Source.page724.take 241, 241, by simp only [List.length_take, List.length_drop, Source.size724] <;> rfl⟩
theorem gap741617 : (Source.page724.drop 241).take 1 = [10] := by rfl
def cell741618 : Cell := ⟨(Source.page724.drop 242).take 496, 496, by simp only [List.length_take, List.length_drop, Source.size724] <;> rfl⟩
theorem gap742114 : (Source.page724.drop 738).take 1 = [10] := by rfl
def cell742115 : Cell := ⟨(Source.page724.drop 739), 285, by simp only [List.length_take, List.length_drop, Source.size724] <;> rfl⟩
def coveredPage724 : Page := ⟨Source.page724, [cell741376, lf, cell741618, lf, cell742115], by
  have h := (cutBytes_cover [241, 1, 496, 1] Source.page724).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap741617, gap742114] at h
  exact h⟩
def cell742400 : Cell := ⟨Source.page725.take 186, 186, by simp only [List.length_take, List.length_drop, Source.size725] <;> rfl⟩
theorem gap742586 : (Source.page725.drop 186).take 1 = [10] := by rfl
def cell742587 : Cell := ⟨(Source.page725.drop 187).take 472, 472, by simp only [List.length_take, List.length_drop, Source.size725] <;> rfl⟩
theorem gap743059 : (Source.page725.drop 659).take 1 = [10] := by rfl
def cell743060 : Cell := ⟨(Source.page725.drop 660), 364, by simp only [List.length_take, List.length_drop, Source.size725] <;> rfl⟩
def coveredPage725 : Page := ⟨Source.page725, [cell742400, lf, cell742587, lf, cell743060], by
  have h := (cutBytes_cover [186, 1, 472, 1] Source.page725).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap742586, gap743059] at h
  exact h⟩
def cell743424 : Cell := ⟨Source.page726.take 49, 49, by simp only [List.length_take, List.length_drop, Source.size726] <;> rfl⟩
theorem gap743473 : (Source.page726.drop 49).take 1 = [10] := by rfl
def cell743474 : Cell := ⟨(Source.page726.drop 50).take 452, 452, by simp only [List.length_take, List.length_drop, Source.size726] <;> rfl⟩
theorem gap743926 : (Source.page726.drop 502).take 1 = [10] := by rfl
def cell743927 : Cell := ⟨(Source.page726.drop 503).take 492, 492, by simp only [List.length_take, List.length_drop, Source.size726] <;> rfl⟩
theorem gap744419 : (Source.page726.drop 995).take 1 = [10] := by rfl
def cell744420 : Cell := ⟨(Source.page726.drop 996), 28, by simp only [List.length_take, List.length_drop, Source.size726] <;> rfl⟩
def coveredPage726 : Page := ⟨Source.page726, [cell743424, lf, cell743474, lf, cell743927, lf, cell744420], by
  have h := (cutBytes_cover [49, 1, 452, 1, 492, 1] Source.page726).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap743473, gap743926, gap744419] at h
  exact h⟩
def cell744448 : Cell := ⟨Source.page727.take 351, 351, by simp only [List.length_take, List.length_drop, Source.size727] <;> rfl⟩
theorem gap744799 : (Source.page727.drop 351).take 1 = [10] := by rfl
def cell744800 : Cell := ⟨(Source.page727.drop 352).take 484, 484, by simp only [List.length_take, List.length_drop, Source.size727] <;> rfl⟩
theorem gap745284 : (Source.page727.drop 836).take 1 = [10] := by rfl
def cell745285 : Cell := ⟨(Source.page727.drop 837), 187, by simp only [List.length_take, List.length_drop, Source.size727] <;> rfl⟩
def coveredPage727 : Page := ⟨Source.page727, [cell744448, lf, cell744800, lf, cell745285], by
  have h := (cutBytes_cover [351, 1, 484, 1] Source.page727).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap744799, gap745284] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
