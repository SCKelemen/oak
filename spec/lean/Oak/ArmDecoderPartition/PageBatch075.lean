import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch037

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell614400 : Cell := ⟨Source.page600.take 199, 199, by simp only [List.length_take, List.length_drop, Source.size600] <;> rfl⟩
theorem gap614599 : (Source.page600.drop 199).take 1 = [10] := by rfl
def cell614600 : Cell := ⟨(Source.page600.drop 200).take 536, 536, by simp only [List.length_take, List.length_drop, Source.size600] <;> rfl⟩
theorem gap615136 : (Source.page600.drop 736).take 1 = [10] := by rfl
def cell615137 : Cell := ⟨(Source.page600.drop 737).take 234, 234, by simp only [List.length_take, List.length_drop, Source.size600] <;> rfl⟩
theorem gap615371 : (Source.page600.drop 971).take 1 = [10] := by rfl
def cell615372 : Cell := ⟨(Source.page600.drop 972), 52, by simp only [List.length_take, List.length_drop, Source.size600] <;> rfl⟩
def coveredPage600 : Page := ⟨Source.page600, [cell614400, lf, cell614600, lf, cell615137, lf, cell615372], by
  have h := (cutBytes_cover [199, 1, 536, 1, 234, 1] Source.page600).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap614599, gap615136, gap615371] at h
  exact h⟩
def cell615424 : Cell := ⟨Source.page601.take 388, 388, by simp only [List.length_take, List.length_drop, Source.size601] <;> rfl⟩
theorem gap615812 : (Source.page601.drop 388).take 1 = [10] := by rfl
def cell615813 : Cell := ⟨(Source.page601.drop 389).take 445, 445, by simp only [List.length_take, List.length_drop, Source.size601] <;> rfl⟩
theorem gap616258 : (Source.page601.drop 834).take 1 = [10] := by rfl
def cell616259 : Cell := ⟨(Source.page601.drop 835), 189, by simp only [List.length_take, List.length_drop, Source.size601] <;> rfl⟩
def coveredPage601 : Page := ⟨Source.page601, [cell615424, lf, cell615813, lf, cell616259], by
  have h := (cutBytes_cover [388, 1, 445, 1] Source.page601).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap615812, gap616258] at h
  exact h⟩
def cell616448 : Cell := ⟨Source.page602.take 351, 351, by simp only [List.length_take, List.length_drop, Source.size602] <;> rfl⟩
theorem gap616799 : (Source.page602.drop 351).take 1 = [10] := by rfl
def cell616800 : Cell := ⟨(Source.page602.drop 352).take 607, 607, by simp only [List.length_take, List.length_drop, Source.size602] <;> rfl⟩
theorem gap617407 : (Source.page602.drop 959).take 1 = [10] := by rfl
def cell617408 : Cell := ⟨(Source.page602.drop 960), 64, by simp only [List.length_take, List.length_drop, Source.size602] <;> rfl⟩
def coveredPage602 : Page := ⟨Source.page602, [cell616448, lf, cell616800, lf, cell617408], by
  have h := (cutBytes_cover [351, 1, 607, 1] Source.page602).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap616799, gap617407] at h
  exact h⟩
def cell617472 : Cell := ⟨Source.page603.take 431, 431, by simp only [List.length_take, List.length_drop, Source.size603] <;> rfl⟩
theorem gap617903 : (Source.page603.drop 431).take 1 = [10] := by rfl
def cell617904 : Cell := ⟨(Source.page603.drop 432).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size603] <;> rfl⟩
theorem gap618375 : (Source.page603.drop 903).take 1 = [10] := by rfl
def cell618376 : Cell := ⟨(Source.page603.drop 904), 120, by simp only [List.length_take, List.length_drop, Source.size603] <;> rfl⟩
def coveredPage603 : Page := ⟨Source.page603, [cell617472, lf, cell617904, lf, cell618376], by
  have h := (cutBytes_cover [431, 1, 471, 1] Source.page603).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap617903, gap618375] at h
  exact h⟩
def cell618496 : Cell := ⟨Source.page604.take 250, 250, by simp only [List.length_take, List.length_drop, Source.size604] <;> rfl⟩
theorem gap618746 : (Source.page604.drop 250).take 1 = [10] := by rfl
def cell618747 : Cell := ⟨(Source.page604.drop 251).take 393, 393, by simp only [List.length_take, List.length_drop, Source.size604] <;> rfl⟩
theorem gap619140 : (Source.page604.drop 644).take 1 = [10] := by rfl
def cell619141 : Cell := ⟨(Source.page604.drop 645), 379, by simp only [List.length_take, List.length_drop, Source.size604] <;> rfl⟩
def coveredPage604 : Page := ⟨Source.page604, [cell618496, lf, cell618747, lf, cell619141], by
  have h := (cutBytes_cover [250, 1, 393, 1] Source.page604).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap618746, gap619140] at h
  exact h⟩
def cell619520 : Cell := ⟨Source.page605.take 61, 61, by simp only [List.length_take, List.length_drop, Source.size605] <;> rfl⟩
theorem gap619581 : (Source.page605.drop 61).take 1 = [10] := by rfl
def cell619582 : Cell := ⟨(Source.page605.drop 62).take 545, 545, by simp only [List.length_take, List.length_drop, Source.size605] <;> rfl⟩
theorem gap620127 : (Source.page605.drop 607).take 1 = [10] := by rfl
def cell620128 : Cell := ⟨(Source.page605.drop 608), 416, by simp only [List.length_take, List.length_drop, Source.size605] <;> rfl⟩
def coveredPage605 : Page := ⟨Source.page605, [cell619520, lf, cell619582, lf, cell620128], by
  have h := (cutBytes_cover [61, 1, 545, 1] Source.page605).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap619581, gap620127] at h
  exact h⟩
def cell620544 : Cell := ⟨Source.page606.take 159, 159, by simp only [List.length_take, List.length_drop, Source.size606] <;> rfl⟩
theorem gap620703 : (Source.page606.drop 159).take 1 = [10] := by rfl
def cell620704 : Cell := ⟨(Source.page606.drop 160).take 564, 564, by simp only [List.length_take, List.length_drop, Source.size606] <;> rfl⟩
theorem gap621268 : (Source.page606.drop 724).take 1 = [10] := by rfl
def cell621269 : Cell := ⟨(Source.page606.drop 725), 299, by simp only [List.length_take, List.length_drop, Source.size606] <;> rfl⟩
def coveredPage606 : Page := ⟨Source.page606, [cell620544, lf, cell620704, lf, cell621269], by
  have h := (cutBytes_cover [159, 1, 564, 1] Source.page606).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap620703, gap621268] at h
  exact h⟩
def cell621568 : Cell := ⟨Source.page607.take 201, 201, by simp only [List.length_take, List.length_drop, Source.size607] <;> rfl⟩
theorem gap621769 : (Source.page607.drop 201).take 1 = [10] := by rfl
def cell621770 : Cell := ⟨(Source.page607.drop 202).take 417, 417, by simp only [List.length_take, List.length_drop, Source.size607] <;> rfl⟩
theorem gap622187 : (Source.page607.drop 619).take 1 = [10] := by rfl
def cell622188 : Cell := ⟨(Source.page607.drop 620), 404, by simp only [List.length_take, List.length_drop, Source.size607] <;> rfl⟩
def coveredPage607 : Page := ⟨Source.page607, [cell621568, lf, cell621770, lf, cell622188], by
  have h := (cutBytes_cover [201, 1, 417, 1] Source.page607).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap621769, gap622187] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
