import Oak.ArmDecoderPartition.Checker
import Oak.ArmDecoderPartition.SourceBatch044

namespace Oak.ArmDecoderPartition.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
def cell720896 : Cell := ⟨Source.page704.take 3, 3, by simp only [List.length_take, List.length_drop, Source.size704] <;> rfl⟩
theorem gap720899 : (Source.page704.drop 3).take 1 = [10] := by rfl
def cell720900 : Cell := ⟨(Source.page704.drop 4).take 330, 330, by simp only [List.length_take, List.length_drop, Source.size704] <;> rfl⟩
theorem gap721230 : (Source.page704.drop 334).take 1 = [10] := by rfl
def cell721231 : Cell := ⟨(Source.page704.drop 335).take 536, 536, by simp only [List.length_take, List.length_drop, Source.size704] <;> rfl⟩
theorem gap721767 : (Source.page704.drop 871).take 1 = [10] := by rfl
def cell721768 : Cell := ⟨(Source.page704.drop 872), 152, by simp only [List.length_take, List.length_drop, Source.size704] <;> rfl⟩
def coveredPage704 : Page := ⟨Source.page704, [cell720896, lf, cell720900, lf, cell721231, lf, cell721768], by
  have h := (cutBytes_cover [3, 1, 330, 1, 536, 1] Source.page704).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap720899, gap721230, gap721767] at h
  exact h⟩
def cell721920 : Cell := ⟨Source.page705.take 248, 248, by simp only [List.length_take, List.length_drop, Source.size705] <;> rfl⟩
theorem gap722168 : (Source.page705.drop 248).take 1 = [10] := by rfl
def cell722169 : Cell := ⟨(Source.page705.drop 249).take 307, 307, by simp only [List.length_take, List.length_drop, Source.size705] <;> rfl⟩
theorem gap722476 : (Source.page705.drop 556).take 1 = [10] := by rfl
def cell722477 : Cell := ⟨(Source.page705.drop 557).take 337, 337, by simp only [List.length_take, List.length_drop, Source.size705] <;> rfl⟩
theorem gap722814 : (Source.page705.drop 894).take 1 = [10] := by rfl
def cell722815 : Cell := ⟨(Source.page705.drop 895), 129, by simp only [List.length_take, List.length_drop, Source.size705] <;> rfl⟩
def coveredPage705 : Page := ⟨Source.page705, [cell721920, lf, cell722169, lf, cell722477, lf, cell722815], by
  have h := (cutBytes_cover [248, 1, 307, 1, 337, 1] Source.page705).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap722168, gap722476, gap722814] at h
  exact h⟩
def cell722944 : Cell := ⟨Source.page706.take 235, 235, by simp only [List.length_take, List.length_drop, Source.size706] <;> rfl⟩
theorem gap723179 : (Source.page706.drop 235).take 1 = [10] := by rfl
def cell723180 : Cell := ⟨(Source.page706.drop 236).take 522, 522, by simp only [List.length_take, List.length_drop, Source.size706] <;> rfl⟩
theorem gap723702 : (Source.page706.drop 758).take 1 = [10] := by rfl
def cell723703 : Cell := ⟨(Source.page706.drop 759), 265, by simp only [List.length_take, List.length_drop, Source.size706] <;> rfl⟩
def coveredPage706 : Page := ⟨Source.page706, [cell722944, lf, cell723180, lf, cell723703], by
  have h := (cutBytes_cover [235, 1, 522, 1] Source.page706).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap723179, gap723702] at h
  exact h⟩
def cell723968 : Cell := ⟨Source.page707.take 253, 253, by simp only [List.length_take, List.length_drop, Source.size707] <;> rfl⟩
theorem gap724221 : (Source.page707.drop 253).take 1 = [10] := by rfl
def cell724222 : Cell := ⟨(Source.page707.drop 254).take 471, 471, by simp only [List.length_take, List.length_drop, Source.size707] <;> rfl⟩
theorem gap724693 : (Source.page707.drop 725).take 1 = [10] := by rfl
def cell724694 : Cell := ⟨(Source.page707.drop 726), 298, by simp only [List.length_take, List.length_drop, Source.size707] <;> rfl⟩
def coveredPage707 : Page := ⟨Source.page707, [cell723968, lf, cell724222, lf, cell724694], by
  have h := (cutBytes_cover [253, 1, 471, 1] Source.page707).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap724221, gap724693] at h
  exact h⟩
def cell724992 : Cell := ⟨Source.page708.take 119, 119, by simp only [List.length_take, List.length_drop, Source.size708] <;> rfl⟩
theorem gap725111 : (Source.page708.drop 119).take 1 = [10] := by rfl
def cell725112 : Cell := ⟨(Source.page708.drop 120).take 433, 433, by simp only [List.length_take, List.length_drop, Source.size708] <;> rfl⟩
theorem gap725545 : (Source.page708.drop 553).take 1 = [10] := by rfl
def cell725546 : Cell := ⟨(Source.page708.drop 554).take 360, 360, by simp only [List.length_take, List.length_drop, Source.size708] <;> rfl⟩
theorem gap725906 : (Source.page708.drop 914).take 1 = [10] := by rfl
def cell725907 : Cell := ⟨(Source.page708.drop 915), 109, by simp only [List.length_take, List.length_drop, Source.size708] <;> rfl⟩
def coveredPage708 : Page := ⟨Source.page708, [cell724992, lf, cell725112, lf, cell725546, lf, cell725907], by
  have h := (cutBytes_cover [119, 1, 433, 1, 360, 1] Source.page708).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap725111, gap725545, gap725906] at h
  exact h⟩
def cell726016 : Cell := ⟨Source.page709.take 427, 427, by simp only [List.length_take, List.length_drop, Source.size709] <;> rfl⟩
theorem gap726443 : (Source.page709.drop 427).take 1 = [10] := by rfl
def cell726444 : Cell := ⟨(Source.page709.drop 428).take 544, 544, by simp only [List.length_take, List.length_drop, Source.size709] <;> rfl⟩
theorem gap726988 : (Source.page709.drop 972).take 1 = [10] := by rfl
def cell726989 : Cell := ⟨(Source.page709.drop 973), 51, by simp only [List.length_take, List.length_drop, Source.size709] <;> rfl⟩
def coveredPage709 : Page := ⟨Source.page709, [cell726016, lf, cell726444, lf, cell726989], by
  have h := (cutBytes_cover [427, 1, 544, 1] Source.page709).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap726443, gap726988] at h
  exact h⟩
def cell727040 : Cell := ⟨Source.page710.take 346, 346, by simp only [List.length_take, List.length_drop, Source.size710] <;> rfl⟩
theorem gap727386 : (Source.page710.drop 346).take 1 = [10] := by rfl
def cell727387 : Cell := ⟨(Source.page710.drop 347).take 432, 432, by simp only [List.length_take, List.length_drop, Source.size710] <;> rfl⟩
theorem gap727819 : (Source.page710.drop 779).take 1 = [10] := by rfl
def cell727820 : Cell := ⟨(Source.page710.drop 780), 244, by simp only [List.length_take, List.length_drop, Source.size710] <;> rfl⟩
def coveredPage710 : Page := ⟨Source.page710, [cell727040, lf, cell727387, lf, cell727820], by
  have h := (cutBytes_cover [346, 1, 432, 1] Source.page710).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap727386, gap727819] at h
  exact h⟩
def cell728064 : Cell := ⟨Source.page711.take 67, 67, by simp only [List.length_take, List.length_drop, Source.size711] <;> rfl⟩
theorem gap728131 : (Source.page711.drop 67).take 1 = [10] := by rfl
def cell728132 : Cell := ⟨(Source.page711.drop 68).take 537, 537, by simp only [List.length_take, List.length_drop, Source.size711] <;> rfl⟩
theorem gap728669 : (Source.page711.drop 605).take 1 = [10] := by rfl
def cell728670 : Cell := ⟨(Source.page711.drop 606), 418, by simp only [List.length_take, List.length_drop, Source.size711] <;> rfl⟩
def coveredPage711 : Page := ⟨Source.page711, [cell728064, lf, cell728132, lf, cell728670], by
  have h := (cutBytes_cover [67, 1, 537, 1] Source.page711).symm
  simp only [cutBytes, List.flatten_cons, List.flatten_nil, List.append_nil, List.drop_drop, Nat.reduceAdd, gap728131, gap728669] at h
  exact h⟩
end Oak.ArmDecoderPartition.Data
