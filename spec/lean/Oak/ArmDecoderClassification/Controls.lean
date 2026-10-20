import Oak.ArmDecoderClassification.Batch062
import Oak.ArmDecoderClassification.Batch095
import Oak.ArmDecoderClassification.Batch102
import Oak.ArmDecoderClassification.Batch104

namespace Oak.ArmDecoderClassification
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-- Synthetic classifier controls, not additional Sail instruction coverage. -/
def toy : Clause := ⟨[.any 32], 10, [⟨"Rd", 5, 4, 0, false⟩], "test_decode"⟩
def toyRaw : List String :=
 ["function clause decode64 ((", "_ : bits(", "32", ")", " as op_code) if SEE < ", "10",
 ") = {\n    SEE = ", "10", ";\n", "    ", "Rd", " : bits(", "5", ") = ",
 "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "test_decode", "(", "Rd", ")\n}\n"]

theorem control_positive : check toyRaw toy = true := by decide_cbv
theorem reject_punctuation : check (toyRaw.set 24 ")\n};\n") toy = false := by decide_cbv
theorem reject_whitespace : check (toyRaw.set 9 "  ") toy = false := by decide_cbv
theorem reject_guard : check (toyRaw.set 5 "11") toy = false := by decide_cbv
theorem reject_write : check (toyRaw.set 7 "11") toy = false := by decide_cbv
theorem reject_callee : check (toyRaw.set 21 "other_decode") toy = false := by decide_cbv
theorem reject_argument : check (toyRaw.set 23 "Rn") toy = false := by decide_cbv
theorem reject_extra_body : check (toyRaw ++ ["SEE = 0;\n"]) toy = false := by decide_cbv
theorem reject_pattern_width : ({toy with segments := [.any 31]}).valid = false := by decide_cbv
theorem reject_bad_digit : ({toy with segments := [.fixed "x"]}).valid = false := by decide_cbv
theorem reject_field_width : ({toy with fields := [⟨"Rd", 4, 4, 0, false⟩]}).valid = false := by decide_cbv
theorem reject_field_bounds : ({toy with fields := [⟨"Rd", 5, 34, 30, false⟩]}).valid = false := by decide_cbv
theorem reject_singleton_width : ({toy with fields := [⟨"Rd", 5, 4, 0, true⟩]}).valid = false := by decide_cbv
theorem reject_duplicate_binder : ({toy with fields := toy.fields ++ toy.fields}).valid = false := by decide_cbv
theorem reject_word_binder : ({toy with fields := [⟨"op_code", 5, 4, 0, false⟩]}).valid = false := by decide_cbv
theorem reject_see_binder : ({toy with fields := [⟨"SEE", 5, 4, 0, false⟩]}).valid = false := by decide_cbv
theorem reject_keyword_binder : ({toy with fields := [⟨"match", 5, 4, 0, false⟩]}).valid = false := by decide_cbv
theorem reject_callee_capture : ({toy with fields := [⟨"test_decode", 5, 4, 0, false⟩]}).valid = false := by decide_cbv

theorem first_overlapping : first [⟨1,0,0⟩,⟨2,0,0⟩] 0#32 (-1) = some 1 := by decide_cbv
theorem first_reordered : first [⟨2,0,0⟩,⟨1,0,0⟩] 0#32 (-1) = some 2 := by decide_cbv
theorem strict_guard_equal : first [⟨1,0,0⟩] 0#32 1 = none := by decide_cbv
theorem strict_guard_continues : first [⟨1,0,0⟩,⟨2,0,0⟩] 0#32 1 = some 2 := by decide_cbv

/-- Exact argument classification in source order. These do not execute callees. -/
theorem and_arguments : Data.clause1845.arguments 0x0a010000#32 = [0,0,0,1,0,0,0,0] := by decide_cbv
theorem orr_arguments : Data.clause1858.arguments 0x2a010000#32 = [0,0,0,1,0,0,1,0] := by decide_cbv
theorem eor_arguments : Data.clause1788.arguments 0x4a010000#32 = [0,0,0,1,0,0,2,0] := by decide_cbv
theorem ret_arguments : Data.clause1522.arguments 0xd65f03c0#32 = [0,30,0,0,31,2,0] := by decide_cbv
/-- Changing Rd still belongs to the AND class, but changes its actual arguments. -/
theorem changed_destination : Data.clause1845.arguments 0x0a010001#32 = [1,0,0,1,0,0,0,0] := by decide_cbv
theorem changed_fixed_bit : Data.row1845.matches 0x0b010000#32 = false := by decide_cbv
end Oak.ArmDecoderClassification
