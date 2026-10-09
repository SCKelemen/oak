import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1770 : List String := ["function clause decode64 ((", "0b", "01101110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "4", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1770", ") = {\n    SEE = ", "1770", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm4", " : bits(", "4", ") = ", "op_code[", "14", " .. ", "11", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_insert_decode", "(", "Rd", ", ", "Rn", ", ", "imm4", ", ", "imm5", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1770 : Clause := ⟨[.fixed "01101110000", .any 5, .fixed "0", .any 4, .fixed "1", .any 10], 1770, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm4", 4, 14, 11, false⟩, ⟨"imm5", 5, 20, 16, false⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_insert_decode"⟩
theorem checked1770 : check raw1770 clause1770 = true := by rfl
def row1770 : Row := ⟨1770, 4292903936, 1845494784⟩
theorem derived1770 : clause1770.row = row1770 := by rfl
def entry1770 : CheckedRow := ⟨raw1770, clause1770, row1770, checked1770, derived1770⟩

def raw1771 : List String := ["function clause decode64 ((", "0b", "110101100101111100001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1111111111", " as op_code) if SEE < ", "1771", ") = {\n    SEE = ", "1771", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "22", " .. ", "21", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "branch_unconditional_register_decode", "(", "Rm", ", ", "Rn", ", ", "M", ", ", "A", ", ", "op2", ", ", "op", ", ", "Z", ")\n}\n"]
def clause1771 : Clause := ⟨[.fixed "110101100101111100001", .any 1, .fixed "1111111111"], 1771, [⟨"Rm", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"M", 1, 10, 10, true⟩, ⟨"A", 1, 11, 11, true⟩, ⟨"op2", 5, 20, 16, false⟩, ⟨"op", 2, 22, 21, false⟩, ⟨"Z", 1, 24, 24, true⟩], "branch_unconditional_register_decode"⟩
theorem checked1771 : check raw1771 clause1771 = true := by rfl
def row1771 : Row := ⟨1771, 4294966271, 3596553215⟩
theorem derived1771 : clause1771.row = row1771 := by rfl
def entry1771 : CheckedRow := ⟨raw1771, clause1771, row1771, checked1771, derived1771⟩

def raw1772 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0100", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1772", ") = {\n    SEE = ", "1772", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "Rm", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1772 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100110", .any 5, .fixed "0100", .any 12], 1772, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode"⟩
theorem checked1772 : check raw1772 clause1772 = true := by rfl
def row1772 : Row := ⟨1772, 3219189760, 213925888⟩
theorem derived1772 : clause1772.row = row1772 := by rfl
def entry1772 : CheckedRow := ⟨raw1772, clause1772, row1772, checked1772, derived1772⟩

def raw1773 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001000000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1773", ") = {\n    SEE = ", "1773", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1773 : Clause := ⟨[.fixed "1", .any 1, .fixed "001000000", .any 5, .fixed "0", .any 15], 1773, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1773 : check raw1773 clause1773 = true := by rfl
def row1773 : Row := ⟨1773, 3219161088, 2281701376⟩
theorem derived1773 : clause1773.row = row1773 := by rfl
def entry1773 : CheckedRow := ⟨raw1773, clause1773, row1773, checked1773, derived1773⟩

def raw1774 : List String := ["function clause decode64 ((", "0b", "01111110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1774", ") = {\n    SEE = ", "1774", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "E", ", ", "U", ")\n}\n"]
def clause1774 : Clause := ⟨[.fixed "01111110110", .any 5, .fixed "001001", .any 10], 1774, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode"⟩
theorem checked1774 : check raw1774 clause1774 = true := by rfl
def row1774 : Row := ⟨1774, 4292934656, 2126521344⟩
theorem derived1774 : clause1774.row = row1774 := by rfl
def entry1774 : CheckedRow := ⟨raw1774, clause1774, row1774, checked1774, derived1774⟩

def raw1775 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1775", ") = {\n    SEE = ", "1775", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_fp_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1775 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "1", .any 5, .fixed "110101", .any 10], 1775, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_fp_decode"⟩
theorem checked1775 : check raw1775 clause1775 = true := by rfl
def row1775 : Row := ⟨1775, 3214998528, 773903360⟩
theorem derived1775 : clause1775.row = row1775 := by rfl
def entry1775 : CheckedRow := ⟨raw1775, clause1775, row1775, checked1775, derived1775⟩

def raw1776 : List String := ["function clause decode64 ((", "0b", "00011111", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1776", ") = {\n    SEE = ", "1776", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_mul_addsub_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "o1", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1776 : Clause := ⟨[.fixed "00011111", .any 2, .fixed "0", .any 5, .fixed "0", .any 15], 1776, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_mul_addsub_decode"⟩
theorem checked1776 : check raw1776 clause1776 = true := by rfl
def row1776 : Row := ⟨1776, 4280320000, 520093696⟩
theorem derived1776 : clause1776.row = row1776 := by rfl
def entry1776 : CheckedRow := ⟨raw1776, clause1776, row1776, checked1776, derived1776⟩

def raw1777 : List String := ["function clause decode64 ((", "0b", "0111100100", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1777", ") = {\n    SEE = ", "1777", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1777 : Clause := ⟨[.fixed "0111100100", .any 22], 1777, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1777 : check raw1777 clause1777 = true := by rfl
def row1777 : Row := ⟨1777, 4290772992, 2030043136⟩
theorem derived1777 : clause1777.row = row1777 := by rfl
def entry1777 : CheckedRow := ⟨raw1777, clause1777, row1777, checked1777, derived1777⟩

def entries93 : List CheckedRow := [entry1770, entry1771, entry1772, entry1773, entry1774, entry1775, entry1776, entry1777]
def rows93 : List Row := [row1770, row1771, row1772, row1773, row1774, row1775, row1776, row1777]
theorem indices93 : rows93.map Row.index = [1770, 1771, 1772, 1773, 1774, 1775, 1776, 1777] := by rfl
theorem bound93 : entries93.map CheckedRow.row = rows93 := by rfl
theorem choices_and_93 : choices rows93 167837696#32 (-1) = [] := by rfl
theorem choices_orr_93 : choices rows93 704708608#32 (-1) = [] := by rfl
theorem choices_eor_93 : choices rows93 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_93 : choices rows93 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
