import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1434 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "011101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1434", ") = {\n    SEE = ", "1434", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_leftsat_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1434 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "011101", .any 10], 1434, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_leftsat_simd_decode"⟩
theorem checked1434 : check raw1434 clause1434 = true := by rfl
def row1434 : Row := ⟨1434, 3212901376, 251687936⟩
theorem derived1434 : clause1434.row = row1434 := by rfl
def entry1434 : CheckedRow := ⟨raw1434, clause1434, row1434, checked1434, derived1434⟩

def raw1435 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "101000000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1435", ") = {\n    SEE = ", "1435", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1435 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "101000000000", .any 10], 1435, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1435 : check raw1435 clause1435 = true := by rfl
def row1435 : Row := ⟨1435, 2134899712, 505937920⟩
theorem derived1435 : clause1435.row = row1435 := by rfl
def entry1435 : CheckedRow := ⟨raw1435, clause1435, row1435, checked1435, derived1435⟩

def raw1436 : List String := ["function clause decode64 ((", "0b", "00011001101", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1436", ") = {\n    SEE = ", "1436", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagpairandzerodata_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1436 : Clause := ⟨[.fixed "00011001101", .any 9, .fixed "10", .any 10], 1436, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagpairandzerodata_decode"⟩
theorem checked1436 : check raw1436 clause1436 = true := by rfl
def row1436 : Row := ⟨1436, 4292873216, 429918208⟩
theorem derived1436 : clause1436.row = row1436 := by rfl
def entry1436 : CheckedRow := ⟨raw1436, clause1436, row1436, checked1436, derived1436⟩

def raw1437 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "0000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1437", ") = {\n    SEE = ", "1437", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_int_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1437 : Clause := ⟨[.fixed "0", .any 1, .fixed "101111", .any 8, .fixed "0000", .any 1, .fixed "0", .any 10], 1437, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_int_decode"⟩
theorem checked1437 : check raw1437 clause1437 = true := by rfl
def row1437 : Row := ⟨1437, 3204510720, 788529152⟩
theorem derived1437 : clause1437.row = row1437 := by rfl
def entry1437 : CheckedRow := ⟨raw1437, clause1437, row1437, checked1437, derived1437⟩

def raw1438 : List String := ["function clause decode64 ((", "0b", "1101101011000000000010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1438", ") = {\n    SEE = ", "1438", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_rev_decode", "(", "Rd", ", ", "Rn", ", ", "opc", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1438 : Clause := ⟨[.fixed "1101101011000000000010", .any 10], 1438, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 2, 11, 10, false⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_rev_decode"⟩
theorem checked1438 : check raw1438 clause1438 = true := by rfl
def row1438 : Row := ⟨1438, 4294966272, 3670018048⟩
theorem derived1438 : clause1438.row = row1438 := by rfl
def entry1438 : CheckedRow := ⟨raw1438, clause1438, row1438, checked1438, derived1438⟩

def raw1439 : List String := ["function clause decode64 ((", "0b", "001110001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1439", ") = {\n    SEE = ", "1439", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1439 : Clause := ⟨[.fixed "001110001", .any 1, .fixed "0", .any 9, .fixed "01", .any 10], 1439, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1439 : check raw1439 clause1439 = true := by rfl
def row1439 : Row := ⟨1439, 4288678912, 947913728⟩
theorem derived1439 : clause1439.row = row1439 := by rfl
def entry1439 : CheckedRow := ⟨raw1439, clause1439, row1439, checked1439, derived1439⟩

def raw1440 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "10110010", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1440", ") = {\n    SEE = ", "1440", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_simdfp_postidx_memory_pair_simdfp_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1440 : Clause := ⟨[.any 2, .fixed "10110010", .any 22], 1440, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_simdfp_postidx_memory_pair_simdfp_postidx__decode"⟩
theorem checked1440 : check raw1440 clause1440 = true := by rfl
def row1440 : Row := ⟨1440, 1069547520, 746586112⟩
theorem derived1440 : clause1440.row = row1440 := by rfl
def entry1440 : CheckedRow := ⟨raw1440, clause1440, row1440, checked1440, derived1440⟩

def raw1441 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1441", ") = {\n    SEE = ", "1441", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "16", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_intmax_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1441 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "110001101010", .any 10], 1441, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 16, 16, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_intmax_decode"⟩
theorem checked1441 : check raw1441 clause1441 = true := by rfl
def row1441 : Row := ⟨1441, 3208641536, 238135296⟩
theorem derived1441 : clause1441.row = row1441 := by rfl
def entry1441 : CheckedRow := ⟨raw1441, clause1441, row1441, checked1441, derived1441⟩

def entries51 : List CheckedRow := [entry1434, entry1435, entry1436, entry1437, entry1438, entry1439, entry1440, entry1441]
def rows51 : List Row := [row1434, row1435, row1436, row1437, row1438, row1439, row1440, row1441]
theorem indices51 : rows51.map Row.index = [1434, 1435, 1436, 1437, 1438, 1439, 1440, 1441] := by rfl
theorem bound51 : entries51.map CheckedRow.row = rows51 := by rfl
theorem choices_and_51 : choices rows51 167837696#32 (-1) = [] := by rfl
theorem choices_orr_51 : choices rows51 704708608#32 (-1) = [] := by rfl
theorem choices_eor_51 : choices rows51 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_51 : choices rows51 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
