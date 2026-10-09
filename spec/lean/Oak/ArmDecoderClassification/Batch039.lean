import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1338 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1338", ") = {\n    SEE = ", "1338", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1338 : Clause := ⟨[.fixed "1", .any 1, .fixed "1110000", .any 1, .fixed "1", .any 5, .fixed "011100", .any 5, .fixed "11111"], 1338, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1338 : check raw1338 clause1338 = true := by rfl
def row1338 : Row := ⟨1338, 3214998559, 3089133599⟩
theorem derived1338 : clause1338.row = row1338 := by rfl
def entry1338 : CheckedRow := ⟨raw1338, clause1338, row1338, checked1338, derived1338⟩

def raw1339 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1339", ") = {\n    SEE = ", "1339", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_accum_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1339 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "100000", .any 10], 1339, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_mul_accum_decode"⟩
theorem checked1339 : check raw1339 clause1339 = true := by rfl
def row1339 : Row := ⟨1339, 3206609920, 773881856⟩
theorem derived1339 : clause1339.row = row1339 := by rfl
def entry1339 : CheckedRow := ⟨raw1339, clause1339, row1339, checked1339, derived1339⟩

def raw1340 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1010", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1340", ") = {\n    SEE = ", "1340", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_long_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1340 : Clause := ⟨[.fixed "0", .any 1, .fixed "101111", .any 8, .fixed "1010", .any 1, .fixed "0", .any 10], 1340, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mul_long_decode"⟩
theorem checked1340 : check raw1340 clause1340 = true := by rfl
def row1340 : Row := ⟨1340, 3204510720, 788570112⟩
theorem derived1340 : clause1340.row = row1340 := by rfl
def entry1340 : CheckedRow := ⟨raw1340, clause1340, row1340, checked1340, derived1340⟩

def raw1341 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110001000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1341", ") = {\n    SEE = ", "1341", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1341 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "110001000000", .any 10], 1341, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1341 : check raw1341 clause1341 = true := by rfl
def row1341 : Row := ⟨1341, 2134899712, 506527744⟩
theorem derived1341 : clause1341.row = row1341 := by rfl
def entry1341 : CheckedRow := ⟨raw1341, clause1341, row1341, checked1341, derived1341⟩

def raw1342 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1342", ") = {\n    SEE = ", "1342", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_conv_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1342 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "111001", .any 10], 1342, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_conv_int_simd_decode"⟩
theorem checked1342 : check raw1342 clause1342 = true := by rfl
def row1342 : Row := ⟨1342, 3212901376, 788587520⟩
theorem derived1342 : clause1342.row = row1342 := by rfl
def entry1342 : CheckedRow := ⟨raw1342, clause1342, row1342, checked1342, derived1342⟩

def raw1343 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1343", ") = {\n    SEE = ", "1343", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1343 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "100001101010", .any 10], 1343, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_simd_decode"⟩
theorem checked1343 : check raw1343 clause1343 = true := by rfl
def row1343 : Row := ⟨1343, 3217030144, 773957632⟩
theorem derived1343 : clause1343.row = row1343 := by rfl
def entry1343 : CheckedRow := ⟨raw1343, clause1343, row1343, checked1343, derived1343⟩

def raw1344 : List String := ["function clause decode64 ((", "0b", "01011001110", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1344", ") = {\n    SEE = ", "1344", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1344 : Clause := ⟨[.fixed "01011001110", .any 9, .fixed "00", .any 10], 1344, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1344 : check raw1344 clause1344 = true := by rfl
def row1344 : Row := ⟨1344, 4292873216, 1505755136⟩
theorem derived1344 : clause1344.row = row1344 := by rfl
def entry1344 : CheckedRow := ⟨raw1344, clause1344, row1344, checked1344, derived1344⟩

def raw1345 : List String := ["function clause decode64 ((", "0b", "1101011000111111000000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "00000", " as op_code) if SEE < ", "1345", ") = {\n    SEE = ", "1345", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "22", " .. ", "21", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "branch_unconditional_register_decode", "(", "Rm", ", ", "Rn", ", ", "M", ", ", "A", ", ", "op2", ", ", "op", ", ", "Z", ")\n}\n"]
def clause1345 : Clause := ⟨[.fixed "1101011000111111000000", .any 5, .fixed "00000"], 1345, [⟨"Rm", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"M", 1, 10, 10, true⟩, ⟨"A", 1, 11, 11, true⟩, ⟨"op2", 5, 20, 16, false⟩, ⟨"op", 2, 22, 21, false⟩, ⟨"Z", 1, 24, 24, true⟩], "branch_unconditional_register_decode"⟩
theorem checked1345 : check raw1345 clause1345 = true := by rfl
def row1345 : Row := ⟨1345, 4294966303, 3594452992⟩
theorem derived1345 : clause1345.row = row1345 := by rfl
def entry1345 : CheckedRow := ⟨raw1345, clause1345, row1345, checked1345, derived1345⟩

def entries39 : List CheckedRow := [entry1338, entry1339, entry1340, entry1341, entry1342, entry1343, entry1344, entry1345]
def rows39 : List Row := [row1338, row1339, row1340, row1341, row1342, row1343, row1344, row1345]
theorem indices39 : rows39.map Row.index = [1338, 1339, 1340, 1341, 1342, 1343, 1344, 1345] := by rfl
theorem bound39 : entries39.map CheckedRow.row = rows39 := by rfl
theorem choices_and_39 : choices rows39 167837696#32 (-1) = [] := by rfl
theorem choices_orr_39 : choices rows39 704708608#32 (-1) = [] := by rfl
theorem choices_eor_39 : choices rows39 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_39 : choices rows39 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
