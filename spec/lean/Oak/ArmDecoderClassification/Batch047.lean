import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1402 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1402", ") = {\n    SEE = ", "1402", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1402 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "100000110110", .any 10], 1402, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_float_bulk_simd_decode"⟩
theorem checked1402 : check raw1402 clause1402 = true := by rfl
def row1402 : Row := ⟨1402, 3217030144, 245422080⟩
theorem derived1402 : clause1402.row = row1402 := by rfl
def entry1402 : CheckedRow := ⟨raw1402, clause1402, row1402, checked1402, derived1402⟩

def raw1403 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "10000000", " @ ", "_ : bits(", "5", ")", " as op_code) if SEE < ", "1403", ") = {\n    SEE = ", "1403", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm8", " : bits(", "8", ") = ", "op_code[", "20", " .. ", "13", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_move_fp_imm_decode", "(", "Rd", ", ", "imm5", ", ", "imm8", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1403 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 8, .fixed "10000000", .any 5], 1403, [⟨"Rd", 5, 4, 0, false⟩, ⟨"imm5", 5, 9, 5, false⟩, ⟨"imm8", 8, 20, 13, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_move_fp_imm_decode"⟩
theorem checked1403 : check raw1403 clause1403 = true := by rfl
def row1403 : Row := ⟨1403, 4280295392, 505417728⟩
theorem derived1403 : clause1403.row = row1403 := by rfl
def entry1403 : CheckedRow := ⟨raw1403, clause1403, row1403, checked1403, derived1403⟩

def raw1404 : List String := ["function clause decode64 ((", "0b", "0101111001111001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1404", ") = {\n    SEE = ", "1404", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ")\n}\n"]
def clause1404 : Clause := ⟨[.fixed "0101111001111001110110", .any 10], 1404, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_int_sisd_decode"⟩
theorem checked1404 : check raw1404 clause1404 = true := by rfl
def row1404 : Row := ⟨1404, 4294966272, 1585043456⟩
theorem derived1404 : clause1404.row = row1404 := by rfl
def entry1404 : CheckedRow := ⟨raw1404, clause1404, row1404, checked1404, derived1404⟩

def raw1405 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0000", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1405", ") = {\n    SEE = ", "1405", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "Rm", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1405 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100100", .any 5, .fixed "0000", .any 12], 1405, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode"⟩
theorem checked1405 : check raw1405 clause1405 = true := by rfl
def row1405 : Row := ⟨1405, 3219189760, 209715200⟩
theorem derived1405 : clause1405.row = row1405 := by rfl
def entry1405 : CheckedRow := ⟨raw1405, clause1405, row1405, checked1405, derived1405⟩

def raw1406 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1406", ") = {\n    SEE = ", "1406", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_addsub_wide_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1406 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "000100", .any 10], 1406, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_addsub_wide_decode"⟩
theorem checked1406 : check raw1406 clause1406 = true := by rfl
def row1406 : Row := ⟨1406, 3206609920, 236982272⟩
theorem derived1406 : clause1406.row = row1406 := by rfl
def entry1406 : CheckedRow := ⟨raw1406, clause1406, row1406, checked1406, derived1406⟩

def raw1407 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101100", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1407", ") = {\n    SEE = ", "1407", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1407 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101100", .any 7, .fixed "1", .any 13], 1407, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1407 : check raw1407 clause1407 = true := by rfl
def row1407 : Row := ⟨1407, 3219136512, 226500608⟩
theorem derived1407 : clause1407.row = row1407 := by rfl
def entry1407 : CheckedRow := ⟨raw1407, clause1407, row1407, checked1407, derived1407⟩

def raw1408 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1408", ") = {\n    SEE = ", "1408", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "13", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_maxmin_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1408 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "011110", .any 10], 1408, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 2, 13, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_maxmin_decode"⟩
theorem checked1408 : check raw1408 clause1408 = true := by rfl
def row1408 : Row := ⟨1408, 4280351744, 505444352⟩
theorem derived1408 : clause1408.row = row1408 := by rfl
def entry1408 : CheckedRow := ⟨raw1408, clause1408, row1408, checked1408, derived1408⟩

def raw1409 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1409", ") = {\n    SEE = ", "1409", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_int_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1409 : Clause := ⟨[.fixed "0", .any 1, .fixed "001111", .any 8, .fixed "1000", .any 1, .fixed "0", .any 10], 1409, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mul_int_decode"⟩
theorem checked1409 : check raw1409 clause1409 = true := by rfl
def row1409 : Row := ⟨1409, 3204510720, 251691008⟩
theorem derived1409 : clause1409.row = row1409 := by rfl
def entry1409 : CheckedRow := ⟨raw1409, clause1409, row1409, checked1409, derived1409⟩

def entries47 : List CheckedRow := [entry1402, entry1403, entry1404, entry1405, entry1406, entry1407, entry1408, entry1409]
def rows47 : List Row := [row1402, row1403, row1404, row1405, row1406, row1407, row1408, row1409]
theorem indices47 : rows47.map Row.index = [1402, 1403, 1404, 1405, 1406, 1407, 1408, 1409] := by rfl
theorem bound47 : entries47.map CheckedRow.row = rows47 := by rfl
theorem choices_and_47 : choices rows47 167837696#32 (-1) = [] := by rfl
theorem choices_orr_47 : choices rows47 704708608#32 (-1) = [] := by rfl
theorem choices_eor_47 : choices rows47 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_47 : choices rows47 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
