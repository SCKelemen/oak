import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1458 : List String := ["function clause decode64 ((", "0b", "011110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1458", ") = {\n    SEE = ", "1458", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1458 : Clause := ⟨[.fixed "011110000", .any 1, .fixed "1", .any 5, .fixed "011100", .any 5, .fixed "11111"], 1458, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1458 : check raw1458 clause1458 = true := by rfl
def row1458 : Row := ⟨1458, 4288740383, 2015391775⟩
theorem derived1458 : clause1458.row = row1458 := by rfl
def entry1458 : CheckedRow := ⟨raw1458, clause1458, row1458, checked1458, derived1458⟩

def raw1459 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "000", " as op_code) if SEE < ", "1459", ") = {\n    SEE = ", "1459", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "4", " .. ", "3", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "15", " .. ", "14", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_compare_uncond_decode", "(", "opc", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1459 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "001000", .any 5, .fixed "0", .any 1, .fixed "000"], 1459, [⟨"opc", 2, 4, 3, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 2, 15, 14, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_compare_uncond_decode"⟩
theorem checked1459 : check raw1459 clause1459 = true := by rfl
def row1459 : Row := ⟨1459, 4280351767, 505421824⟩
theorem derived1459 : clause1459.row = row1459 := by rfl
def entry1459 : CheckedRow := ⟨raw1459, clause1459, row1459, checked1459, derived1459⟩

def raw1460 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1460", ") = {\n    SEE = ", "1460", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_permute_transpose_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "size", ", ", "Q", ")\n}\n"]
def clause1460 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "0", .any 5, .fixed "001010", .any 10], 1460, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_permute_transpose_decode"⟩
theorem checked1460 : check raw1460 clause1460 = true := by rfl
def row1460 : Row := ⟨1460, 3206609920, 234891264⟩
theorem derived1460 : clause1460.row = row1460 := by rfl
def entry1460 : CheckedRow := ⟨raw1460, clause1460, row1460, checked1460, derived1460⟩

def raw1461 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0110110", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1461", ") = {\n    SEE = ", "1461", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm14", " : bits(", "14", ") = ", "op_code[", "18", " .. ", "5", "]", ";\n", "    ", "b40", " : bits(", "5", ") = ", "op_code[", "23", " .. ", "19", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "b5", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "branch_conditional_test_decode", "(", "Rt", ", ", "imm14", ", ", "b40", ", ", "op", ", ", "b5", ")\n}\n"]
def clause1461 : Clause := ⟨[.any 1, .fixed "0110110", .any 24], 1461, [⟨"Rt", 5, 4, 0, false⟩, ⟨"imm14", 14, 18, 5, false⟩, ⟨"b40", 5, 23, 19, false⟩, ⟨"op", 1, 24, 24, true⟩, ⟨"b5", 1, 31, 31, true⟩], "branch_conditional_test_decode"⟩
theorem checked1461 : check raw1461 clause1461 = true := by rfl
def row1461 : Row := ⟨1461, 2130706432, 905969664⟩
theorem derived1461 : clause1461.row = row1461 := by rfl
def entry1461 : CheckedRow := ⟨raw1461, clause1461, row1461, checked1461, derived1461⟩

def raw1462 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1462", ") = {\n    SEE = ", "1462", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1462 : Clause := ⟨[.fixed "1", .any 1, .fixed "1110000", .any 1, .fixed "1", .any 5, .fixed "001000", .any 5, .fixed "11111"], 1462, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1462 : check raw1462 clause1462 = true := by rfl
def row1462 : Row := ⟨1462, 3214998559, 3089113119⟩
theorem derived1462 : clause1462.row = row1462 := by rfl
def entry1462 : CheckedRow := ⟨raw1462, clause1462, row1462, checked1462, derived1462⟩

def raw1463 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011111", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "0101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1463", ") = {\n    SEE = ", "1463", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1463 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011111", .any 7, .fixed "0101", .any 1, .fixed "0", .any 10], 1463, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_fp_simd_decode"⟩
theorem checked1463 : check raw1463 clause1463 = true := by rfl
def row1463 : Row := ⟨1463, 3212899328, 260067328⟩
theorem derived1463 : clause1463.row = row1463 := by rfl
def entry1463 : CheckedRow := ⟨raw1463, clause1463, row1463, checked1463, derived1463⟩

def raw1464 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1464", ") = {\n    SEE = ", "1464", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "eq", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "eq", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1464 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "001101", .any 10], 1464, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"eq", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_int_simd_decode"⟩
theorem checked1464 : check raw1464 clause1464 = true := by rfl
def row1464 : Row := ⟨1464, 3206609920, 773862400⟩
theorem derived1464 : clause1464.row = row1464 := by rfl
def entry1464 : CheckedRow := ⟨raw1464, clause1464, row1464, checked1464, derived1464⟩

def raw1465 : List String := ["function clause decode64 ((", "0b", "011110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1465", ") = {\n    SEE = ", "1465", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1465 : Clause := ⟨[.fixed "011110000", .any 1, .fixed "1", .any 5, .fixed "010100", .any 5, .fixed "11111"], 1465, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1465 : check raw1465 clause1465 = true := by rfl
def row1465 : Row := ⟨1465, 4288740383, 2015383583⟩
theorem derived1465 : clause1465.row = row1465 := by rfl
def entry1465 : CheckedRow := ⟨raw1465, clause1465, row1465, checked1465, derived1465⟩

def entries54 : List CheckedRow := [entry1458, entry1459, entry1460, entry1461, entry1462, entry1463, entry1464, entry1465]
def rows54 : List Row := [row1458, row1459, row1460, row1461, row1462, row1463, row1464, row1465]
theorem indices54 : rows54.map Row.index = [1458, 1459, 1460, 1461, 1462, 1463, 1464, 1465] := by rfl
theorem bound54 : entries54.map CheckedRow.row = rows54 := by rfl
theorem choices_and_54 : choices rows54 167837696#32 (-1) = [] := by rfl
theorem choices_orr_54 : choices rows54 704708608#32 (-1) = [] := by rfl
theorem choices_eor_54 : choices rows54 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_54 : choices rows54 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
