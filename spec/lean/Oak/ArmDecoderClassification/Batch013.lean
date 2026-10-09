import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1130 : List String := ["function clause decode64 ((", "0b", "0101111011111001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1130", ") = {\n    SEE = ", "1130", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size_1_", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_special_recip_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size_1_", ", ", "U", ")\n}\n"]
def clause1130 : Clause := ⟨[.fixed "0101111011111001110110", .any 10], 1130, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size_1_", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_special_recip_fp16_sisd_decode"⟩
theorem checked1130 : check raw1130 clause1130 = true := by rfl
def row1130 : Row := ⟨1130, 4294966272, 1593432064⟩
theorem derived1130 : clause1130.row = row1130 := by rfl
def entry1130 : CheckedRow := ⟨raw1130, clause1130, row1130, checked1130, derived1130⟩

def raw1131 : List String := ["function clause decode64 ((", "0b", "110101010001", " @ ", "_ : bits(", "20", ")", " as op_code) if SEE < ", "1131", ") = {\n    SEE = ", "1131", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "19", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_register_system_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "o0", ", ", "L", ")\n}\n"]
def clause1131 : Clause := ⟨[.fixed "110101010001", .any 20], 1131, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"o0", 1, 19, 19, true⟩, ⟨"L", 1, 21, 21, true⟩], "system_register_system_decode"⟩
theorem checked1131 : check raw1131 clause1131 = true := by rfl
def row1131 : Row := ⟨1131, 4293918720, 3574595584⟩
theorem derived1131 : clause1131.row = row1131 := by rfl
def entry1131 : CheckedRow := ⟨raw1131, clause1131, row1131, checked1131, derived1131⟩

def raw1132 : List String := ["function clause decode64 ((", "0b", "01111111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1111", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1132", ") = {\n    SEE = ", "1132", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_high_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "S", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1132 : Clause := ⟨[.fixed "01111111", .any 8, .fixed "1111", .any 1, .fixed "0", .any 10], 1132, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"S", 1, 13, 13, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mulacc_high_sisd_decode"⟩
theorem checked1132 : check raw1132 clause1132 = true := by rfl
def row1132 : Row := ⟨1132, 4278252544, 2130767872⟩
theorem derived1132 : clause1132.row = row1132 := by rfl
def entry1132 : CheckedRow := ⟨raw1132, clause1132, row1132, checked1132, derived1132⟩

def raw1133 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011111", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "1001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1133", ") = {\n    SEE = ", "1133", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1133 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011111", .any 7, .fixed "1001", .any 1, .fixed "0", .any 10], 1133, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mul_fp_simd_decode"⟩
theorem checked1133 : check raw1133 clause1133 = true := by rfl
def row1133 : Row := ⟨1133, 3212899328, 796954624⟩
theorem derived1133 : clause1133.row = row1133 := by rfl
def entry1133 : CheckedRow := ⟨raw1133, clause1133, row1133, checked1133, derived1133⟩

def raw1134 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1111010010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "4", ")", " as op_code) if SEE < ", "1134", ") = {\n    SEE = ", "1134", ";\n", "    ", "nzcv", " : bits(", "4", ") = ", "op_code[", "3", " .. ", "0", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "4", "]]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_conditional_compare_register_decode", "(", "nzcv", ", ", "o3", ", ", "Rn", ", ", "o2", ", ", "cond", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1134 : Clause := ⟨[.any 1, .fixed "1111010010", .any 9, .fixed "00", .any 5, .fixed "0", .any 4], 1134, [⟨"nzcv", 4, 3, 0, false⟩, ⟨"o3", 1, 4, 4, true⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o2", 1, 10, 10, true⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_conditional_compare_register_decode"⟩
theorem checked1134 : check raw1134 clause1134 = true := by rfl
def row1134 : Row := ⟨1134, 2145389584, 2051014656⟩
theorem derived1134 : clause1134.row = row1134 := by rfl
def entry1134 : CheckedRow := ⟨raw1134, clause1134, row1134, checked1134, derived1134⟩

def raw1135 : List String := ["function clause decode64 ((", "0b", "01111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1135", ") = {\n    SEE = ", "1135", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1135 : Clause := ⟨[.fixed "01111000", .any 2, .fixed "1", .any 5, .fixed "010100", .any 10], 1135, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1135 : check raw1135 clause1135 = true := by rfl
def row1135 : Row := ⟨1135, 4280351744, 2015383552⟩
theorem derived1135 : clause1135.row = row1135 := by rfl
def entry1135 : CheckedRow := ⟨raw1135, clause1135, row1135, checked1135, derived1135⟩

def raw1136 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1136", ") = {\n    SEE = ", "1136", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_conditional_select_decode", "(", "Rd", ", ", "Rn", ", ", "o2", ", ", "cond", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1136 : Clause := ⟨[.any 1, .fixed "0011010100", .any 9, .fixed "01", .any 10], 1136, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o2", 1, 10, 10, true⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_conditional_select_decode"⟩
theorem checked1136 : check raw1136 clause1136 = true := by rfl
def row1136 : Row := ⟨1136, 2145389568, 444597248⟩
theorem derived1136 : clause1136.row = row1136 := by rfl
def entry1136 : CheckedRow := ⟨raw1136, clause1136, row1136, checked1136, derived1136⟩

def raw1137 : List String := ["function clause decode64 ((", "0b", "10011000", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1137", ") = {\n    SEE = ", "1137", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm19", " : bits(", "19", ") = ", "op_code[", "23", " .. ", "5", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_literal_general_decode", "(", "Rt", ", ", "imm19", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1137 : Clause := ⟨[.fixed "10011000", .any 24], 1137, [⟨"Rt", 5, 4, 0, false⟩, ⟨"imm19", 19, 23, 5, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_literal_general_decode"⟩
theorem checked1137 : check raw1137 clause1137 = true := by rfl
def row1137 : Row := ⟨1137, 4278190080, 2550136832⟩
theorem derived1137 : clause1137.row = row1137 := by rfl
def entry1137 : CheckedRow := ⟨raw1137, clause1137, row1137, checked1137, derived1137⟩

def entries13 : List CheckedRow := [entry1130, entry1131, entry1132, entry1133, entry1134, entry1135, entry1136, entry1137]
def rows13 : List Row := [row1130, row1131, row1132, row1133, row1134, row1135, row1136, row1137]
theorem indices13 : rows13.map Row.index = [1130, 1131, 1132, 1133, 1134, 1135, 1136, 1137] := by rfl
theorem bound13 : entries13.map CheckedRow.row = rows13 := by rfl
theorem choices_and_13 : choices rows13 167837696#32 (-1) = [] := by rfl
theorem choices_orr_13 : choices rows13 704708608#32 (-1) = [] := by rfl
theorem choices_eor_13 : choices rows13 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_13 : choices rows13 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
