import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1090 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1090", ") = {\n    SEE = ", "1090", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1090 : Clause := ⟨[.fixed "1", .any 1, .fixed "1110000", .any 1, .fixed "1", .any 5, .fixed "001100", .any 5, .fixed "11111"], 1090, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1090 : check raw1090 clause1090 = true := by rfl
def row1090 : Row := ⟨1090, 3214998559, 3089117215⟩
theorem derived1090 : clause1090.row = row1090 := by rfl
def entry1090 : CheckedRow := ⟨raw1090, clause1090, row1090, checked1090, derived1090⟩

def raw1091 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111010110000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1091", ") = {\n    SEE = ", "1091", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_fp16max_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1091 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111010110000111110", .any 10], 1091, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_fp16max_simd_decode"⟩
theorem checked1091 : check raw1091 clause1091 = true := by rfl
def row1091 : Row := ⟨1091, 3221224448, 246478848⟩
theorem derived1091 : clause1091.row = row1091 := by rfl
def entry1091 : CheckedRow := ⟨raw1091, clause1091, row1091, checked1091, derived1091⟩

def raw1092 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0001011001", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1092", ") = {\n    SEE = ", "1092", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm3", " : bits(", "3", ") = ", "op_code[", "12", " .. ", "10", "]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opt", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_extendedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm3", ", ", "option_name", ", ", "Rm", ", ", "opt", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1092 : Clause := ⟨[.any 1, .fixed "0001011001", .any 21], 1092, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm3", 3, 12, 10, false⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opt", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_extendedreg_decode"⟩
theorem checked1092 : check raw1092 clause1092 = true := by rfl
def row1092 : Row := ⟨1092, 2145386496, 186646528⟩
theorem derived1092 : clause1092.row = row1092 := by rfl
def entry1092 : CheckedRow := ⟨raw1092, clause1092, row1092, checked1092, derived1092⟩

def raw1093 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111100000", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1093", ") = {\n    SEE = ", "1093", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "h", " : bits(", "1", ") = ", "[op_code[", "5", "]]", ";\n", "    ", "g", " : bits(", "1", ") = ", "[op_code[", "6", "]]", ";\n", "    ", "f", " : bits(", "1", ") = ", "[op_code[", "7", "]]", ";\n", "    ", "e", " : bits(", "1", ") = ", "[op_code[", "8", "]]", ";\n", "    ", "d", " : bits(", "1", ") = ", "[op_code[", "9", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "cmode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "c", " : bits(", "1", ") = ", "[op_code[", "16", "]]", ";\n", "    ", "b", " : bits(", "1", ") = ", "[op_code[", "17", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "18", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_logical_decode", "(", "Rd", ", ", "h", ", ", "g", ", ", "f", ", ", "e", ", ", "d", ", ", "o2", ", ", "cmode", ", ", "c", ", ", "b", ", ", "a", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1093 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111100000", .any 6, .fixed "101", .any 10], 1093, [⟨"Rd", 5, 4, 0, false⟩, ⟨"h", 1, 5, 5, true⟩, ⟨"g", 1, 6, 6, true⟩, ⟨"f", 1, 7, 7, true⟩, ⟨"e", 1, 8, 8, true⟩, ⟨"d", 1, 9, 9, true⟩, ⟨"o2", 1, 11, 11, true⟩, ⟨"cmode", 4, 15, 12, false⟩, ⟨"c", 1, 16, 16, true⟩, ⟨"b", 1, 17, 17, true⟩, ⟨"a", 1, 18, 18, true⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_logical_decode"⟩
theorem checked1093 : check raw1093 clause1093 = true := by rfl
def row1093 : Row := ⟨1093, 3220708352, 251663360⟩
theorem derived1093 : clause1093.row = row1093 := by rfl
def entry1093 : CheckedRow := ⟨raw1093, clause1093, row1093, checked1093, derived1093⟩

def raw1094 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1094", ") = {\n    SEE = ", "1094", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp_2008_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1094 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "1", .any 5, .fixed "110001", .any 10], 1094, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp_2008_decode"⟩
theorem checked1094 : check raw1094 clause1094 = true := by rfl
def row1094 : Row := ⟨1094, 3214998528, 782287872⟩
theorem derived1094 : clause1094.row = row1094 := by rfl
def entry1094 : CheckedRow := ⟨raw1094, clause1094, row1094, checked1094, derived1094⟩

def raw1095 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011011000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1095", ") = {\n    SEE = ", "1095", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op31", " : bits(", "3", ") = ", "op_code[", "23", " .. ", "21", "]", ";\n", "    ", "op54", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_mul_uniform_addsub_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "op31", ", ", "op54", ", ", "sf", ")\n}\n"]
def clause1095 : Clause := ⟨[.any 1, .fixed "0011011000", .any 5, .fixed "1", .any 15], 1095, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"op31", 3, 23, 21, false⟩, ⟨"op54", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_mul_uniform_addsub_decode"⟩
theorem checked1095 : check raw1095 clause1095 = true := by rfl
def row1095 : Row := ⟨1095, 2145419264, 453017600⟩
theorem derived1095 : clause1095.row = row1095 := by rfl
def entry1095 : CheckedRow := ⟨raw1095, clause1095, row1095, checked1095, derived1095⟩

def raw1096 : List String := ["function clause decode64 ((", "0b", "00001000100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1096", ") = {\n    SEE = ", "1096", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_ordered_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1096 : Clause := ⟨[.fixed "00001000100", .any 5, .fixed "0", .any 15], 1096, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_ordered_decode"⟩
theorem checked1096 : check raw1096 clause1096 = true := by rfl
def row1096 : Row := ⟨1096, 4292902912, 142606336⟩
theorem derived1096 : clause1096.row = row1096 := by rfl
def entry1096 : CheckedRow := ⟨raw1096, clause1096, row1096, checked1096, derived1096⟩

def raw1097 : List String := ["function clause decode64 ((", "0b", "0101111000110000110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1097", ") = {\n    SEE = ", "1097", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fp16add_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1097 : Clause := ⟨[.fixed "0101111000110000110110", .any 10], 1097, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fp16add_sisd_decode"⟩
theorem checked1097 : check raw1097 clause1097 = true := by rfl
def row1097 : Row := ⟨1097, 4294966272, 1580259328⟩
theorem derived1097 : clause1097.row = row1097 := by rfl
def entry1097 : CheckedRow := ⟨raw1097, clause1097, row1097, checked1097, derived1097⟩

def entries8 : List CheckedRow := [entry1090, entry1091, entry1092, entry1093, entry1094, entry1095, entry1096, entry1097]
def rows8 : List Row := [row1090, row1091, row1092, row1093, row1094, row1095, row1096, row1097]
theorem indices8 : rows8.map Row.index = [1090, 1091, 1092, 1093, 1094, 1095, 1096, 1097] := by rfl
theorem bound8 : entries8.map CheckedRow.row = rows8 := by rfl
theorem choices_and_8 : choices rows8 167837696#32 (-1) = [] := by rfl
theorem choices_orr_8 : choices rows8 704708608#32 (-1) = [] := by rfl
theorem choices_eor_8 : choices rows8 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_8 : choices rows8 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
