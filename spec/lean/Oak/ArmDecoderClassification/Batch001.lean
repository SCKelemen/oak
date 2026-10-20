import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1034 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111100000", " @ ", "_ : bits(", "3", ")", " @ ", "0b", "111111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1034", ") = {\n    SEE = ", "1034", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "h", " : bits(", "1", ") = ", "[op_code[", "5", "]]", ";\n", "    ", "g", " : bits(", "1", ") = ", "[op_code[", "6", "]]", ";\n", "    ", "f", " : bits(", "1", ") = ", "[op_code[", "7", "]]", ";\n", "    ", "e", " : bits(", "1", ") = ", "[op_code[", "8", "]]", ";\n", "    ", "d", " : bits(", "1", ") = ", "[op_code[", "9", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "cmode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "c", " : bits(", "1", ") = ", "[op_code[", "16", "]]", ";\n", "    ", "b", " : bits(", "1", ") = ", "[op_code[", "17", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "18", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_fp16_movi_decode", "(", "Rd", ", ", "h", ", ", "g", ", ", "f", ", ", "e", ", ", "d", ", ", "o2", ", ", "cmode", ", ", "c", ", ", "b", ", ", "a", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1034 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111100000", .any 3, .fixed "111111", .any 10], 1034, [⟨"Rd", 5, 4, 0, false⟩, ⟨"h", 1, 5, 5, true⟩, ⟨"g", 1, 6, 6, true⟩, ⟨"f", 1, 7, 7, true⟩, ⟨"e", 1, 8, 8, true⟩, ⟨"d", 1, 9, 9, true⟩, ⟨"o2", 1, 11, 11, true⟩, ⟨"cmode", 4, 15, 12, false⟩, ⟨"c", 1, 16, 16, true⟩, ⟨"b", 1, 17, 17, true⟩, ⟨"a", 1, 18, 18, true⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_fp16_movi_decode"⟩
theorem checked1034 : check raw1034 clause1034 = true := by rfl
def row1034 : Row := ⟨1034, 3220765696, 251722752⟩
theorem derived1034 : clause1034.row = row1034 := by rfl
def entry1034 : CheckedRow := ⟨raw1034, clause1034, row1034, checked1034, derived1034⟩

def raw1035 : List String := ["function clause decode64 ((", "0b", "0110100100", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1035", ") = {\n    SEE = ", "1035", ";\n", "    ", "Xt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Xt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "simm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "integer_tags_mcsettaganddatapair_decode", "(", "Xt", ", ", "Xn", ", ", "Xt2", ", ", "simm7", ")\n}\n"]
def clause1035 : Clause := ⟨[.fixed "0110100100", .any 22], 1035, [⟨"Xt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"Xt2", 5, 14, 10, false⟩, ⟨"simm7", 7, 21, 15, false⟩], "integer_tags_mcsettaganddatapair_decode"⟩
theorem checked1035 : check raw1035 clause1035 = true := by rfl
def row1035 : Row := ⟨1035, 4290772992, 1761607680⟩
theorem derived1035 : clause1035.row = row1035 := by rfl
def entry1035 : CheckedRow := ⟨raw1035, clause1035, row1035, checked1035, derived1035⟩

def raw1036 : List String := ["function clause decode64 ((", "0b", "110110101100000100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1036", ") = {\n    SEE = ", "1036", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_autib_dp_1src_decode", "(", "Rd", ", ", "Rn", ", ", "Z", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1036 : Clause := ⟨[.fixed "110110101100000100", .any 1, .fixed "101", .any 10], 1036, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Z", 1, 13, 13, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_autib_dp_1src_decode"⟩
theorem checked1036 : check raw1036 clause1036 = true := by rfl
def row1036 : Row := ⟨1036, 4294958080, 3670086656⟩
theorem derived1036 : clause1036.row = row1036 := by rfl
def entry1036 : CheckedRow := ⟨raw1036, clause1036, row1036, checked1036, derived1036⟩

def raw1037 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1037", ") = {\n    SEE = ", "1037", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "eq", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "eq", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1037 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "001101", .any 10], 1037, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"eq", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_int_simd_decode"⟩
theorem checked1037 : check raw1037 clause1037 = true := by rfl
def row1037 : Row := ⟨1037, 3206609920, 236991488⟩
theorem derived1037 : clause1037.row = row1037 := by rfl
def entry1037 : CheckedRow := ⟨raw1037, clause1037, row1037, checked1037, derived1037⟩

def raw1038 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1038", ") = {\n    SEE = ", "1038", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1038 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110110", .any 5, .fixed "000101", .any 10], 1038, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_sub_fp16_simd_decode"⟩
theorem checked1038 : check raw1038 clause1038 = true := by rfl
def row1038 : Row := ⟨1038, 3219192832, 247469056⟩
theorem derived1038 : clause1038.row = row1038 := by rfl
def entry1038 : CheckedRow := ⟨raw1038, clause1038, row1038, checked1038, derived1038⟩

def raw1039 : List String := ["function clause decode64 ((", "0b", "0111111100", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "1001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1039", ") = {\n    SEE = ", "1039", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1039 : Clause := ⟨[.fixed "0111111100", .any 6, .fixed "1001", .any 1, .fixed "0", .any 10], 1039, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mul_fp16_sisd_decode"⟩
theorem checked1039 : check raw1039 clause1039 = true := by rfl
def row1039 : Row := ⟨1039, 4290835456, 2130743296⟩
theorem derived1039 : clause1039.row = row1039 := by rfl
def entry1039 : CheckedRow := ⟨raw1039, clause1039, row1039, checked1039, derived1039⟩

def raw1040 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110011", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1040", ") = {\n    SEE = ", "1040", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_logical_andorr_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1040 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110011", .any 5, .fixed "000111", .any 10], 1040, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_logical_andorr_decode"⟩
theorem checked1040 : check raw1040 clause1040 = true := by rfl
def row1040 : Row := ⟨1040, 3219192832, 241179648⟩
theorem derived1040 : clause1040.row = row1040 := by rfl
def entry1040 : CheckedRow := ⟨raw1040, clause1040, row1040, checked1040, derived1040⟩

def raw1041 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1041", ") = {\n    SEE = ", "1041", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_halving_truncating_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1041 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "000001", .any 10], 1041, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_halving_truncating_decode"⟩
theorem checked1041 : check raw1041 clause1041 = true := by rfl
def row1041 : Row := ⟨1041, 3206609920, 773850112⟩
theorem derived1041 : clause1041.row = row1041 := by rfl
def entry1041 : CheckedRow := ⟨raw1041, clause1041, row1041, checked1041, derived1041⟩

def entries1 : List CheckedRow := [entry1034, entry1035, entry1036, entry1037, entry1038, entry1039, entry1040, entry1041]
def rows1 : List Row := [row1034, row1035, row1036, row1037, row1038, row1039, row1040, row1041]
theorem indices1 : rows1.map Row.index = [1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041] := by rfl
theorem bound1 : entries1.map CheckedRow.row = rows1 := by rfl
theorem choices_and_1 : choices rows1 167837696#32 (-1) = [] := by rfl
theorem choices_orr_1 : choices rows1 704708608#32 (-1) = [] := by rfl
theorem choices_eor_1 : choices rows1 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_1 : choices rows1 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
