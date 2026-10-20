import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1314 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1314", ") = {\n    SEE = ", "1314", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_diff_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1314 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "010100", .any 10], 1314, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_diff_decode"⟩
theorem checked1314 : check raw1314 clause1314 = true := by rfl
def row1314 : Row := ⟨1314, 3206609920, 773869568⟩
theorem derived1314 : clause1314.row = row1314 := by rfl
def entry1314 : CheckedRow := ⟨raw1314, clause1314, row1314, checked1314, derived1314⟩

def raw1315 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001111", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1315", ") = {\n    SEE = ", "1315", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_round_frint_32_64_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1315 : Clause := ⟨[.fixed "0", .any 2, .fixed "011100", .any 1, .fixed "100001111", .any 1, .fixed "10", .any 10], 1315, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_round_frint_32_64_decode"⟩
theorem checked1315 : check raw1315 clause1315 = true := by rfl
def row1315 : Row := ⟨1315, 2680155136, 237103104⟩
theorem derived1315 : clause1315.row = row1315 := by rfl
def entry1315 : CheckedRow := ⟨raw1315, clause1315, row1315, checked1315, derived1315⟩

def raw1316 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1316", ") = {\n    SEE = ", "1316", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_div_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1316 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "000110", .any 10], 1316, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_div_decode"⟩
theorem checked1316 : check raw1316 clause1316 = true := by rfl
def row1316 : Row := ⟨1316, 4280351744, 505419776⟩
theorem derived1316 : clause1316.row = row1316 := by rfl
def entry1316 : CheckedRow := ⟨raw1316, clause1316, row1316, checked1316, derived1316⟩

def raw1317 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1317", ") = {\n    SEE = ", "1317", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "E", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1317 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110110", .any 5, .fixed "001001", .any 10], 1317, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_fp16_simd_decode"⟩
theorem checked1317 : check raw1317 clause1317 = true := by rfl
def row1317 : Row := ⟨1317, 3219192832, 784344064⟩
theorem derived1317 : clause1317.row = row1317 := by rfl
def entry1317 : CheckedRow := ⟨raw1317, clause1317, row1317, checked1317, derived1317⟩

def raw1318 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000100110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1318", ") = {\n    SEE = ", "1318", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ")\n}\n"]
def clause1318 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "100000100110", .any 10], 1318, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_int_bulk_sisd_decode"⟩
theorem checked1318 : check raw1318 clause1318 = true := by rfl
def row1318 : Row := ⟨1318, 4282383360, 2116065280⟩
theorem derived1318 : clause1318.row = row1318 := by rfl
def entry1318 : CheckedRow := ⟨raw1318, clause1318, row1318, checked1318, derived1318⟩

def raw1319 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0010000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "11111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1319", ") = {\n    SEE = ", "1319", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_atomicops_cas_pair_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "sz", ")\n}\n"]
def clause1319 : Clause := ⟨[.fixed "0", .any 1, .fixed "0010000", .any 1, .fixed "1", .any 6, .fixed "11111", .any 10], 1319, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"sz", 1, 30, 30, true⟩], "memory_atomicops_cas_pair_decode"⟩
theorem checked1319 : check raw1319 clause1319 = true := by rfl
def row1319 : Row := ⟨1319, 3214965760, 136346624⟩
theorem derived1319 : clause1319.row = row1319 := by rfl
def entry1319 : CheckedRow := ⟨raw1319, clause1319, row1319, checked1319, derived1319⟩

def raw1320 : List String := ["function clause decode64 ((", "0b", "010111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1320", ") = {\n    SEE = ", "1320", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_rightnarrow_uniform_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1320 : Clause := ⟨[.fixed "010111110", .any 7, .fixed "100111", .any 10], 1320, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_rightnarrow_uniform_sisd_decode"⟩
theorem checked1320 : check raw1320 clause1320 = true := by rfl
def row1320 : Row := ⟨1320, 4286643200, 1593875456⟩
theorem derived1320 : clause1320.row = row1320 := by rfl
def entry1320 : CheckedRow := ⟨raw1320, clause1320, row1320, checked1320, derived1320⟩

def raw1321 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111000110000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1321", ") = {\n    SEE = ", "1321", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_fp16max_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1321 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111000110000111110", .any 10], 1321, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_fp16max_simd_decode"⟩
theorem checked1321 : check raw1321 clause1321 = true := by rfl
def row1321 : Row := ⟨1321, 3221224448, 238090240⟩
theorem derived1321 : clause1321.row = row1321 := by rfl
def entry1321 : CheckedRow := ⟨raw1321, clause1321, row1321, checked1321, derived1321⟩

def entries36 : List CheckedRow := [entry1314, entry1315, entry1316, entry1317, entry1318, entry1319, entry1320, entry1321]
def rows36 : List Row := [row1314, row1315, row1316, row1317, row1318, row1319, row1320, row1321]
theorem indices36 : rows36.map Row.index = [1314, 1315, 1316, 1317, 1318, 1319, 1320, 1321] := by rfl
theorem bound36 : entries36.map CheckedRow.row = rows36 := by rfl
theorem choices_and_36 : choices rows36 167837696#32 (-1) = [] := by rfl
theorem choices_orr_36 : choices rows36 704708608#32 (-1) = [] := by rfl
theorem choices_eor_36 : choices rows36 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_36 : choices rows36 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
