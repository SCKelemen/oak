import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1354 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1354", ") = {\n    SEE = ", "1354", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1354 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "100001101010", .any 10], 1354, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_simd_decode"⟩
theorem checked1354 : check raw1354 clause1354 = true := by rfl
def row1354 : Row := ⟨1354, 3217030144, 782346240⟩
theorem derived1354 : clause1354.row = row1354 := by rfl
def entry1354 : CheckedRow := ⟨raw1354, clause1354, row1354, checked1354, derived1354⟩

def raw1355 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "010101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1355", ") = {\n    SEE = ", "1355", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_leftinsert_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1355 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "010101", .any 10], 1355, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_leftinsert_sisd_decode"⟩
theorem checked1355 : check raw1355 clause1355 = true := by rfl
def row1355 : Row := ⟨1355, 4286643200, 2130727936⟩
theorem derived1355 : clause1355.row = row1355 := by rfl
def entry1355 : CheckedRow := ⟨raw1355, clause1355, row1355, checked1355, derived1355⟩

def raw1356 : List String := ["function clause decode64 ((", "0b", "1101000110", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1356", ") = {\n    SEE = ", "1356", ";\n", "    ", "Xd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "uimm4", " : bits(", "4", ") = ", "op_code[", "13", " .. ", "10", "]", ";\n", "    ", "op3", " : bits(", "2", ") = ", "op_code[", "15", " .. ", "14", "]", ";\n", "    ", "uimm6", " : bits(", "6", ") = ", "op_code[", "21", " .. ", "16", "]", ";\n", "    ", "integer_tags_mcsubtag_decode", "(", "Xd", ", ", "Xn", ", ", "uimm4", ", ", "op3", ", ", "uimm6", ")\n}\n"]
def clause1356 : Clause := ⟨[.fixed "1101000110", .any 22], 1356, [⟨"Xd", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"uimm4", 4, 13, 10, false⟩, ⟨"op3", 2, 15, 14, false⟩, ⟨"uimm6", 6, 21, 16, false⟩], "integer_tags_mcsubtag_decode"⟩
theorem checked1356 : check raw1356 clause1356 = true := by rfl
def row1356 : Row := ⟨1356, 4290772992, 3514826752⟩
theorem derived1356 : clause1356.row = row1356 := by rfl
def entry1356 : CheckedRow := ⟨raw1356, clause1356, row1356, checked1356, derived1356⟩

def raw1357 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "010100100", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1357", ") = {\n    SEE = ", "1357", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_general_offset_memory_pair_general_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1357 : Clause := ⟨[.any 1, .fixed "010100100", .any 22], 1357, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_general_offset_memory_pair_general_postidx__decode"⟩
theorem checked1357 : check raw1357 clause1357 = true := by rfl
def row1357 : Row := ⟨1357, 2143289344, 687865856⟩
theorem derived1357 : clause1357.row = row1357 := by rfl
def entry1357 : CheckedRow := ⟨raw1357, clause1357, row1357, checked1357, derived1357⟩

def raw1358 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001010000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1358", ") = {\n    SEE = ", "1358", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "16", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_unary_decode", "(", "Rd", ", ", "Rn", ", ", "opc", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1358 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100001010000", .any 10], 1358, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 2, 16, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_unary_decode"⟩
theorem checked1358 : check raw1358 clause1358 = true := by rfl
def row1358 : Row := ⟨1358, 4282383360, 505495552⟩
theorem derived1358 : clause1358.row = row1358 := by rfl
def entry1358 : CheckedRow := ⟨raw1358, clause1358, row1358, checked1358, derived1358⟩

def raw1359 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1359", ") = {\n    SEE = ", "1359", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "E", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1359 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110110", .any 5, .fixed "001011", .any 10], 1359, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_fp16_simd_decode"⟩
theorem checked1359 : check raw1359 clause1359 = true := by rfl
def row1359 : Row := ⟨1359, 3219192832, 784346112⟩
theorem derived1359 : clause1359.row = row1359 := by rfl
def entry1359 : CheckedRow := ⟨raw1359, clause1359, row1359, checked1359, derived1359⟩

def raw1360 : List String := ["function clause decode64 ((", "0b", "011110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1360", ") = {\n    SEE = ", "1360", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1360 : Clause := ⟨[.fixed "011110000", .any 1, .fixed "1", .any 5, .fixed "001000", .any 5, .fixed "11111"], 1360, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1360 : check raw1360 clause1360 = true := by rfl
def row1360 : Row := ⟨1360, 4288740383, 2015371295⟩
theorem derived1360 : clause1360.row = row1360 := by rfl
def entry1360 : CheckedRow := ⟨raw1360, clause1360, row1360, checked1360, derived1360⟩

def raw1361 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1361", ") = {\n    SEE = ", "1361", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_rightnarrow_logical_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1361 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "100011", .any 10], 1361, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_rightnarrow_logical_decode"⟩
theorem checked1361 : check raw1361 clause1361 = true := by rfl
def row1361 : Row := ⟨1361, 3212901376, 251694080⟩
theorem derived1361 : clause1361.row = row1361 := by rfl
def entry1361 : CheckedRow := ⟨raw1361, clause1361, row1361, checked1361, derived1361⟩

def entries41 : List CheckedRow := [entry1354, entry1355, entry1356, entry1357, entry1358, entry1359, entry1360, entry1361]
def rows41 : List Row := [row1354, row1355, row1356, row1357, row1358, row1359, row1360, row1361]
theorem indices41 : rows41.map Row.index = [1354, 1355, 1356, 1357, 1358, 1359, 1360, 1361] := by rfl
theorem bound41 : entries41.map CheckedRow.row = rows41 := by rfl
theorem choices_and_41 : choices rows41 167837696#32 (-1) = [] := by rfl
theorem choices_orr_41 : choices rows41 704708608#32 (-1) = [] := by rfl
theorem choices_eor_41 : choices rows41 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_41 : choices rows41 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
