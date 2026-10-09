import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1410 : List String := ["function clause decode64 ((", "0b", "11001110100", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1410", ") = {\n    SEE = ", "1410", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "vector_crypto_sha3_xar_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ")\n}\n"]
def clause1410 : Clause := ⟨[.fixed "11001110100", .any 21], 1410, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩], "vector_crypto_sha3_xar_decode"⟩
theorem checked1410 : check raw1410 clause1410 = true := by rfl
def row1410 : Row := ⟨1410, 4292870144, 3464495104⟩
theorem derived1410 : clause1410.row = row1410 := by rfl
def entry1410 : CheckedRow := ⟨raw1410, clause1410, row1410, checked1410, derived1410⟩

def raw1411 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000001010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1411", ") = {\n    SEE = ", "1411", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_add_pairwise_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1411 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000001010", .any 10], 1411, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_add_pairwise_decode"⟩
theorem checked1411 : check raw1411 clause1411 = true := by rfl
def row1411 : Row := ⟨1411, 3208641536, 236988416⟩
theorem derived1411 : clause1411.row = row1411 := by rfl
def entry1411 : CheckedRow := ⟨raw1411, clause1411, row1411, checked1411, derived1411⟩

def raw1412 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1412", ") = {\n    SEE = ", "1412", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_addsub_long_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1412 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "001000", .any 10], 1412, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_addsub_long_decode"⟩
theorem checked1412 : check raw1412 clause1412 = true := by rfl
def row1412 : Row := ⟨1412, 3206609920, 236986368⟩
theorem derived1412 : clause1412.row = row1412 := by rfl
def entry1412 : CheckedRow := ⟨raw1412, clause1412, row1412, checked1412, derived1412⟩

def raw1413 : List String := ["function clause decode64 ((", "0b", "011110011", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1413", ") = {\n    SEE = ", "1413", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1413 : Clause := ⟨[.fixed "011110011", .any 23], 1413, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1413 : check raw1413 clause1413 = true := by rfl
def row1413 : Row := ⟨1413, 4286578688, 2038431744⟩
theorem derived1413 : clause1413.row = row1413 := by rfl
def entry1413 : CheckedRow := ⟨raw1413, clause1413, row1413, checked1413, derived1413⟩

def raw1414 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1414", ") = {\n    SEE = ", "1414", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1414 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "1", .any 5, .fixed "110101", .any 10], 1414, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_sub_fp_simd_decode"⟩
theorem checked1414 : check raw1414 clause1414 = true := by rfl
def row1414 : Row := ⟨1414, 3214998528, 782291968⟩
theorem derived1414 : clause1414.row = row1414 := by rfl
def entry1414 : CheckedRow := ⟨raw1414, clause1414, row1414, checked1414, derived1414⟩

def raw1415 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "00100110", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1415", ") = {\n    SEE = ", "1415", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imms", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "immr", " : bits(", "6", ") = ", "op_code[", "21", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_bitfield_decode", "(", "Rd", ", ", "Rn", ", ", "imms", ", ", "immr", ", ", "N", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1415 : Clause := ⟨[.any 1, .fixed "00100110", .any 23], 1415, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imms", 6, 15, 10, false⟩, ⟨"immr", 6, 21, 16, false⟩, ⟨"N", 1, 22, 22, true⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_bitfield_decode"⟩
theorem checked1415 : check raw1415 clause1415 = true := by rfl
def row1415 : Row := ⟨1415, 2139095040, 318767104⟩
theorem derived1415 : clause1415.row = row1415 := by rfl
def entry1415 : CheckedRow := ⟨raw1415, clause1415, row1415, checked1415, derived1415⟩

def raw1416 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1416", ") = {\n    SEE = ", "1416", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_right_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1416 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "000101", .any 10], 1416, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_right_simd_decode"⟩
theorem checked1416 : check raw1416 clause1416 = true := by rfl
def row1416 : Row := ⟨1416, 3212901376, 251663360⟩
theorem derived1416 : clause1416.row = row1416 := by rfl
def entry1416 : CheckedRow := ⟨raw1416, clause1416, row1416, checked1416, derived1416⟩

def raw1417 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1417", ") = {\n    SEE = ", "1417", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_high_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "S", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1417 : Clause := ⟨[.fixed "0", .any 1, .fixed "101111", .any 8, .fixed "1101", .any 1, .fixed "0", .any 10], 1417, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"S", 1, 13, 13, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_high_simd_decode"⟩
theorem checked1417 : check raw1417 clause1417 = true := by rfl
def row1417 : Row := ⟨1417, 3204510720, 788582400⟩
theorem derived1417 : clause1417.row = row1417 := by rfl
def entry1417 : CheckedRow := ⟨raw1417, clause1417, row1417, checked1417, derived1417⟩

def entries48 : List CheckedRow := [entry1410, entry1411, entry1412, entry1413, entry1414, entry1415, entry1416, entry1417]
def rows48 : List Row := [row1410, row1411, row1412, row1413, row1414, row1415, row1416, row1417]
theorem indices48 : rows48.map Row.index = [1410, 1411, 1412, 1413, 1414, 1415, 1416, 1417] := by rfl
theorem bound48 : entries48.map CheckedRow.row = rows48 := by rfl
theorem choices_and_48 : choices rows48 167837696#32 (-1) = [] := by rfl
theorem choices_orr_48 : choices rows48 704708608#32 (-1) = [] := by rfl
theorem choices_eor_48 : choices rows48 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_48 : choices rows48 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
