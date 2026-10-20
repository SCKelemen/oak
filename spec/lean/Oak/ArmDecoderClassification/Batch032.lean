import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1282 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1101010", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1282", ") = {\n    SEE = ", "1282", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "N", ", ", "shift", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1282 : Clause := ⟨[.any 1, .fixed "1101010", .any 2, .fixed "1", .any 21], 1282, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"N", 1, 21, 21, true⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_shiftedreg_decode"⟩
theorem checked1282 : check raw1282 clause1282 = true := by rfl
def row1282 : Row := ⟨1282, 2132803584, 1780482048⟩
theorem derived1282 : clause1282.row = row1282 := by rfl
def entry1282 : CheckedRow := ⟨raw1282, clause1282, row1282, checked1282, derived1282⟩

def raw1283 : List String := ["function clause decode64 ((", "0b", "10011001100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1283", ") = {\n    SEE = ", "1283", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1283 : Clause := ⟨[.fixed "10011001100", .any 9, .fixed "00", .any 10], 1283, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1283 : check raw1283 clause1283 = true := by rfl
def row1283 : Row := ⟨1283, 4292873216, 2575302656⟩
theorem derived1283 : clause1283.row = row1283 := by rfl
def entry1283 : CheckedRow := ⟨raw1283, clause1283, row1283, checked1283, derived1283⟩

def raw1284 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011111", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "0001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1284", ") = {\n    SEE = ", "1284", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1284 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011111", .any 7, .fixed "0001", .any 1, .fixed "0", .any 10], 1284, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_fp_simd_decode"⟩
theorem checked1284 : check raw1284 clause1284 = true := by rfl
def row1284 : Row := ⟨1284, 3212899328, 260050944⟩
theorem derived1284 : clause1284.row = row1284 := by rfl
def entry1284 : CheckedRow := ⟨raw1284, clause1284, row1284, checked1284, derived1284⟩

def raw1285 : List String := ["function clause decode64 ((", "0b", "0111111011111001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1285", ") = {\n    SEE = ", "1285", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_special_sqrtest_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ")\n}\n"]
def clause1285 : Clause := ⟨[.fixed "0111111011111001110110", .any 10], 1285, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_special_sqrtest_fp16_sisd_decode"⟩
theorem checked1285 : check raw1285 clause1285 = true := by rfl
def row1285 : Row := ⟨1285, 4294966272, 2130302976⟩
theorem derived1285 : clause1285.row = row1285 := by rfl
def entry1285 : CheckedRow := ⟨raw1285, clause1285, row1285, checked1285, derived1285⟩

def raw1286 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0101010", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1286", ") = {\n    SEE = ", "1286", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "N", ", ", "shift", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1286 : Clause := ⟨[.any 1, .fixed "0101010", .any 2, .fixed "1", .any 21], 1286, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"N", 1, 21, 21, true⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_shiftedreg_decode"⟩
theorem checked1286 : check raw1286 clause1286 = true := by rfl
def row1286 : Row := ⟨1286, 2132803584, 706740224⟩
theorem derived1286 : clause1286.row = row1286 := by rfl
def entry1286 : CheckedRow := ⟨raw1286, clause1286, row1286, checked1286, derived1286⟩

def raw1287 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1287", ") = {\n    SEE = ", "1287", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_diff_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1287 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "011111", .any 10], 1287, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_diff_decode"⟩
theorem checked1287 : check raw1287 clause1287 = true := by rfl
def row1287 : Row := ⟨1287, 3206609920, 237009920⟩
theorem derived1287 : clause1287.row = row1287 := by rfl
def entry1287 : CheckedRow := ⟨raw1287, clause1287, row1287, checked1287, derived1287⟩

def raw1288 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000101", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1288", ") = {\n    SEE = ", "1288", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_orderedrcpc_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1288 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000101", .any 5, .fixed "110000", .any 10], 1288, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_orderedrcpc_decode"⟩
theorem checked1288 : check raw1288 clause1288 = true := by rfl
def row1288 : Row := ⟨1288, 3219192832, 3097542656⟩
theorem derived1288 : clause1288.row = row1288 := by rfl
def entry1288 : CheckedRow := ⟨raw1288, clause1288, row1288, checked1288, derived1288⟩

def raw1289 : List String := ["function clause decode64 ((", "0b", "0110100110", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1289", ") = {\n    SEE = ", "1289", ";\n", "    ", "Xt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Xt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "simm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "integer_tags_mcsettaganddatapairpre_decode", "(", "Xt", ", ", "Xn", ", ", "Xt2", ", ", "simm7", ")\n}\n"]
def clause1289 : Clause := ⟨[.fixed "0110100110", .any 22], 1289, [⟨"Xt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"Xt2", 5, 14, 10, false⟩, ⟨"simm7", 7, 21, 15, false⟩], "integer_tags_mcsettaganddatapairpre_decode"⟩
theorem checked1289 : check raw1289 clause1289 = true := by rfl
def row1289 : Row := ⟨1289, 4290772992, 1769996288⟩
theorem derived1289 : clause1289.row = row1289 := by rfl
def entry1289 : CheckedRow := ⟨raw1289, clause1289, row1289, checked1289, derived1289⟩

def entries32 : List CheckedRow := [entry1282, entry1283, entry1284, entry1285, entry1286, entry1287, entry1288, entry1289]
def rows32 : List Row := [row1282, row1283, row1284, row1285, row1286, row1287, row1288, row1289]
theorem indices32 : rows32.map Row.index = [1282, 1283, 1284, 1285, 1286, 1287, 1288, 1289] := by rfl
theorem bound32 : entries32.map CheckedRow.row = rows32 := by rfl
theorem choices_and_32 : choices rows32 167837696#32 (-1) = [] := by rfl
theorem choices_orr_32 : choices rows32 704708608#32 (-1) = [] := by rfl
theorem choices_eor_32 : choices rows32 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_32 : choices rows32 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
