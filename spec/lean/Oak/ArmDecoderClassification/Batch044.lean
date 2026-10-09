import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1378 : List String := ["function clause decode64 ((", "0b", "001110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1378", ") = {\n    SEE = ", "1378", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1378 : Clause := ⟨[.fixed "001110000", .any 1, .fixed "1", .any 5, .fixed "011100", .any 5, .fixed "11111"], 1378, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1378 : check raw1378 clause1378 = true := by rfl
def row1378 : Row := ⟨1378, 4288740383, 941649951⟩
theorem derived1378 : clause1378.row = row1378 := by rfl
def entry1378 : CheckedRow := ⟨raw1378, clause1378, row1378, checked1378, derived1378⟩

def raw1379 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1379", ") = {\n    SEE = ", "1379", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_saturating_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1379 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "001011", .any 10], 1379, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_sub_saturating_simd_decode"⟩
theorem checked1379 : check raw1379 clause1379 = true := by rfl
def row1379 : Row := ⟨1379, 3206609920, 236989440⟩
theorem derived1379 : clause1379.row = row1379 := by rfl
def entry1379 : CheckedRow := ⟨raw1379, clause1379, row1379, checked1379, derived1379⟩

def raw1380 : List String := ["function clause decode64 ((", "0b", "0100111000101000010110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1380", ") = {\n    SEE = ", "1380", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "D", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_aes_round_decode", "(", "Rd", ", ", "Rn", ", ", "D", ", ", "size", ")\n}\n"]
def clause1380 : Clause := ⟨[.fixed "0100111000101000010110", .any 10], 1380, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"D", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_aes_round_decode"⟩
theorem checked1380 : check raw1380 clause1380 = true := by rfl
def row1380 : Row := ⟨1380, 4294966272, 1311266816⟩
theorem derived1380 : clause1380.row = row1380 := by rfl
def entry1380 : CheckedRow := ⟨raw1380, clause1380, row1380, checked1380, derived1380⟩

def raw1381 : List String := ["function clause decode64 ((", "0b", "010111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1381", ") = {\n    SEE = ", "1381", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1381 : Clause := ⟨[.fixed "010111100", .any 1, .fixed "100001110110", .any 10], 1381, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_int_sisd_decode"⟩
theorem checked1381 : check raw1381 clause1381 = true := by rfl
def row1381 : Row := ⟨1381, 4290771968, 1579276288⟩
theorem derived1381 : clause1381.row = row1381 := by rfl
def entry1381 : CheckedRow := ⟨raw1381, clause1381, row1381, checked1381, derived1381⟩

def raw1382 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110001", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1382", ") = {\n    SEE = ", "1382", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_logical_andorr_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1382 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110001", .any 5, .fixed "000111", .any 10], 1382, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_logical_andorr_decode"⟩
theorem checked1382 : check raw1382 clause1382 = true := by rfl
def row1382 : Row := ⟨1382, 3219192832, 236985344⟩
theorem derived1382 : clause1382.row = row1382 := by rfl
def entry1382 : CheckedRow := ⟨raw1382, clause1382, row1382, checked1382, derived1382⟩

def raw1383 : List String := ["function clause decode64 ((", "0b", "01111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1383", ") = {\n    SEE = ", "1383", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1383 : Clause := ⟨[.fixed "01111000000", .any 9, .fixed "11", .any 10], 1383, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1383 : check raw1383 clause1383 = true := by rfl
def row1383 : Row := ⟨1383, 4292873216, 2013268992⟩
theorem derived1383 : clause1383.row = row1383 := by rfl
def entry1383 : CheckedRow := ⟨raw1383, clause1383, row1383, checked1383, derived1383⟩

def raw1384 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1384", ") = {\n    SEE = ", "1384", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1384 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110110", .any 5, .fixed "001101", .any 10], 1384, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode"⟩
theorem checked1384 : check raw1384 clause1384 = true := by rfl
def row1384 : Row := ⟨1384, 3219192832, 247477248⟩
theorem derived1384 : clause1384.row = row1384 := by rfl
def entry1384 : CheckedRow := ⟨raw1384, clause1384, row1384, checked1384, derived1384⟩

def raw1385 : List String := ["function clause decode64 ((", "0b", "0101111001111001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1385", ") = {\n    SEE = ", "1385", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1385 : Clause := ⟨[.fixed "0101111001111001101010", .any 10], 1385, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode"⟩
theorem checked1385 : check raw1385 clause1385 = true := by rfl
def row1385 : Row := ⟨1385, 4294966272, 1585031168⟩
theorem derived1385 : clause1385.row = row1385 := by rfl
def entry1385 : CheckedRow := ⟨raw1385, clause1385, row1385, checked1385, derived1385⟩

def entries44 : List CheckedRow := [entry1378, entry1379, entry1380, entry1381, entry1382, entry1383, entry1384, entry1385]
def rows44 : List Row := [row1378, row1379, row1380, row1381, row1382, row1383, row1384, row1385]
theorem indices44 : rows44.map Row.index = [1378, 1379, 1380, 1381, 1382, 1383, 1384, 1385] := by rfl
theorem bound44 : entries44.map CheckedRow.row = rows44 := by rfl
theorem choices_and_44 : choices rows44 167837696#32 (-1) = [] := by rfl
theorem choices_orr_44 : choices rows44 704708608#32 (-1) = [] := by rfl
theorem choices_eor_44 : choices rows44 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_44 : choices rows44 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
