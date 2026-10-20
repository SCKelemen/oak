import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1362 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111001111001100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1362", ") = {\n    SEE = ", "1362", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1362 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111001111001100010", .any 10], 1362, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_round_decode"⟩
theorem checked1362 : check raw1362 clause1362 = true := by rfl
def row1362 : Row := ⟨1362, 3221224448, 242845696⟩
theorem derived1362 : clause1362.row = row1362 := by rfl
def entry1362 : CheckedRow := ⟨raw1362, clause1362, row1362, checked1362, derived1362⟩

def raw1363 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1363", ") = {\n    SEE = ", "1363", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1363 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "1", .any 5, .fixed "010011", .any 10], 1363, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_shift_sisd_decode"⟩
theorem checked1363 : check raw1363 clause1363 = true := by rfl
def row1363 : Row := ⟨1363, 4280351744, 2116045824⟩
theorem derived1363 : clause1363.row = row1363 := by rfl
def entry1363 : CheckedRow := ⟨raw1363, clause1363, row1363, checked1363, derived1363⟩

def raw1364 : List String := ["function clause decode64 ((", "0b", "011111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1364", ") = {\n    SEE = ", "1364", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1364 : Clause := ⟨[.fixed "011111100", .any 1, .fixed "100001101110", .any 10], 1364, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode"⟩
theorem checked1364 : check raw1364 clause1364 = true := by rfl
def row1364 : Row := ⟨1364, 4290771968, 2116139008⟩
theorem derived1364 : clause1364.row = row1364 := by rfl
def entry1364 : CheckedRow := ⟨raw1364, clause1364, row1364, checked1364, derived1364⟩

def raw1365 : List String := ["function clause decode64 ((", "0b", "0110100111", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1365", ") = {\n    SEE = ", "1365", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_general_preidx_memory_pair_general_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1365 : Clause := ⟨[.fixed "0110100111", .any 22], 1365, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_general_preidx_memory_pair_general_postidx__decode"⟩
theorem checked1365 : check raw1365 clause1365 = true := by rfl
def row1365 : Row := ⟨1365, 4290772992, 1774190592⟩
theorem derived1365 : clause1365.row = row1365 := by rfl
def entry1365 : CheckedRow := ⟨raw1365, clause1365, row1365, checked1365, derived1365⟩

def raw1366 : List String := ["function clause decode64 ((", "0b", "00111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1366", ") = {\n    SEE = ", "1366", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1366 : Clause := ⟨[.fixed "00111000", .any 2, .fixed "1", .any 5, .fixed "001100", .any 10], 1366, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1366 : check raw1366 clause1366 = true := by rfl
def row1366 : Row := ⟨1366, 4280351744, 941633536⟩
theorem derived1366 : clause1366.row = row1366 := by rfl
def entry1366 : CheckedRow := ⟨raw1366, clause1366, row1366, checked1366, derived1366⟩

def raw1367 : List String := ["function clause decode64 ((", "0b", "11010101000000000100", " @ ", "_ : bits(", "4", ")", " @ ", "0b", "00111111", " as op_code) if SEE < ", "1367", ") = {\n    SEE = ", "1367", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "integer_flags_xaflag_decode", "(", "CRm", ")\n}\n"]
def clause1367 : Clause := ⟨[.fixed "11010101000000000100", .any 4, .fixed "00111111"], 1367, [⟨"CRm", 4, 11, 8, false⟩], "integer_flags_xaflag_decode"⟩
theorem checked1367 : check raw1367 clause1367 = true := by rfl
def row1367 : Row := ⟨1367, 4294963455, 3573563455⟩
theorem derived1367 : clause1367.row = row1367 := by rfl
def entry1367 : CheckedRow := ⟨raw1367, clause1367, row1367, checked1367, derived1367⟩

def raw1368 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111001111001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1368", ") = {\n    SEE = ", "1368", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1368 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111001111001101010", .any 10], 1368, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode"⟩
theorem checked1368 : check raw1368 clause1368 = true := by rfl
def row1368 : Row := ⟨1368, 3221224448, 779724800⟩
theorem derived1368 : clause1368.row = row1368 := by rfl
def entry1368 : CheckedRow := ⟨raw1368, clause1368, row1368, checked1368, derived1368⟩

def raw1369 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1369", ") = {\n    SEE = ", "1369", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1369 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "100001100010", .any 10], 1369, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_round_decode"⟩
theorem checked1369 : check raw1369 clause1369 = true := by rfl
def row1369 : Row := ⟨1369, 3217030144, 245467136⟩
theorem derived1369 : clause1369.row = row1369 := by rfl
def entry1369 : CheckedRow := ⟨raw1369, clause1369, row1369, checked1369, derived1369⟩

def entries42 : List CheckedRow := [entry1362, entry1363, entry1364, entry1365, entry1366, entry1367, entry1368, entry1369]
def rows42 : List Row := [row1362, row1363, row1364, row1365, row1366, row1367, row1368, row1369]
theorem indices42 : rows42.map Row.index = [1362, 1363, 1364, 1365, 1366, 1367, 1368, 1369] := by rfl
theorem bound42 : entries42.map CheckedRow.row = rows42 := by rfl
theorem choices_and_42 : choices rows42 167837696#32 (-1) = [] := by rfl
theorem choices_orr_42 : choices rows42 704708608#32 (-1) = [] := by rfl
theorem choices_eor_42 : choices rows42 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_42 : choices rows42 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
