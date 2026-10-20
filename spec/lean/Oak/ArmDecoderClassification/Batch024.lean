import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1218 : List String := ["function clause decode64 ((", "0b", "00001000110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1218", ") = {\n    SEE = ", "1218", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_ordered_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1218 : Clause := ⟨[.fixed "00001000110", .any 5, .fixed "0", .any 15], 1218, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_ordered_decode"⟩
theorem checked1218 : check raw1218 clause1218 = true := by rfl
def row1218 : Row := ⟨1218, 4292902912, 146800640⟩
theorem derived1218 : clause1218.row = row1218 := by rfl
def entry1218 : CheckedRow := ⟨raw1218, clause1218, row1218, checked1218, derived1218⟩

def raw1219 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1219", ") = {\n    SEE = ", "1219", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Op3", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode", "(", "Rd", ", ", "Rn", ", ", "Op3", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1219 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110010", .any 5, .fixed "000001", .any 10], 1219, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Op3", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode"⟩
theorem checked1219 : check raw1219 clause1219 = true := by rfl
def row1219 : Row := ⟨1219, 3219192832, 775947264⟩
theorem derived1219 : clause1219.row = row1219 := by rfl
def entry1219 : CheckedRow := ⟨raw1219, clause1219, row1219, checked1219, derived1219⟩

def raw1220 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "101001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1220", ") = {\n    SEE = ", "1220", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_leftlong_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1220 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "101001", .any 10], 1220, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_leftlong_decode"⟩
theorem checked1220 : check raw1220 clause1220 = true := by rfl
def row1220 : Row := ⟨1220, 3212901376, 788571136⟩
theorem derived1220 : clause1220.row = row1220 := by rfl
def entry1220 : CheckedRow := ⟨raw1220, clause1220, row1220, checked1220, derived1220⟩

def raw1221 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000011110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1221", ") = {\n    SEE = ", "1221", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_sat_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1221 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "100000011110", .any 10], 1221, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_diffneg_sat_sisd_decode"⟩
theorem checked1221 : check raw1221 clause1221 = true := by rfl
def row1221 : Row := ⟨1221, 4282383360, 1579186176⟩
theorem derived1221 : clause1221.row = row1221 := by rfl
def entry1221 : CheckedRow := ⟨raw1221, clause1221, row1221, checked1221, derived1221⟩

def raw1222 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111011111000110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1222", ") = {\n    SEE = ", "1222", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_fp16_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1222 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111011111000110110", .any 10], 1222, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_fp16_bulk_simd_decode"⟩
theorem checked1222 : check raw1222 clause1222 = true := by rfl
def row1222 : Row := ⟨1222, 3221224448, 788060160⟩
theorem derived1222 : clause1222.row = row1222 := by rfl
def entry1222 : CheckedRow := ⟨raw1222, clause1222, row1222, checked1222, derived1222⟩

def raw1223 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111011111000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1223", ") = {\n    SEE = ", "1223", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_fp16_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1223 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111011111000110010", .any 10], 1223, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_fp16_bulk_simd_decode"⟩
theorem checked1223 : check raw1223 clause1223 = true := by rfl
def row1223 : Row := ⟨1223, 3221224448, 788056064⟩
theorem derived1223 : clause1223.row = row1223 := by rfl
def entry1223 : CheckedRow := ⟨raw1223, clause1223, row1223, checked1223, derived1223⟩

def raw1224 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "10110110", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1224", ") = {\n    SEE = ", "1224", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_simdfp_preidx_memory_pair_simdfp_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1224 : Clause := ⟨[.any 2, .fixed "10110110", .any 22], 1224, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_simdfp_preidx_memory_pair_simdfp_postidx__decode"⟩
theorem checked1224 : check raw1224 clause1224 = true := by rfl
def row1224 : Row := ⟨1224, 1069547520, 763363328⟩
theorem derived1224 : clause1224.row = row1224 := by rfl
def entry1224 : CheckedRow := ⟨raw1224, clause1224, row1224, checked1224, derived1224⟩

def raw1225 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1225", ") = {\n    SEE = ", "1225", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp_extended_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1225 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "1", .any 5, .fixed "110111", .any 10], 1225, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp_extended_simd_decode"⟩
theorem checked1225 : check raw1225 clause1225 = true := by rfl
def row1225 : Row := ⟨1225, 3214998528, 237034496⟩
theorem derived1225 : clause1225.row = row1225 := by rfl
def entry1225 : CheckedRow := ⟨raw1225, clause1225, row1225, checked1225, derived1225⟩

def entries24 : List CheckedRow := [entry1218, entry1219, entry1220, entry1221, entry1222, entry1223, entry1224, entry1225]
def rows24 : List Row := [row1218, row1219, row1220, row1221, row1222, row1223, row1224, row1225]
theorem indices24 : rows24.map Row.index = [1218, 1219, 1220, 1221, 1222, 1223, 1224, 1225] := by rfl
theorem bound24 : entries24.map CheckedRow.row = rows24 := by rfl
theorem choices_and_24 : choices rows24 167837696#32 (-1) = [] := by rfl
theorem choices_orr_24 : choices rows24 704708608#32 (-1) = [] := by rfl
theorem choices_eor_24 : choices rows24 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_24 : choices rows24 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
