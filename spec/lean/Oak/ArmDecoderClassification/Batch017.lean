import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1162 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000011110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1162", ") = {\n    SEE = ", "1162", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_sat_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1162 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "100000011110", .any 10], 1162, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_diffneg_sat_sisd_decode"⟩
theorem checked1162 : check raw1162 clause1162 = true := by rfl
def row1162 : Row := ⟨1162, 4282383360, 2116057088⟩
theorem derived1162 : clause1162.row = row1162 := by rfl
def entry1162 : CheckedRow := ⟨raw1162, clause1162, row1162, checked1162, derived1162⟩

def raw1163 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1111010000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1163", ") = {\n    SEE = ", "1163", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode2", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_carry_decode", "(", "Rd", ", ", "Rn", ", ", "opcode2", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1163 : Clause := ⟨[.any 1, .fixed "1111010000", .any 5, .fixed "000000", .any 10], 1163, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode2", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_carry_decode"⟩
theorem checked1163 : check raw1163 clause1163 = true := by rfl
def row1163 : Row := ⟨1163, 2145451008, 2046820352⟩
theorem derived1163 : clause1163.row = row1163 := by rfl
def entry1163 : CheckedRow := ⟨raw1163, clause1163, row1163, checked1163, derived1163⟩

def raw1164 : List String := ["function clause decode64 ((", "0b", "011110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1164", ") = {\n    SEE = ", "1164", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1164 : Clause := ⟨[.fixed "011110000", .any 1, .fixed "1", .any 5, .fixed "011000", .any 5, .fixed "11111"], 1164, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1164 : check raw1164 clause1164 = true := by rfl
def row1164 : Row := ⟨1164, 4288740383, 2015387679⟩
theorem derived1164 : clause1164.row = row1164 := by rfl
def entry1164 : CheckedRow := ⟨raw1164, clause1164, row1164, checked1164, derived1164⟩

def raw1165 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1165", ") = {\n    SEE = ", "1165", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_wrapping_single_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1165 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "100001", .any 10], 1165, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_wrapping_single_simd_decode"⟩
theorem checked1165 : check raw1165 clause1165 = true := by rfl
def row1165 : Row := ⟨1165, 3206609920, 237011968⟩
theorem derived1165 : clause1165.row = row1165 := by rfl
def entry1165 : CheckedRow := ⟨raw1165, clause1165, row1165, checked1165, derived1165⟩

def raw1166 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1166", ") = {\n    SEE = ", "1166", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1166 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "1", .any 5, .fixed "111001", .any 10], 1166, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_simd_decode"⟩
theorem checked1166 : check raw1166 clause1166 = true := by rfl
def row1166 : Row := ⟨1166, 3214998528, 773907456⟩
theorem derived1166 : clause1166.row = row1166 := by rfl
def entry1166 : CheckedRow := ⟨raw1166, clause1166, row1166, checked1166, derived1166⟩

def raw1167 : List String := ["function clause decode64 ((", "0b", "010111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1167", ") = {\n    SEE = ", "1167", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1167 : Clause := ⟨[.fixed "010111101", .any 1, .fixed "100000110010", .any 10], 1167, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_float_bulk_sisd_decode"⟩
theorem checked1167 : check raw1167 clause1167 = true := by rfl
def row1167 : Row := ⟨1167, 4290771968, 1587595264⟩
theorem derived1167 : clause1167.row = row1167 := by rfl
def entry1167 : CheckedRow := ⟨raw1167, clause1167, row1167, checked1167, derived1167⟩

def raw1168 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1168", ") = {\n    SEE = ", "1168", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_addsub_narrow_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1168 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "011000", .any 10], 1168, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_addsub_narrow_decode"⟩
theorem checked1168 : check raw1168 clause1168 = true := by rfl
def row1168 : Row := ⟨1168, 3206609920, 773873664⟩
theorem derived1168 : clause1168.row = row1168 := by rfl
def entry1168 : CheckedRow := ⟨raw1168, clause1168, row1168, checked1168, derived1168⟩

def raw1169 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "11100101", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1169", ") = {\n    SEE = ", "1169", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "hw", " : bits(", "2", ") = ", "op_code[", "22", " .. ", "21", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_insext_insert_movewide_decode", "(", "Rd", ", ", "imm16", ", ", "hw", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1169 : Clause := ⟨[.any 1, .fixed "11100101", .any 23], 1169, [⟨"Rd", 5, 4, 0, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"hw", 2, 22, 21, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_insext_insert_movewide_decode"⟩
theorem checked1169 : check raw1169 clause1169 = true := by rfl
def row1169 : Row := ⟨1169, 2139095040, 1920991232⟩
theorem derived1169 : clause1169.row = row1169 := by rfl
def entry1169 : CheckedRow := ⟨raw1169, clause1169, row1169, checked1169, derived1169⟩

def entries17 : List CheckedRow := [entry1162, entry1163, entry1164, entry1165, entry1166, entry1167, entry1168, entry1169]
def rows17 : List Row := [row1162, row1163, row1164, row1165, row1166, row1167, row1168, row1169]
theorem indices17 : rows17.map Row.index = [1162, 1163, 1164, 1165, 1166, 1167, 1168, 1169] := by rfl
theorem bound17 : entries17.map CheckedRow.row = rows17 := by rfl
theorem choices_and_17 : choices rows17 167837696#32 (-1) = [] := by rfl
theorem choices_orr_17 : choices rows17 704708608#32 (-1) = [] := by rfl
theorem choices_eor_17 : choices rows17 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_17 : choices rows17 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
