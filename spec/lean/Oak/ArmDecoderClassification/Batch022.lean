import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1202 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1202", ") = {\n    SEE = ", "1202", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_special_sqrtest_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1202 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "100001110010", .any 10], 1202, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_special_sqrtest_int_decode"⟩
theorem checked1202 : check raw1202 clause1202 = true := by rfl
def row1202 : Row := ⟨1202, 3217030144, 782354432⟩
theorem derived1202 : clause1202.row = row1202 := by rfl
def entry1202 : CheckedRow := ⟨raw1202, clause1202, row1202, checked1202, derived1202⟩

def raw1203 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100000000000100", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1203", ") = {\n    SEE = ", "1203", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1203 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100000000000100", .any 12], 1203, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode"⟩
theorem checked1203 : check raw1203 clause1203 = true := by rfl
def row1203 : Row := ⟨1203, 3221221376, 201342976⟩
theorem derived1203 : clause1203.row = row1203 := by rfl
def entry1203 : CheckedRow := ⟨raw1203, clause1203, row1203, checked1203, derived1203⟩

def raw1204 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "01100100", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1204", ") = {\n    SEE = ", "1204", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imms", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "immr", " : bits(", "6", ") = ", "op_code[", "21", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_immediate_decode", "(", "Rd", ", ", "Rn", ", ", "imms", ", ", "immr", ", ", "N", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1204 : Clause := ⟨[.any 1, .fixed "01100100", .any 23], 1204, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imms", 6, 15, 10, false⟩, ⟨"immr", 6, 21, 16, false⟩, ⟨"N", 1, 22, 22, true⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_immediate_decode"⟩
theorem checked1204 : check raw1204 clause1204 = true := by rfl
def row1204 : Row := ⟨1204, 2139095040, 838860800⟩
theorem derived1204 : clause1204.row = row1204 := by rfl
def entry1204 : CheckedRow := ⟨raw1204, clause1204, row1204, checked1204, derived1204⟩

def raw1205 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000000010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1205", ") = {\n    SEE = ", "1205", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_rev_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1205 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100000000010", .any 10], 1205, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_rev_decode"⟩
theorem checked1205 : check raw1205 clause1205 = true := by rfl
def row1205 : Row := ⟨1205, 3208641536, 773851136⟩
theorem derived1205 : clause1205.row = row1205 := by rfl
def entry1205 : CheckedRow := ⟨raw1205, clause1205, row1205, checked1205, derived1205⟩

def raw1206 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1206", ") = {\n    SEE = ", "1206", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_permute_unzip_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "size", ", ", "Q", ")\n}\n"]
def clause1206 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "0", .any 5, .fixed "000110", .any 10], 1206, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_permute_unzip_decode"⟩
theorem checked1206 : check raw1206 clause1206 = true := by rfl
def row1206 : Row := ⟨1206, 3206609920, 234887168⟩
theorem derived1206 : clause1206.row = row1206 := by rfl
def entry1206 : CheckedRow := ⟨raw1206, clause1206, row1206, checked1206, derived1206⟩

def raw1207 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111011111000110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1207", ") = {\n    SEE = ", "1207", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_fp16_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1207 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111011111000110110", .any 10], 1207, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_fp16_bulk_simd_decode"⟩
theorem checked1207 : check raw1207 clause1207 = true := by rfl
def row1207 : Row := ⟨1207, 3221224448, 251189248⟩
theorem derived1207 : clause1207.row = row1207 := by rfl
def entry1207 : CheckedRow := ⟨raw1207, clause1207, row1207, checked1207, derived1207⟩

def raw1208 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "010100000", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1208", ") = {\n    SEE = ", "1208", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_general_noalloc_memory_pair_general_noalloc__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1208 : Clause := ⟨[.any 1, .fixed "010100000", .any 22], 1208, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_general_noalloc_memory_pair_general_noalloc__decode"⟩
theorem checked1208 : check raw1208 clause1208 = true := by rfl
def row1208 : Row := ⟨1208, 2143289344, 671088640⟩
theorem derived1208 : clause1208.row = row1208 := by rfl
def entry1208 : CheckedRow := ⟨raw1208, clause1208, row1208, checked1208, derived1208⟩

def raw1209 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001100110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1209", ") = {\n    SEE = ", "1209", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1209 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "100001100110", .any 10], 1209, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_round_decode"⟩
theorem checked1209 : check raw1209 clause1209 = true := by rfl
def row1209 : Row := ⟨1209, 3217030144, 237082624⟩
theorem derived1209 : clause1209.row = row1209 := by rfl
def entry1209 : CheckedRow := ⟨raw1209, clause1209, row1209, checked1209, derived1209⟩

def entries22 : List CheckedRow := [entry1202, entry1203, entry1204, entry1205, entry1206, entry1207, entry1208, entry1209]
def rows22 : List Row := [row1202, row1203, row1204, row1205, row1206, row1207, row1208, row1209]
theorem indices22 : rows22.map Row.index = [1202, 1203, 1204, 1205, 1206, 1207, 1208, 1209] := by rfl
theorem bound22 : entries22.map CheckedRow.row = rows22 := by rfl
theorem choices_and_22 : choices rows22 167837696#32 (-1) = [] := by rfl
theorem choices_orr_22 : choices rows22 704708608#32 (-1) = [] := by rfl
theorem choices_eor_22 : choices rows22 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_22 : choices rows22 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
