import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1242 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111001111001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1242", ") = {\n    SEE = ", "1242", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1242 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111001111001110010", .any 10], 1242, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode"⟩
theorem checked1242 : check raw1242 clause1242 = true := by rfl
def row1242 : Row := ⟨1242, 3221224448, 779732992⟩
theorem derived1242 : clause1242.row = row1242 := by rfl
def entry1242 : CheckedRow := ⟨raw1242, clause1242, row1242, checked1242, derived1242⟩

def raw1243 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1243", ") = {\n    SEE = ", "1243", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_bitwise_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1243 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "100011", .any 10], 1243, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_bitwise_simd_decode"⟩
theorem checked1243 : check raw1243 clause1243 = true := by rfl
def row1243 : Row := ⟨1243, 3206609920, 773884928⟩
theorem derived1243 : clause1243.row = row1243 := by rfl
def entry1243 : CheckedRow := ⟨raw1243, clause1243, row1243, checked1243, derived1243⟩

def raw1244 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0001010", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1244", ") = {\n    SEE = ", "1244", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "N", ", ", "shift", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1244 : Clause := ⟨[.any 1, .fixed "0001010", .any 2, .fixed "1", .any 21], 1244, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"N", 1, 21, 21, true⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_shiftedreg_decode"⟩
theorem checked1244 : check raw1244 clause1244 = true := by rfl
def row1244 : Row := ⟨1244, 2132803584, 169869312⟩
theorem derived1244 : clause1244.row = row1244 := by rfl
def entry1244 : CheckedRow := ⟨raw1244, clause1244, row1244, checked1244, derived1244⟩

def raw1245 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1245", ") = {\n    SEE = ", "1245", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_permute_zip_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "size", ", ", "Q", ")\n}\n"]
def clause1245 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "0", .any 5, .fixed "011110", .any 10], 1245, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_permute_zip_decode"⟩
theorem checked1245 : check raw1245 clause1245 = true := by rfl
def row1245 : Row := ⟨1245, 3206609920, 234911744⟩
theorem derived1245 : clause1245.row = row1245 := by rfl
def entry1245 : CheckedRow := ⟨raw1245, clause1245, row1245, checked1245, derived1245⟩

def raw1246 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0100", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1246", ") = {\n    SEE = ", "1246", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "sz", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "C", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode2_5_3_", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_crc_decode", "(", "Rd", ", ", "Rn", ", ", "sz", ", ", "C", ", ", "opcode2_5_3_", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1246 : Clause := ⟨[.any 1, .fixed "0011010110", .any 5, .fixed "0100", .any 12], 1246, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"sz", 2, 11, 10, false⟩, ⟨"C", 1, 12, 12, true⟩, ⟨"opcode2_5_3_", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_crc_decode"⟩
theorem checked1246 : check raw1246 clause1246 = true := by rfl
def row1246 : Row := ⟨1246, 2145447936, 448806912⟩
theorem derived1246 : clause1246.row = row1246 := by rfl
def entry1246 : CheckedRow := ⟨raw1246, clause1246, row1246, checked1246, derived1246⟩

def raw1247 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "111111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1247", ") = {\n    SEE = ", "1247", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_conv_float_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1247 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "111111", .any 10], 1247, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_conv_float_sisd_decode"⟩
theorem checked1247 : check raw1247 clause1247 = true := by rfl
def row1247 : Row := ⟨1247, 4286643200, 2130770944⟩
theorem derived1247 : clause1247.row = row1247 := by rfl
def entry1247 : CheckedRow := ⟨raw1247, clause1247, row1247, checked1247, derived1247⟩

def raw1248 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1248", ") = {\n    SEE = ", "1248", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1248 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110110", .any 5, .fixed "001101", .any 10], 1248, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode"⟩
theorem checked1248 : check raw1248 clause1248 = true := by rfl
def row1248 : Row := ⟨1248, 3219192832, 784348160⟩
theorem derived1248 : clause1248.row = row1248 := by rfl
def entry1248 : CheckedRow := ⟨raw1248, clause1248, row1248, checked1248, derived1248⟩

def raw1249 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "011101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1249", ") = {\n    SEE = ", "1249", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_leftsat_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1249 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "011101", .any 10], 1249, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_leftsat_simd_decode"⟩
theorem checked1249 : check raw1249 clause1249 = true := by rfl
def row1249 : Row := ⟨1249, 3212901376, 788558848⟩
theorem derived1249 : clause1249.row = row1249 := by rfl
def entry1249 : CheckedRow := ⟨raw1249, clause1249, row1249, checked1249, derived1249⟩

def entries27 : List CheckedRow := [entry1242, entry1243, entry1244, entry1245, entry1246, entry1247, entry1248, entry1249]
def rows27 : List Row := [row1242, row1243, row1244, row1245, row1246, row1247, row1248, row1249]
theorem indices27 : rows27.map Row.index = [1242, 1243, 1244, 1245, 1246, 1247, 1248, 1249] := by rfl
theorem bound27 : entries27.map CheckedRow.row = rows27 := by rfl
theorem choices_and_27 : choices rows27 167837696#32 (-1) = [] := by rfl
theorem choices_orr_27 : choices rows27 704708608#32 (-1) = [] := by rfl
theorem choices_eor_27 : choices rows27 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_27 : choices rows27 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
