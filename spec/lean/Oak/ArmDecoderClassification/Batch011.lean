import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1114 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1114", ") = {\n    SEE = ", "1114", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1114 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000000", .any 9, .fixed "00", .any 10], 1114, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1114 : check raw1114 clause1114 = true := by rfl
def row1114 : Row := ⟨1114, 3219131392, 3087007744⟩
theorem derived1114 : clause1114.row = row1114 := by rfl
def entry1114 : CheckedRow := ⟨raw1114, clause1114, row1114, checked1114, derived1114⟩

def raw1115 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110000101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1115", ") = {\n    SEE = ", "1115", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "16", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_intmax_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1115 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "110000101010", .any 10], 1115, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 16, 16, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_intmax_decode"⟩
theorem checked1115 : check raw1115 clause1115 = true := by rfl
def row1115 : Row := ⟨1115, 3208641536, 238069760⟩
theorem derived1115 : clause1115.row = row1115 := by rfl
def entry1115 : CheckedRow := ⟨raw1115, clause1115, row1115, checked1115, derived1115⟩

def raw1116 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1116", ") = {\n    SEE = ", "1116", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1116 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "0", .any 5, .fixed "100011", .any 10], 1116, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_int_doubling_accum_simd_decode"⟩
theorem checked1116 : check raw1116 clause1116 = true := by rfl
def row1116 : Row := ⟨1116, 3206609920, 771787776⟩
theorem derived1116 : clause1116.row = row1116 := by rfl
def entry1116 : CheckedRow := ⟨raw1116, clause1116, row1116, checked1116, derived1116⟩

def raw1117 : List String := ["function clause decode64 ((", "0b", "01011110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1117", ") = {\n    SEE = ", "1117", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "E", ", ", "U", ")\n}\n"]
def clause1117 : Clause := ⟨[.fixed "01011110010", .any 5, .fixed "001001", .any 10], 1117, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode"⟩
theorem checked1117 : check raw1117 clause1117 = true := by rfl
def row1117 : Row := ⟨1117, 4292934656, 1581261824⟩
theorem derived1117 : clause1117.row = row1117 := by rfl
def entry1117 : CheckedRow := ⟨raw1117, clause1117, row1117, checked1117, derived1117⟩

def raw1118 : List String := ["function clause decode64 ((", "0b", "01011110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1118", ") = {\n    SEE = ", "1118", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha3op_sha1hash_majority_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ")\n}\n"]
def clause1118 : Clause := ⟨[.fixed "01011110000", .any 5, .fixed "001000", .any 10], 1118, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 14, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha3op_sha1hash_majority_decode"⟩
theorem checked1118 : check raw1118 clause1118 = true := by rfl
def row1118 : Row := ⟨1118, 4292934656, 1577066496⟩
theorem derived1118 : clause1118.row = row1118 := by rfl
def entry1118 : CheckedRow := ⟨raw1118, clause1118, row1118, checked1118, derived1118⟩

def raw1119 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1119", ") = {\n    SEE = ", "1119", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_addsub_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1119 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "001010", .any 10], 1119, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_addsub_decode"⟩
theorem checked1119 : check raw1119 clause1119 = true := by rfl
def row1119 : Row := ⟨1119, 4280351744, 505423872⟩
theorem derived1119 : clause1119.row = row1119 := by rfl
def entry1119 : CheckedRow := ⟨raw1119, clause1119, row1119, checked1119, derived1119⟩

def raw1120 : List String := ["function clause decode64 ((", "0b", "01011110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1120", ") = {\n    SEE = ", "1120", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "P", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha3op_sha256hash_decode", "(", "Rd", ", ", "Rn", ", ", "P", ", ", "Rm", ", ", "size", ")\n}\n"]
def clause1120 : Clause := ⟨[.fixed "01011110000", .any 5, .fixed "010000", .any 10], 1120, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"P", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha3op_sha256hash_decode"⟩
theorem checked1120 : check raw1120 clause1120 = true := by rfl
def row1120 : Row := ⟨1120, 4292934656, 1577074688⟩
theorem derived1120 : clause1120.row = row1120 := by rfl
def entry1120 : CheckedRow := ⟨raw1120, clause1120, row1120, checked1120, derived1120⟩

def raw1121 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1121", ") = {\n    SEE = ", "1121", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1121 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "1", .any 5, .fixed "110101", .any 10], 1121, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_sub_fp_simd_decode"⟩
theorem checked1121 : check raw1121 clause1121 = true := by rfl
def row1121 : Row := ⟨1121, 3214998528, 245421056⟩
theorem derived1121 : clause1121.row = row1121 := by rfl
def entry1121 : CheckedRow := ⟨raw1121, clause1121, row1121, checked1121, derived1121⟩

def entries11 : List CheckedRow := [entry1114, entry1115, entry1116, entry1117, entry1118, entry1119, entry1120, entry1121]
def rows11 : List Row := [row1114, row1115, row1116, row1117, row1118, row1119, row1120, row1121]
theorem indices11 : rows11.map Row.index = [1114, 1115, 1116, 1117, 1118, 1119, 1120, 1121] := by rfl
theorem bound11 : entries11.map CheckedRow.row = rows11 := by rfl
theorem choices_and_11 : choices rows11 167837696#32 (-1) = [] := by rfl
theorem choices_orr_11 : choices rows11 704708608#32 (-1) = [] := by rfl
theorem choices_eor_11 : choices rows11 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_11 : choices rows11 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
