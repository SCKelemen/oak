import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1194 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1194", ") = {\n    SEE = ", "1194", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_recpsfp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1194 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110010", .any 5, .fixed "001111", .any 10], 1194, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_recpsfp16_simd_decode"⟩
theorem checked1194 : check raw1194 clause1194 = true := by rfl
def row1194 : Row := ⟨1194, 3219192832, 239090688⟩
theorem derived1194 : clause1194.row = row1194 := by rfl
def entry1194 : CheckedRow := ⟨raw1194, clause1194, row1194, checked1194, derived1194⟩

def raw1195 : List String := ["function clause decode64 ((", "0b", "0101111011111001111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1195", ") = {\n    SEE = ", "1195", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_special_frecpxfp16_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ")\n}\n"]
def clause1195 : Clause := ⟨[.fixed "0101111011111001111110", .any 10], 1195, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_special_frecpxfp16_decode"⟩
theorem checked1195 : check raw1195 clause1195 = true := by rfl
def row1195 : Row := ⟨1195, 4294966272, 1593440256⟩
theorem derived1195 : clause1195.row = row1195 := by rfl
def entry1195 : CheckedRow := ⟨raw1195, clause1195, row1195, checked1195, derived1195⟩

def raw1196 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000000110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1196", ") = {\n    SEE = ", "1196", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_rev_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1196 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000000110", .any 10], 1196, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_rev_decode"⟩
theorem checked1196 : check raw1196 clause1196 = true := by rfl
def row1196 : Row := ⟨1196, 3208641536, 236984320⟩
theorem derived1196 : clause1196.row = row1196 := by rfl
def entry1196 : CheckedRow := ⟨raw1196, clause1196, row1196, checked1196, derived1196⟩

def raw1197 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1197", ") = {\n    SEE = ", "1197", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp16_product_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1197 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110010", .any 5, .fixed "000111", .any 10], 1197, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp16_product_decode"⟩
theorem checked1197 : check raw1197 clause1197 = true := by rfl
def row1197 : Row := ⟨1197, 3219192832, 775953408⟩
theorem derived1197 : clause1197.row = row1197 := by rfl
def entry1197 : CheckedRow := ⟨raw1197, clause1197, row1197, checked1197, derived1197⟩

def raw1198 : List String := ["function clause decode64 ((", "0b", "011110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1198", ") = {\n    SEE = ", "1198", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1198 : Clause := ⟨[.fixed "011110000", .any 1, .fixed "1", .any 5, .fixed "000100", .any 5, .fixed "11111"], 1198, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1198 : check raw1198 clause1198 = true := by rfl
def row1198 : Row := ⟨1198, 4288740383, 2015367199⟩
theorem derived1198 : clause1198.row = row1198 := by rfl
def entry1198 : CheckedRow := ⟨raw1198, clause1198, row1198, checked1198, derived1198⟩

def raw1199 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1199", ") = {\n    SEE = ", "1199", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp16_fused_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1199 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110110", .any 5, .fixed "000011", .any 10], 1199, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp16_fused_decode"⟩
theorem checked1199 : check raw1199 clause1199 = true := by rfl
def row1199 : Row := ⟨1199, 3219192832, 247467008⟩
theorem derived1199 : clause1199.row = row1199 := by rfl
def entry1199 : CheckedRow := ⟨raw1199, clause1199, row1199, checked1199, derived1199⟩

def raw1200 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1200", ") = {\n    SEE = ", "1200", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_lessthan_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1200 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000101010", .any 10], 1200, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_int_lessthan_simd_decode"⟩
theorem checked1200 : check raw1200 clause1200 = true := by rfl
def row1200 : Row := ⟨1200, 3208641536, 237021184⟩
theorem derived1200 : clause1200.row = row1200 := by rfl
def entry1200 : CheckedRow := ⟨raw1200, clause1200, row1200, checked1200, derived1200⟩

def raw1201 : List String := ["function clause decode64 ((", "0b", "0101111000101000000010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1201", ") = {\n    SEE = ", "1201", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha2op_sha1hash_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ")\n}\n"]
def clause1201 : Clause := ⟨[.fixed "0101111000101000000010", .any 10], 1201, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha2op_sha1hash_decode"⟩
theorem checked1201 : check raw1201 clause1201 = true := by rfl
def row1201 : Row := ⟨1201, 4294966272, 1579681792⟩
theorem derived1201 : clause1201.row = row1201 := by rfl
def entry1201 : CheckedRow := ⟨raw1201, clause1201, row1201, checked1201, derived1201⟩

def entries21 : List CheckedRow := [entry1194, entry1195, entry1196, entry1197, entry1198, entry1199, entry1200, entry1201]
def rows21 : List Row := [row1194, row1195, row1196, row1197, row1198, row1199, row1200, row1201]
theorem indices21 : rows21.map Row.index = [1194, 1195, 1196, 1197, 1198, 1199, 1200, 1201] := by rfl
theorem bound21 : entries21.map CheckedRow.row = rows21 := by rfl
theorem choices_and_21 : choices rows21 167837696#32 (-1) = [] := by rfl
theorem choices_orr_21 : choices rows21 704708608#32 (-1) = [] := by rfl
theorem choices_eor_21 : choices rows21 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_21 : choices rows21 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
