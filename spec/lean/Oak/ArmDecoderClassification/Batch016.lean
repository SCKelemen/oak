import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1154 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1154", ") = {\n    SEE = ", "1154", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_rightnarrow_uniform_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1154 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "100111", .any 10], 1154, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_rightnarrow_uniform_simd_decode"⟩
theorem checked1154 : check raw1154 clause1154 = true := by rfl
def row1154 : Row := ⟨1154, 3212901376, 788569088⟩
theorem derived1154 : clause1154.row = row1154 := by rfl
def entry1154 : CheckedRow := ⟨raw1154, clause1154, row1154, checked1154, derived1154⟩

def raw1155 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1155", ") = {\n    SEE = ", "1155", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp_fused_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "op", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1155 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "1", .any 5, .fixed "110011", .any 10], 1155, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"op", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp_fused_decode"⟩
theorem checked1155 : check raw1155 clause1155 = true := by rfl
def row1155 : Row := ⟨1155, 3214998528, 245419008⟩
theorem derived1155 : clause1155.row = row1155 := by rfl
def entry1155 : CheckedRow := ⟨raw1155, clause1155, row1155, checked1155, derived1155⟩

def raw1156 : List String := ["function clause decode64 ((", "0b", "01011110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1156", ") = {\n    SEE = ", "1156", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha3op_sha256sched1_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ")\n}\n"]
def clause1156 : Clause := ⟨[.fixed "01011110000", .any 5, .fixed "011000", .any 10], 1156, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 14, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha3op_sha256sched1_decode"⟩
theorem checked1156 : check raw1156 clause1156 = true := by rfl
def row1156 : Row := ⟨1156, 4292934656, 1577082880⟩
theorem derived1156 : clause1156.row = row1156 := by rfl
def entry1156 : CheckedRow := ⟨raw1156, clause1156, row1156, checked1156, derived1156⟩

def raw1157 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1157", ") = {\n    SEE = ", "1157", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_rsqrtsfp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1157 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110110", .any 5, .fixed "001111", .any 10], 1157, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_rsqrtsfp16_simd_decode"⟩
theorem checked1157 : check raw1157 clause1157 = true := by rfl
def row1157 : Row := ⟨1157, 3219192832, 247479296⟩
theorem derived1157 : clause1157.row = row1157 := by rfl
def entry1157 : CheckedRow := ⟨raw1157, clause1157, row1157, checked1157, derived1157⟩

def raw1158 : List String := ["function clause decode64 ((", "0b", "1101011", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0001111100001", " @ ", "_ : bits(", "11", ")", " as op_code) if SEE < ", "1158", ") = {\n    SEE = ", "1158", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "22", " .. ", "21", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "branch_unconditional_register_decode", "(", "Rm", ", ", "Rn", ", ", "M", ", ", "A", ", ", "op2", ", ", "op", ", ", "Z", ")\n}\n"]
def clause1158 : Clause := ⟨[.fixed "1101011", .any 1, .fixed "0001111100001", .any 11], 1158, [⟨"Rm", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"M", 1, 10, 10, true⟩, ⟨"A", 1, 11, 11, true⟩, ⟨"op2", 5, 20, 16, false⟩, ⟨"op", 2, 22, 21, false⟩, ⟨"Z", 1, 24, 24, true⟩], "branch_unconditional_register_decode"⟩
theorem checked1158 : check raw1158 clause1158 = true := by rfl
def row1158 : Row := ⟨1158, 4278188032, 3592357888⟩
theorem derived1158 : clause1158.row = row1158 := by rfl
def entry1158 : CheckedRow := ⟨raw1158, clause1158, row1158, checked1158, derived1158⟩

def raw1159 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0100", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1159", ") = {\n    SEE = ", "1159", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "Rm", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1159 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100100", .any 5, .fixed "0100", .any 12], 1159, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode"⟩
theorem checked1159 : check raw1159 clause1159 = true := by rfl
def row1159 : Row := ⟨1159, 3219189760, 209731584⟩
theorem derived1159 : clause1159.row = row1159 := by rfl
def entry1159 : CheckedRow := ⟨raw1159, clause1159, row1159, checked1159, derived1159⟩

def raw1160 : List String := ["function clause decode64 ((", "0b", "1101010100000", " @ ", "_ : bits(", "3", ")", " @ ", "0b", "0100", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1160", ") = {\n    SEE = ", "1160", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_register_cpsr_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1160 : Clause := ⟨[.fixed "1101010100000", .any 3, .fixed "0100", .any 7, .fixed "11111"], 1160, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_register_cpsr_decode"⟩
theorem checked1160 : check raw1160 clause1160 = true := by rfl
def row1160 : Row := ⟨1160, 4294504479, 3573563423⟩
theorem derived1160 : clause1160.row = row1160 := by rfl
def entry1160 : CheckedRow := ⟨raw1160, clause1160, row1160, checked1160, derived1160⟩

def raw1161 : List String := ["function clause decode64 ((", "0b", "011111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001011010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1161", ") = {\n    SEE = ", "1161", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_xtn_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1161 : Clause := ⟨[.fixed "011111100", .any 1, .fixed "100001011010", .any 10], 1161, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_xtn_sisd_decode"⟩
theorem checked1161 : check raw1161 clause1161 = true := by rfl
def row1161 : Row := ⟨1161, 4290771968, 2116118528⟩
theorem derived1161 : clause1161.row = row1161 := by rfl
def entry1161 : CheckedRow := ⟨raw1161, clause1161, row1161, checked1161, derived1161⟩

def entries16 : List CheckedRow := [entry1154, entry1155, entry1156, entry1157, entry1158, entry1159, entry1160, entry1161]
def rows16 : List Row := [row1154, row1155, row1156, row1157, row1158, row1159, row1160, row1161]
theorem indices16 : rows16.map Row.index = [1154, 1155, 1156, 1157, 1158, 1159, 1160, 1161] := by rfl
theorem bound16 : entries16.map CheckedRow.row = rows16 := by rfl
theorem choices_and_16 : choices rows16 167837696#32 (-1) = [] := by rfl
theorem choices_orr_16 : choices rows16 704708608#32 (-1) = [] := by rfl
theorem choices_eor_16 : choices rows16 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_16 : choices rows16 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
