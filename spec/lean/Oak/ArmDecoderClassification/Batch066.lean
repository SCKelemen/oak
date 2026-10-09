import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1554 : List String := ["function clause decode64 ((", "0b", "00111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1554", ") = {\n    SEE = ", "1554", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1554 : Clause := ⟨[.fixed "00111000", .any 2, .fixed "1", .any 5, .fixed "000100", .any 10], 1554, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1554 : check raw1554 clause1554 = true := by rfl
def row1554 : Row := ⟨1554, 4280351744, 941625344⟩
theorem derived1554 : clause1554.row = row1554 := by rfl
def entry1554 : CheckedRow := ⟨raw1554, clause1554, row1554, checked1554, derived1554⟩

def raw1555 : List String := ["function clause decode64 ((", "0b", "01011110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1555", ") = {\n    SEE = ", "1555", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha3op_sha1hash_choose_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ")\n}\n"]
def clause1555 : Clause := ⟨[.fixed "01011110000", .any 5, .fixed "000000", .any 10], 1555, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 14, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha3op_sha1hash_choose_decode"⟩
theorem checked1555 : check raw1555 clause1555 = true := by rfl
def row1555 : Row := ⟨1555, 4292934656, 1577058304⟩
theorem derived1555 : clause1555.row = row1555 := by rfl
def entry1555 : CheckedRow := ⟨raw1555, clause1555, row1555, checked1555, derived1555⟩

def raw1556 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111011111001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1556", ") = {\n    SEE = ", "1556", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_special_sqrtest_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1556 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111011111001110110", .any 10], 1556, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_special_sqrtest_fp16_simd_decode"⟩
theorem checked1556 : check raw1556 clause1556 = true := by rfl
def row1556 : Row := ⟨1556, 3221224448, 788125696⟩
theorem derived1556 : clause1556.row = row1556 := by rfl
def entry1556 : CheckedRow := ⟨raw1556, clause1556, row1556, checked1556, derived1556⟩

def raw1557 : List String := ["function clause decode64 ((", "0b", "11010100000", " @ ", "_ : bits(", "16", ")", " @ ", "0b", "00010", " as op_code) if SEE < ", "1557", ") = {\n    SEE = ", "1557", ";\n", "    ", "LL", " : bits(", "2", ") = ", "op_code[", "1", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "4", " .. ", "2", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "23", " .. ", "21", "]", ";\n", "    ", "system_exceptions_runtime_hvc_decode", "(", "LL", ", ", "op2", ", ", "imm16", ", ", "opc", ")\n}\n"]
def clause1557 : Clause := ⟨[.fixed "11010100000", .any 16, .fixed "00010"], 1557, [⟨"LL", 2, 1, 0, false⟩, ⟨"op2", 3, 4, 2, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"opc", 3, 23, 21, false⟩], "system_exceptions_runtime_hvc_decode"⟩
theorem checked1557 : check raw1557 clause1557 = true := by rfl
def row1557 : Row := ⟨1557, 4292870175, 3556769794⟩
theorem derived1557 : clause1557.row = row1557 := by rfl
def entry1557 : CheckedRow := ⟨raw1557, clause1557, row1557, checked1557, derived1557⟩

def raw1558 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1558", ") = {\n    SEE = ", "1558", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp_fused_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "op", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1558 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "1", .any 5, .fixed "110011", .any 10], 1558, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"op", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp_fused_decode"⟩
theorem checked1558 : check raw1558 clause1558 = true := by rfl
def row1558 : Row := ⟨1558, 3214998528, 237030400⟩
theorem derived1558 : clause1558.row = row1558 := by rfl
def entry1558 : CheckedRow := ⟨raw1558, clause1558, row1558, checked1558, derived1558⟩

def raw1559 : List String := ["function clause decode64 ((", "0b", "00011001000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1559", ") = {\n    SEE = ", "1559", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettag_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1559 : Clause := ⟨[.fixed "00011001000", .any 9, .fixed "10", .any 10], 1559, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettag_decode"⟩
theorem checked1559 : check raw1559 clause1559 = true := by rfl
def row1559 : Row := ⟨1559, 4292873216, 419432448⟩
theorem derived1559 : clause1559.row = row1559 := by rfl
def entry1559 : CheckedRow := ⟨raw1559, clause1559, row1559, checked1559, derived1559⟩

def raw1560 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001010010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1560", ") = {\n    SEE = ", "1560", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_extract_sat_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1560 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100001010010", .any 10], 1560, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_extract_sat_simd_decode"⟩
theorem checked1560 : check raw1560 clause1560 = true := by rfl
def row1560 : Row := ⟨1560, 3208641536, 237062144⟩
theorem derived1560 : clause1560.row = row1560 := by rfl
def entry1560 : CheckedRow := ⟨raw1560, clause1560, row1560, checked1560, derived1560⟩

def raw1561 : List String := ["function clause decode64 ((", "0b", "10011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1561", ") = {\n    SEE = ", "1561", ";\n", "    ", "Xd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Xm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "integer_arithmetic_pointer_mcsubtracttaggedaddress_decode", "(", "Xd", ", ", "Xn", ", ", "Xm", ")\n}\n"]
def clause1561 : Clause := ⟨[.fixed "10011010110", .any 5, .fixed "000000", .any 10], 1561, [⟨"Xd", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"Xm", 5, 20, 16, false⟩], "integer_arithmetic_pointer_mcsubtracttaggedaddress_decode"⟩
theorem checked1561 : check raw1561 clause1561 = true := by rfl
def row1561 : Row := ⟨1561, 4292934656, 2596274176⟩
theorem derived1561 : clause1561.row = row1561 := by rfl
def entry1561 : CheckedRow := ⟨raw1561, clause1561, row1561, checked1561, derived1561⟩

def entries66 : List CheckedRow := [entry1554, entry1555, entry1556, entry1557, entry1558, entry1559, entry1560, entry1561]
def rows66 : List Row := [row1554, row1555, row1556, row1557, row1558, row1559, row1560, row1561]
theorem indices66 : rows66.map Row.index = [1554, 1555, 1556, 1557, 1558, 1559, 1560, 1561] := by rfl
theorem bound66 : entries66.map CheckedRow.row = rows66 := by rfl
theorem choices_and_66 : choices rows66 167837696#32 (-1) = [] := by rfl
theorem choices_orr_66 : choices rows66 704708608#32 (-1) = [] := by rfl
theorem choices_eor_66 : choices rows66 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_66 : choices rows66 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
