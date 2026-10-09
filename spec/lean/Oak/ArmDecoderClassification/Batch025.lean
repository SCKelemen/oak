import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1226 : List String := ["function clause decode64 ((", "0b", "001110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1226", ") = {\n    SEE = ", "1226", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1226 : Clause := ⟨[.fixed "001110000", .any 1, .fixed "1", .any 5, .fixed "010000", .any 5, .fixed "11111"], 1226, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1226 : check raw1226 clause1226 = true := by rfl
def row1226 : Row := ⟨1226, 4288740383, 941637663⟩
theorem derived1226 : clause1226.row = row1226 := by rfl
def entry1226 : CheckedRow := ⟨raw1226, clause1226, row1226, checked1226, derived1226⟩

def raw1227 : List String := ["function clause decode64 ((", "0b", "11010101000000110010000010111111", " as op_code) if SEE < ", "1227", ") = {\n    SEE = ", "1227", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_hints_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1227 : Clause := ⟨[.fixed "11010101000000110010000010111111"], 1227, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_hints_decode"⟩
theorem checked1227 : check raw1227 clause1227 = true := by rfl
def row1227 : Row := ⟨1227, 4294967295, 3573751999⟩
theorem derived1227 : clause1227.row = row1227 := by rfl
def entry1227 : CheckedRow := ⟨raw1227, clause1227, row1227, checked1227, derived1227⟩

def raw1228 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000001110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1228", ") = {\n    SEE = ", "1228", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_add_saturating_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1228 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100000001110", .any 10], 1228, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_add_saturating_simd_decode"⟩
theorem checked1228 : check raw1228 clause1228 = true := by rfl
def row1228 : Row := ⟨1228, 3208641536, 773863424⟩
theorem derived1228 : clause1228.row = row1228 := by rfl
def entry1228 : CheckedRow := ⟨raw1228, clause1228, row1228, checked1228, derived1228⟩

def raw1229 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "101101011000000000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1229", ") = {\n    SEE = ", "1229", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_cnt_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1229 : Clause := ⟨[.any 1, .fixed "101101011000000000101", .any 10], 1229, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 10, 10, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_cnt_decode"⟩
theorem checked1229 : check raw1229 clause1229 = true := by rfl
def row1229 : Row := ⟨1229, 2147482624, 1522537472⟩
theorem derived1229 : clause1229.row = row1229 := by rfl
def entry1229 : CheckedRow := ⟨raw1229, clause1229, row1229, checked1229, derived1229⟩

def raw1230 : List String := ["function clause decode64 ((", "0b", "01011110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1230", ") = {\n    SEE = ", "1230", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "P", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha3op_sha256hash_decode", "(", "Rd", ", ", "Rn", ", ", "P", ", ", "Rm", ", ", "size", ")\n}\n"]
def clause1230 : Clause := ⟨[.fixed "01011110000", .any 5, .fixed "010100", .any 10], 1230, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"P", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha3op_sha256hash_decode"⟩
theorem checked1230 : check raw1230 clause1230 = true := by rfl
def row1230 : Row := ⟨1230, 4292934656, 1577078784⟩
theorem derived1230 : clause1230.row = row1230 := by rfl
def entry1230 : CheckedRow := ⟨raw1230, clause1230, row1230, checked1230, derived1230⟩

def raw1231 : List String := ["function clause decode64 ((", "0b", "001110001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1231", ") = {\n    SEE = ", "1231", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1231 : Clause := ⟨[.fixed "001110001", .any 1, .fixed "0", .any 9, .fixed "00", .any 10], 1231, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1231 : check raw1231 clause1231 = true := by rfl
def row1231 : Row := ⟨1231, 4288678912, 947912704⟩
theorem derived1231 : clause1231.row = row1231 := by rfl
def entry1231 : CheckedRow := ⟨raw1231, clause1231, row1231, checked1231, derived1231⟩

def raw1232 : List String := ["function clause decode64 ((", "0b", "10011011001", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1232", ") = {\n    SEE = ", "1232", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "op54", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_mul_widening_3264_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "U", ", ", "op54", ", ", "sf", ")\n}\n"]
def clause1232 : Clause := ⟨[.fixed "10011011001", .any 5, .fixed "0", .any 15], 1232, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"U", 1, 23, 23, true⟩, ⟨"op54", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_mul_widening_3264_decode"⟩
theorem checked1232 : check raw1232 clause1232 = true := by rfl
def row1232 : Row := ⟨1232, 4292902912, 2602565632⟩
theorem derived1232 : clause1232.row = row1232 := by rfl
def entry1232 : CheckedRow := ⟨raw1232, clause1232, row1232, checked1232, derived1232⟩

def raw1233 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0110111", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1233", ") = {\n    SEE = ", "1233", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm14", " : bits(", "14", ") = ", "op_code[", "18", " .. ", "5", "]", ";\n", "    ", "b40", " : bits(", "5", ") = ", "op_code[", "23", " .. ", "19", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "b5", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "branch_conditional_test_decode", "(", "Rt", ", ", "imm14", ", ", "b40", ", ", "op", ", ", "b5", ")\n}\n"]
def clause1233 : Clause := ⟨[.any 1, .fixed "0110111", .any 24], 1233, [⟨"Rt", 5, 4, 0, false⟩, ⟨"imm14", 14, 18, 5, false⟩, ⟨"b40", 5, 23, 19, false⟩, ⟨"op", 1, 24, 24, true⟩, ⟨"b5", 1, 31, 31, true⟩], "branch_conditional_test_decode"⟩
theorem checked1233 : check raw1233 clause1233 = true := by rfl
def row1233 : Row := ⟨1233, 2130706432, 922746880⟩
theorem derived1233 : clause1233.row = row1233 := by rfl
def entry1233 : CheckedRow := ⟨raw1233, clause1233, row1233, checked1233, derived1233⟩

def entries25 : List CheckedRow := [entry1226, entry1227, entry1228, entry1229, entry1230, entry1231, entry1232, entry1233]
def rows25 : List Row := [row1226, row1227, row1228, row1229, row1230, row1231, row1232, row1233]
theorem indices25 : rows25.map Row.index = [1226, 1227, 1228, 1229, 1230, 1231, 1232, 1233] := by rfl
theorem bound25 : entries25.map CheckedRow.row = rows25 := by rfl
theorem choices_and_25 : choices rows25 167837696#32 (-1) = [] := by rfl
theorem choices_orr_25 : choices rows25 704708608#32 (-1) = [] := by rfl
theorem choices_eor_25 : choices rows25 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_25 : choices rows25 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
