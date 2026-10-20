import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1346 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1346", ") = {\n    SEE = ", "1346", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper_decode", "(", "Rd", ", ", "Rn", ", ", "Rm", ", ", "sz", ", ", "S", ", ", "Q", ")\n}\n"]
def clause1346 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "110011", .any 10], 1346, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"S", 1, 23, 23, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp_mul_norounding_upper_decode"⟩
theorem checked1346 : check raw1346 clause1346 = true := by rfl
def row1346 : Row := ⟨1346, 3206609920, 773901312⟩
theorem derived1346 : clause1346.row = row1346 := by rfl
def entry1346 : CheckedRow := ⟨raw1346, clause1346, row1346, checked1346, derived1346⟩

def raw1347 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1347", ") = {\n    SEE = ", "1347", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode2", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_carry_decode", "(", "Rd", ", ", "Rn", ", ", "opcode2", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1347 : Clause := ⟨[.any 1, .fixed "0011010000", .any 5, .fixed "000000", .any 10], 1347, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode2", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_carry_decode"⟩
theorem checked1347 : check raw1347 clause1347 = true := by rfl
def row1347 : Row := ⟨1347, 2145451008, 436207616⟩
theorem derived1347 : clause1347.row = row1347 := by rfl
def entry1347 : CheckedRow := ⟨raw1347, clause1347, row1347, checked1347, derived1347⟩

def raw1348 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "00100111", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1348", ") = {\n    SEE = ", "1348", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imms", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "op21", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_insext_extract_immediate_decode", "(", "Rd", ", ", "Rn", ", ", "imms", ", ", "Rm", ", ", "o0", ", ", "N", ", ", "op21", ", ", "sf", ")\n}\n"]
def clause1348 : Clause := ⟨[.any 1, .fixed "00100111", .any 1, .fixed "0", .any 21], 1348, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imms", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"o0", 1, 21, 21, true⟩, ⟨"N", 1, 22, 22, true⟩, ⟨"op21", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_insext_extract_immediate_decode"⟩
theorem checked1348 : check raw1348 clause1348 = true := by rfl
def row1348 : Row := ⟨1348, 2141192192, 327155712⟩
theorem derived1348 : clause1348.row = row1348 := by rfl
def entry1348 : CheckedRow := ⟨raw1348, clause1348, row1348, checked1348, derived1348⟩

def raw1349 : List String := ["function clause decode64 ((", "0b", "0011100100", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1349", ") = {\n    SEE = ", "1349", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1349 : Clause := ⟨[.fixed "0011100100", .any 22], 1349, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1349 : check raw1349 clause1349 = true := by rfl
def row1349 : Row := ⟨1349, 4290772992, 956301312⟩
theorem derived1349 : clause1349.row = row1349 := by rfl
def entry1349 : CheckedRow := ⟨raw1349, clause1349, row1349, checked1349, derived1349⟩

def raw1350 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1350", ") = {\n    SEE = ", "1350", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1350 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "010011", .any 10], 1350, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_shift_sisd_decode"⟩
theorem checked1350 : check raw1350 clause1350 = true := by rfl
def row1350 : Row := ⟨1350, 4280351744, 1579174912⟩
theorem derived1350 : clause1350.row = row1350 := by rfl
def entry1350 : CheckedRow := ⟨raw1350, clause1350, row1350, checked1350, derived1350⟩

def raw1351 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "010100011", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1351", ") = {\n    SEE = ", "1351", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_general_postidx_memory_pair_general_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1351 : Clause := ⟨[.any 1, .fixed "010100011", .any 22], 1351, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_general_postidx_memory_pair_general_postidx__decode"⟩
theorem checked1351 : check raw1351 clause1351 = true := by rfl
def row1351 : Row := ⟨1351, 2143289344, 683671552⟩
theorem derived1351 : clause1351.row = row1351 := by rfl
def entry1351 : CheckedRow := ⟨raw1351, clause1351, row1351, checked1351, derived1351⟩

def raw1352 : List String := ["function clause decode64 ((", "0b", "01111000001", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1352", ") = {\n    SEE = ", "1352", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_register_memory_single_general_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1352 : Clause := ⟨[.fixed "01111000001", .any 9, .fixed "10", .any 10], 1352, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_register_memory_single_general_register__decode"⟩
theorem checked1352 : check raw1352 clause1352 = true := by rfl
def row1352 : Row := ⟨1352, 4292873216, 2015365120⟩
theorem derived1352 : clause1352.row = row1352 := by rfl
def entry1352 : CheckedRow := ⟨raw1352, clause1352, row1352, checked1352, derived1352⟩

def raw1353 : List String := ["function clause decode64 ((", "0b", "11010100101", " @ ", "_ : bits(", "16", ")", " @ ", "0b", "00001", " as op_code) if SEE < ", "1353", ") = {\n    SEE = ", "1353", ";\n", "    ", "LL", " : bits(", "2", ") = ", "op_code[", "1", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "4", " .. ", "2", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "23", " .. ", "21", "]", ";\n", "    ", "system_exceptions_debug_exception_decode", "(", "LL", ", ", "op2", ", ", "imm16", ", ", "opc", ")\n}\n"]
def clause1353 : Clause := ⟨[.fixed "11010100101", .any 16, .fixed "00001"], 1353, [⟨"LL", 2, 1, 0, false⟩, ⟨"op2", 3, 4, 2, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"opc", 3, 23, 21, false⟩], "system_exceptions_debug_exception_decode"⟩
theorem checked1353 : check raw1353 clause1353 = true := by rfl
def row1353 : Row := ⟨1353, 4292870175, 3567255553⟩
theorem derived1353 : clause1353.row = row1353 := by rfl
def entry1353 : CheckedRow := ⟨raw1353, clause1353, row1353, checked1353, derived1353⟩

def entries40 : List CheckedRow := [entry1346, entry1347, entry1348, entry1349, entry1350, entry1351, entry1352, entry1353]
def rows40 : List Row := [row1346, row1347, row1348, row1349, row1350, row1351, row1352, row1353]
theorem indices40 : rows40.map Row.index = [1346, 1347, 1348, 1349, 1350, 1351, 1352, 1353] := by rfl
theorem bound40 : entries40.map CheckedRow.row = rows40 := by rfl
theorem choices_and_40 : choices rows40 167837696#32 (-1) = [] := by rfl
theorem choices_orr_40 : choices rows40 704708608#32 (-1) = [] := by rfl
theorem choices_eor_40 : choices rows40 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_40 : choices rows40 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
