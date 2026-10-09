import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1538 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "101101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1538", ") = {\n    SEE = ", "1538", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_int_doubling_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1538 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "101101", .any 10], 1538, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_int_doubling_simd_decode"⟩
theorem checked1538 : check raw1538 clause1538 = true := by rfl
def row1538 : Row := ⟨1538, 3206609920, 773895168⟩
theorem derived1538 : clause1538.row = row1538 := by rfl
def entry1538 : CheckedRow := ⟨raw1538, clause1538, row1538, checked1538, derived1538⟩

def raw1539 : List String := ["function clause decode64 ((", "0b", "00111000010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1539", ") = {\n    SEE = ", "1539", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1539 : Clause := ⟨[.fixed "00111000010", .any 9, .fixed "00", .any 10], 1539, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1539 : check raw1539 clause1539 = true := by rfl
def row1539 : Row := ⟨1539, 4292873216, 943718400⟩
theorem derived1539 : clause1539.row = row1539 := by rfl
def entry1539 : CheckedRow := ⟨raw1539, clause1539, row1539, checked1539, derived1539⟩

def raw1540 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1540", ") = {\n    SEE = ", "1540", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "len", " : bits(", "2", ") = ", "op_code[", "14", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op2", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_table_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "len", ", ", "Rm", ", ", "op2", ", ", "Q", ")\n}\n"]
def clause1540 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110000", .any 5, .fixed "0", .any 2, .fixed "000", .any 10], 1540, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"len", 2, 14, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"op2", 2, 23, 22, false⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_table_decode"⟩
theorem checked1540 : check raw1540 clause1540 = true := by rfl
def row1540 : Row := ⟨1540, 3219168256, 234881024⟩
theorem derived1540 : clause1540.row = row1540 := by rfl
def entry1540 : CheckedRow := ⟨raw1540, clause1540, row1540, checked1540, derived1540⟩

def raw1541 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "00100101", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1541", ") = {\n    SEE = ", "1541", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "hw", " : bits(", "2", ") = ", "op_code[", "22", " .. ", "21", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_insext_insert_movewide_decode", "(", "Rd", ", ", "imm16", ", ", "hw", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1541 : Clause := ⟨[.any 1, .fixed "00100101", .any 23], 1541, [⟨"Rd", 5, 4, 0, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"hw", 2, 22, 21, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_insext_insert_movewide_decode"⟩
theorem checked1541 : check raw1541 clause1541 = true := by rfl
def row1541 : Row := ⟨1541, 2139095040, 310378496⟩
theorem derived1541 : clause1541.row = row1541 := by rfl
def entry1541 : CheckedRow := ⟨raw1541, clause1541, row1541, checked1541, derived1541⟩

def raw1542 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1542", ") = {\n    SEE = ", "1542", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_addsub_wide_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1542 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "001100", .any 10], 1542, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_addsub_wide_decode"⟩
theorem checked1542 : check raw1542 clause1542 = true := by rfl
def row1542 : Row := ⟨1542, 3206609920, 236990464⟩
theorem derived1542 : clause1542.row = row1542 := by rfl
def entry1542 : CheckedRow := ⟨raw1542, clause1542, row1542, checked1542, derived1542⟩

def raw1543 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1543", ") = {\n    SEE = ", "1543", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Op3", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode", "(", "Rd", ", ", "Rn", ", ", "Op3", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1543 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110110", .any 5, .fixed "000001", .any 10], 1543, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Op3", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode"⟩
theorem checked1543 : check raw1543 clause1543 = true := by rfl
def row1543 : Row := ⟨1543, 3219192832, 247464960⟩
theorem derived1543 : clause1543.row = row1543 := by rfl
def entry1543 : CheckedRow := ⟨raw1543, clause1543, row1543, checked1543, derived1543⟩

def raw1544 : List String := ["function clause decode64 ((", "0b", "11010100101", " @ ", "_ : bits(", "16", ")", " @ ", "0b", "00010", " as op_code) if SEE < ", "1544", ") = {\n    SEE = ", "1544", ";\n", "    ", "LL", " : bits(", "2", ") = ", "op_code[", "1", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "4", " .. ", "2", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "23", " .. ", "21", "]", ";\n", "    ", "system_exceptions_debug_exception_decode", "(", "LL", ", ", "op2", ", ", "imm16", ", ", "opc", ")\n}\n"]
def clause1544 : Clause := ⟨[.fixed "11010100101", .any 16, .fixed "00010"], 1544, [⟨"LL", 2, 1, 0, false⟩, ⟨"op2", 3, 4, 2, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"opc", 3, 23, 21, false⟩], "system_exceptions_debug_exception_decode"⟩
theorem checked1544 : check raw1544 clause1544 = true := by rfl
def row1544 : Row := ⟨1544, 4292870175, 3567255554⟩
theorem derived1544 : clause1544.row = row1544 := by rfl
def entry1544 : CheckedRow := ⟨raw1544, clause1544, row1544, checked1544, derived1544⟩

def raw1545 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "101100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1545", ") = {\n    SEE = ", "1545", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1545 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "101100", .any 10], 1545, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode"⟩
theorem checked1545 : check raw1545 clause1545 = true := by rfl
def row1545 : Row := ⟨1545, 4280351744, 1579200512⟩
theorem derived1545 : clause1545.row = row1545 := by rfl
def entry1545 : CheckedRow := ⟨raw1545, clause1545, row1545, checked1545, derived1545⟩

def entries64 : List CheckedRow := [entry1538, entry1539, entry1540, entry1541, entry1542, entry1543, entry1544, entry1545]
def rows64 : List Row := [row1538, row1539, row1540, row1541, row1542, row1543, row1544, row1545]
theorem indices64 : rows64.map Row.index = [1538, 1539, 1540, 1541, 1542, 1543, 1544, 1545] := by rfl
theorem bound64 : entries64.map CheckedRow.row = rows64 := by rfl
theorem choices_and_64 : choices rows64 167837696#32 (-1) = [] := by rfl
theorem choices_orr_64 : choices rows64 704708608#32 (-1) = [] := by rfl
theorem choices_eor_64 : choices rows64 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_64 : choices rows64 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
