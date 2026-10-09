import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1450 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1450", ") = {\n    SEE = ", "1450", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1450 : Clause := ⟨[.fixed "1", .any 1, .fixed "1110000", .any 1, .fixed "1", .any 5, .fixed "011000", .any 5, .fixed "11111"], 1450, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1450 : check raw1450 clause1450 = true := by rfl
def row1450 : Row := ⟨1450, 3214998559, 3089129503⟩
theorem derived1450 : clause1450.row = row1450 := by rfl
def entry1450 : CheckedRow := ⟨raw1450, clause1450, row1450, checked1450, derived1450⟩

def raw1451 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1451", ") = {\n    SEE = ", "1451", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ")\n}\n"]
def clause1451 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "100000100010", .any 10], 1451, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_int_bulk_sisd_decode"⟩
theorem checked1451 : check raw1451 clause1451 = true := by rfl
def row1451 : Row := ⟨1451, 4282383360, 1579190272⟩
theorem derived1451 : clause1451.row = row1451 := by rfl
def entry1451 : CheckedRow := ⟨raw1451, clause1451, row1451, checked1451, derived1451⟩

def raw1452 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101100", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1452", ") = {\n    SEE = ", "1452", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1452 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101100", .any 7, .fixed "0", .any 13], 1452, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1452 : check raw1452 clause1452 = true := by rfl
def row1452 : Row := ⟨1452, 3219136512, 226492416⟩
theorem derived1452 : clause1452.row = row1452 := by rfl
def entry1452 : CheckedRow := ⟨raw1452, clause1452, row1452, checked1452, derived1452⟩

def raw1453 : List String := ["function clause decode64 ((", "0b", "0111111001111001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1453", ") = {\n    SEE = ", "1453", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ")\n}\n"]
def clause1453 : Clause := ⟨[.fixed "0111111001111001110110", .any 10], 1453, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_int_sisd_decode"⟩
theorem checked1453 : check raw1453 clause1453 = true := by rfl
def row1453 : Row := ⟨1453, 4294966272, 2121914368⟩
theorem derived1453 : clause1453.row = row1453 := by rfl
def entry1453 : CheckedRow := ⟨raw1453, clause1453, row1453, checked1453, derived1453⟩

def raw1454 : List String := ["function clause decode64 ((", "0b", "010111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1454", ") = {\n    SEE = ", "1454", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_rsqrts_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1454 : Clause := ⟨[.fixed "010111101", .any 1, .fixed "1", .any 5, .fixed "111111", .any 10], 1454, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_rsqrts_sisd_decode"⟩
theorem checked1454 : check raw1454 clause1454 = true := by rfl
def row1454 : Row := ⟨1454, 4288740352, 1587608576⟩
theorem derived1454 : clause1454.row = row1454 := by rfl
def entry1454 : CheckedRow := ⟨raw1454, clause1454, row1454, checked1454, derived1454⟩

def raw1455 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1455", ") = {\n    SEE = ", "1455", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_special_sqrtest_float_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1455 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "100001110110", .any 10], 1455, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_special_sqrtest_float_simd_decode"⟩
theorem checked1455 : check raw1455 clause1455 = true := by rfl
def row1455 : Row := ⟨1455, 3217030144, 782358528⟩
theorem derived1455 : clause1455.row = row1455 := by rfl
def entry1455 : CheckedRow := ⟨raw1455, clause1455, row1455, checked1455, derived1455⟩

def raw1456 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1011010100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1456", ") = {\n    SEE = ", "1456", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_conditional_select_decode", "(", "Rd", ", ", "Rn", ", ", "o2", ", ", "cond", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1456 : Clause := ⟨[.any 1, .fixed "1011010100", .any 9, .fixed "00", .any 10], 1456, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o2", 1, 10, 10, true⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_conditional_select_decode"⟩
theorem checked1456 : check raw1456 clause1456 = true := by rfl
def row1456 : Row := ⟨1456, 2145389568, 1518338048⟩
theorem derived1456 : clause1456.row = row1456 := by rfl
def entry1456 : CheckedRow := ⟨raw1456, clause1456, row1456, checked1456, derived1456⟩

def raw1457 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111011111000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1457", ") = {\n    SEE = ", "1457", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_fp16_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1457 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111011111000110010", .any 10], 1457, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_fp16_bulk_simd_decode"⟩
theorem checked1457 : check raw1457 clause1457 = true := by rfl
def row1457 : Row := ⟨1457, 3221224448, 251185152⟩
theorem derived1457 : clause1457.row = row1457 := by rfl
def entry1457 : CheckedRow := ⟨raw1457, clause1457, row1457, checked1457, derived1457⟩

def entries53 : List CheckedRow := [entry1450, entry1451, entry1452, entry1453, entry1454, entry1455, entry1456, entry1457]
def rows53 : List Row := [row1450, row1451, row1452, row1453, row1454, row1455, row1456, row1457]
theorem indices53 : rows53.map Row.index = [1450, 1451, 1452, 1453, 1454, 1455, 1456, 1457] := by rfl
theorem bound53 : entries53.map CheckedRow.row = rows53 := by rfl
theorem choices_and_53 : choices rows53 167837696#32 (-1) = [] := by rfl
theorem choices_orr_53 : choices rows53 704708608#32 (-1) = [] := by rfl
theorem choices_eor_53 : choices rows53 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_53 : choices rows53 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
