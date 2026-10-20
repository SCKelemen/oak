import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1482 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001000000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1482", ") = {\n    SEE = ", "1482", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1482 : Clause := ⟨[.fixed "1", .any 1, .fixed "001000000", .any 5, .fixed "1", .any 15], 1482, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1482 : check raw1482 clause1482 = true := by rfl
def row1482 : Row := ⟨1482, 3219161088, 2281734144⟩
theorem derived1482 : clause1482.row = row1482 := by rfl
def entry1482 : CheckedRow := ⟨raw1482, clause1482, row1482, checked1482, derived1482⟩

def raw1483 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1483", ") = {\n    SEE = ", "1483", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_high_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "op", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1483 : Clause := ⟨[.fixed "0", .any 1, .fixed "001111", .any 8, .fixed "1101", .any 1, .fixed "0", .any 10], 1483, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mul_high_simd_decode"⟩
theorem checked1483 : check raw1483 clause1483 = true := by rfl
def row1483 : Row := ⟨1483, 3204510720, 251711488⟩
theorem derived1483 : clause1483.row = row1483 := by rfl
def entry1483 : CheckedRow := ⟨raw1483, clause1483, row1483, checked1483, derived1483⟩

def raw1484 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1484", ") = {\n    SEE = ", "1484", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp16_extended_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1484 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110010", .any 5, .fixed "000111", .any 10], 1484, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp16_extended_simd_decode"⟩
theorem checked1484 : check raw1484 clause1484 = true := by rfl
def row1484 : Row := ⟨1484, 3219192832, 239082496⟩
theorem derived1484 : clause1484.row = row1484 := by rfl
def entry1484 : CheckedRow := ⟨raw1484, clause1484, row1484, checked1484, derived1484⟩

def raw1485 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "111000000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1485", ") = {\n    SEE = ", "1485", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1485 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "111000000000", .any 10], 1485, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1485 : check raw1485 clause1485 = true := by rfl
def row1485 : Row := ⟨1485, 2134899712, 506986496⟩
theorem derived1485 : clause1485.row = row1485 := by rfl
def entry1485 : CheckedRow := ⟨raw1485, clause1485, row1485, checked1485, derived1485⟩

def raw1486 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "10100101", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1486", ") = {\n    SEE = ", "1486", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "hw", " : bits(", "2", ") = ", "op_code[", "22", " .. ", "21", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_insext_insert_movewide_decode", "(", "Rd", ", ", "imm16", ", ", "hw", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1486 : Clause := ⟨[.any 1, .fixed "10100101", .any 23], 1486, [⟨"Rd", 5, 4, 0, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"hw", 2, 22, 21, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_insext_insert_movewide_decode"⟩
theorem checked1486 : check raw1486 clause1486 = true := by rfl
def row1486 : Row := ⟨1486, 2139095040, 1384120320⟩
theorem derived1486 : clause1486.row = row1486 := by rfl
def entry1486 : CheckedRow := ⟨raw1486, clause1486, row1486, checked1486, derived1486⟩

def raw1487 : List String := ["function clause decode64 ((", "0b", "011111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1487", ") = {\n    SEE = ", "1487", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1487 : Clause := ⟨[.fixed "011111100", .any 1, .fixed "100001110110", .any 10], 1487, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_int_sisd_decode"⟩
theorem checked1487 : check raw1487 clause1487 = true := by rfl
def row1487 : Row := ⟨1487, 4290771968, 2116147200⟩
theorem derived1487 : clause1487.row = row1487 := by rfl
def entry1487 : CheckedRow := ⟨raw1487, clause1487, row1487, checked1487, derived1487⟩

def raw1488 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1488", ") = {\n    SEE = ", "1488", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_special_sqrt_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1488 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "100001111110", .any 10], 1488, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_special_sqrt_decode"⟩
theorem checked1488 : check raw1488 clause1488 = true := by rfl
def row1488 : Row := ⟨1488, 3217030144, 782366720⟩
theorem derived1488 : clause1488.row = row1488 := by rfl
def entry1488 : CheckedRow := ⟨raw1488, clause1488, row1488, checked1488, derived1488⟩

def raw1489 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1489", ") = {\n    SEE = ", "1489", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp_2008_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1489 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "1", .any 5, .fixed "110001", .any 10], 1489, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp_2008_decode"⟩
theorem checked1489 : check raw1489 clause1489 = true := by rfl
def row1489 : Row := ⟨1489, 3214998528, 773899264⟩
theorem derived1489 : clause1489.row = row1489 := by rfl
def entry1489 : CheckedRow := ⟨raw1489, clause1489, row1489, checked1489, derived1489⟩

def entries57 : List CheckedRow := [entry1482, entry1483, entry1484, entry1485, entry1486, entry1487, entry1488, entry1489]
def rows57 : List Row := [row1482, row1483, row1484, row1485, row1486, row1487, row1488, row1489]
theorem indices57 : rows57.map Row.index = [1482, 1483, 1484, 1485, 1486, 1487, 1488, 1489] := by rfl
theorem bound57 : entries57.map CheckedRow.row = rows57 := by rfl
theorem choices_and_57 : choices rows57 167837696#32 (-1) = [] := by rfl
theorem choices_orr_57 : choices rows57 704708608#32 (-1) = [] := by rfl
theorem choices_eor_57 : choices rows57 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_57 : choices rows57 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
