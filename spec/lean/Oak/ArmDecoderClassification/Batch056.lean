import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1474 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111100", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "0001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1474", ") = {\n    SEE = ", "1474", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1474 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111100", .any 6, .fixed "0001", .any 1, .fixed "0", .any 10], 1474, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_fp16_simd_decode"⟩
theorem checked1474 : check raw1474 clause1474 = true := by rfl
def row1474 : Row := ⟨1474, 3217093632, 251662336⟩
theorem derived1474 : clause1474.row = row1474 := by rfl
def entry1474 : CheckedRow := ⟨raw1474, clause1474, row1474, checked1474, derived1474⟩

def raw1475 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1475", ") = {\n    SEE = ", "1475", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op2", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode2_5_2_", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_shift_variable_decode", "(", "Rd", ", ", "Rn", ", ", "op2", ", ", "opcode2_5_2_", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1475 : Clause := ⟨[.any 1, .fixed "0011010110", .any 5, .fixed "001011", .any 10], 1475, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op2", 2, 11, 10, false⟩, ⟨"opcode2_5_2_", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_shift_variable_decode"⟩
theorem checked1475 : check raw1475 clause1475 = true := by rfl
def row1475 : Row := ⟨1475, 2145451008, 448801792⟩
theorem derived1475 : clause1475.row = row1475 := by rfl
def entry1475 : CheckedRow := ⟨raw1475, clause1475, row1475, checked1475, derived1475⟩

def raw1476 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110101", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1476", ") = {\n    SEE = ", "1476", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc2", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_logical_bsleor_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "opc2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1476 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110101", .any 5, .fixed "000111", .any 10], 1476, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc2", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_logical_bsleor_decode"⟩
theorem checked1476 : check raw1476 clause1476 = true := by rfl
def row1476 : Row := ⟨1476, 3219192832, 782244864⟩
theorem derived1476 : clause1476.row = row1476 := by rfl
def entry1476 : CheckedRow := ⟨raw1476, clause1476, row1476, checked1476, derived1476⟩

def raw1477 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1011", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1477", ") = {\n    SEE = ", "1477", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_double_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1477 : Clause := ⟨[.fixed "0", .any 1, .fixed "001111", .any 8, .fixed "1011", .any 1, .fixed "0", .any 10], 1477, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mul_double_simd_decode"⟩
theorem checked1477 : check raw1477 clause1477 = true := by rfl
def row1477 : Row := ⟨1477, 3204510720, 251703296⟩
theorem derived1477 : clause1477.row = row1477 := by rfl
def entry1477 : CheckedRow := ⟨raw1477, clause1477, row1477, checked1477, derived1477⟩

def raw1478 : List String := ["function clause decode64 ((", "0b", "01111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1478", ") = {\n    SEE = ", "1478", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1478 : Clause := ⟨[.fixed "01111000", .any 2, .fixed "1", .any 5, .fixed "001100", .any 10], 1478, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1478 : check raw1478 clause1478 = true := by rfl
def row1478 : Row := ⟨1478, 4280351744, 2015375360⟩
theorem derived1478 : clause1478.row = row1478 := by rfl
def entry1478 : CheckedRow := ⟨raw1478, clause1478, row1478, checked1478, derived1478⟩

def raw1479 : List String := ["function clause decode64 ((", "0b", "1101010100000010001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1479", ") = {\n    SEE = ", "1479", ";\n", "    ", "Xt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "integer_tags_mcgettagarray_decode", "(", "Xt", ", ", "Xn", ")\n}\n"]
def clause1479 : Clause := ⟨[.fixed "1101010100000010001001", .any 10], 1479, [⟨"Xt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩], "integer_tags_mcgettagarray_decode"⟩
theorem checked1479 : check raw1479 clause1479 = true := by rfl
def row1479 : Row := ⟨1479, 4294966272, 3573687296⟩
theorem derived1479 : clause1479.row = row1479 := by rfl
def entry1479 : CheckedRow := ⟨raw1479, clause1479, row1479, checked1479, derived1479⟩

def raw1480 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001011010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1480", ") = {\n    SEE = ", "1480", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_narrow_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1480 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "100001011010", .any 10], 1480, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_narrow_decode"⟩
theorem checked1480 : check raw1480 clause1480 = true := by rfl
def row1480 : Row := ⟨1480, 3217030144, 237070336⟩
theorem derived1480 : clause1480.row = row1480 := by rfl
def entry1480 : CheckedRow := ⟨raw1480, clause1480, row1480, checked1480, derived1480⟩

def raw1481 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1481", ") = {\n    SEE = ", "1481", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_special_recip_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1481 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "100001110010", .any 10], 1481, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_special_recip_int_decode"⟩
theorem checked1481 : check raw1481 clause1481 = true := by rfl
def row1481 : Row := ⟨1481, 3217030144, 245483520⟩
theorem derived1481 : clause1481.row = row1481 := by rfl
def entry1481 : CheckedRow := ⟨raw1481, clause1481, row1481, checked1481, derived1481⟩

def entries56 : List CheckedRow := [entry1474, entry1475, entry1476, entry1477, entry1478, entry1479, entry1480, entry1481]
def rows56 : List Row := [row1474, row1475, row1476, row1477, row1478, row1479, row1480, row1481]
theorem indices56 : rows56.map Row.index = [1474, 1475, 1476, 1477, 1478, 1479, 1480, 1481] := by rfl
theorem bound56 : entries56.map CheckedRow.row = rows56 := by rfl
theorem choices_and_56 : choices rows56 167837696#32 (-1) = [] := by rfl
theorem choices_orr_56 : choices rows56 704708608#32 (-1) = [] := by rfl
theorem choices_eor_56 : choices rows56 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_56 : choices rows56 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
