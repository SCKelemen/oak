import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1642 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "101101011000000000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1642", ") = {\n    SEE = ", "1642", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_rbit_decode", "(", "Rd", ", ", "Rn", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1642 : Clause := ⟨[.any 1, .fixed "101101011000000000000", .any 10], 1642, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_rbit_decode"⟩
theorem checked1642 : check raw1642 clause1642 = true := by rfl
def row1642 : Row := ⟨1642, 2147482624, 1522532352⟩
theorem derived1642 : clause1642.row = row1642 := by rfl
def entry1642 : CheckedRow := ⟨raw1642, clause1642, row1642, checked1642, derived1642⟩

def raw1643 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1643", ") = {\n    SEE = ", "1643", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp_product_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1643 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "1", .any 5, .fixed "110111", .any 10], 1643, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp_product_decode"⟩
theorem checked1643 : check raw1643 clause1643 = true := by rfl
def row1643 : Row := ⟨1643, 3214998528, 773905408⟩
theorem derived1643 : clause1643.row = row1643 := by rfl
def entry1643 : CheckedRow := ⟨raw1643, clause1643, row1643, checked1643, derived1643⟩

def raw1644 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1644", ") = {\n    SEE = ", "1644", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp_1985_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1644 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "1", .any 5, .fixed "111101", .any 10], 1644, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp_1985_decode"⟩
theorem checked1644 : check raw1644 clause1644 = true := by rfl
def row1644 : Row := ⟨1644, 3214998528, 245429248⟩
theorem derived1644 : clause1644.row = row1644 := by rfl
def entry1644 : CheckedRow := ⟨raw1644, clause1644, row1644, checked1644, derived1644⟩

def raw1645 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1645", ") = {\n    SEE = ", "1645", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1645 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000000", .any 9, .fixed "10", .any 10], 1645, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode"⟩
theorem checked1645 : check raw1645 clause1645 = true := by rfl
def row1645 : Row := ⟨1645, 3219131392, 3087009792⟩
theorem derived1645 : clause1645.row = row1645 := by rfl
def entry1645 : CheckedRow := ⟨raw1645, clause1645, row1645, checked1645, derived1645⟩

def raw1646 : List String := ["function clause decode64 ((", "0b", "1101011", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011111100001", " @ ", "_ : bits(", "11", ")", " as op_code) if SEE < ", "1646", ") = {\n    SEE = ", "1646", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "22", " .. ", "21", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "branch_unconditional_register_decode", "(", "Rm", ", ", "Rn", ", ", "M", ", ", "A", ", ", "op2", ", ", "op", ", ", "Z", ")\n}\n"]
def clause1646 : Clause := ⟨[.fixed "1101011", .any 1, .fixed "0011111100001", .any 11], 1646, [⟨"Rm", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"M", 1, 10, 10, true⟩, ⟨"A", 1, 11, 11, true⟩, ⟨"op2", 5, 20, 16, false⟩, ⟨"op", 2, 22, 21, false⟩, ⟨"Z", 1, 24, 24, true⟩], "branch_unconditional_register_decode"⟩
theorem checked1646 : check raw1646 clause1646 = true := by rfl
def row1646 : Row := ⟨1646, 4278188032, 3594455040⟩
theorem derived1646 : clause1646.row = row1646 := by rfl
def entry1646 : CheckedRow := ⟨raw1646, clause1646, row1646, checked1646, derived1646⟩

def raw1647 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "010101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1647", ") = {\n    SEE = ", "1647", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_leftinsert_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1647 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "010101", .any 10], 1647, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_leftinsert_simd_decode"⟩
theorem checked1647 : check raw1647 clause1647 = true := by rfl
def row1647 : Row := ⟨1647, 3212901376, 788550656⟩
theorem derived1647 : clause1647.row = row1647 := by rfl
def entry1647 : CheckedRow := ⟨raw1647, clause1647, row1647, checked1647, derived1647⟩

def raw1648 : List String := ["function clause decode64 ((", "0b", "011111111", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "1001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1648", ") = {\n    SEE = ", "1648", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_fp_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1648 : Clause := ⟨[.fixed "011111111", .any 7, .fixed "1001", .any 1, .fixed "0", .any 10], 1648, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mul_fp_sisd_decode"⟩
theorem checked1648 : check raw1648 clause1648 = true := by rfl
def row1648 : Row := ⟨1648, 4286641152, 2139131904⟩
theorem derived1648 : clause1648.row = row1648 := by rfl
def entry1648 : CheckedRow := ⟨raw1648, clause1648, row1648, checked1648, derived1648⟩

def raw1649 : List String := ["function clause decode64 ((", "0b", "01011110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1649", ") = {\n    SEE = ", "1649", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_recpsfp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ")\n}\n"]
def clause1649 : Clause := ⟨[.fixed "01011110010", .any 5, .fixed "001111", .any 10], 1649, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_recpsfp16_sisd_decode"⟩
theorem checked1649 : check raw1649 clause1649 = true := by rfl
def row1649 : Row := ⟨1649, 4292934656, 1581267968⟩
theorem derived1649 : clause1649.row = row1649 := by rfl
def entry1649 : CheckedRow := ⟨raw1649, clause1649, row1649, checked1649, derived1649⟩

def entries77 : List CheckedRow := [entry1642, entry1643, entry1644, entry1645, entry1646, entry1647, entry1648, entry1649]
def rows77 : List Row := [row1642, row1643, row1644, row1645, row1646, row1647, row1648, row1649]
theorem indices77 : rows77.map Row.index = [1642, 1643, 1644, 1645, 1646, 1647, 1648, 1649] := by rfl
theorem bound77 : entries77.map CheckedRow.row = rows77 := by rfl
theorem choices_and_77 : choices rows77 167837696#32 (-1) = [] := by rfl
theorem choices_orr_77 : choices rows77 704708608#32 (-1) = [] := by rfl
theorem choices_eor_77 : choices rows77 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_77 : choices rows77 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
