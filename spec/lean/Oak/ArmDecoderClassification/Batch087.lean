import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1722 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0111010010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "4", ")", " as op_code) if SEE < ", "1722", ") = {\n    SEE = ", "1722", ";\n", "    ", "nzcv", " : bits(", "4", ") = ", "op_code[", "3", " .. ", "0", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "4", "]]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_conditional_compare_register_decode", "(", "nzcv", ", ", "o3", ", ", "Rn", ", ", "o2", ", ", "cond", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1722 : Clause := ⟨[.any 1, .fixed "0111010010", .any 9, .fixed "00", .any 5, .fixed "0", .any 4], 1722, [⟨"nzcv", 4, 3, 0, false⟩, ⟨"o3", 1, 4, 4, true⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o2", 1, 10, 10, true⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_conditional_compare_register_decode"⟩
theorem checked1722 : check raw1722 clause1722 = true := by rfl
def row1722 : Row := ⟨1722, 2145389584, 977272832⟩
theorem derived1722 : clause1722.row = row1722 := by rfl
def entry1722 : CheckedRow := ⟨raw1722, clause1722, row1722, checked1722, derived1722⟩

def raw1723 : List String := ["function clause decode64 ((", "0b", "00111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1723", ") = {\n    SEE = ", "1723", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1723 : Clause := ⟨[.fixed "00111000", .any 2, .fixed "1", .any 5, .fixed "001000", .any 10], 1723, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1723 : check raw1723 clause1723 = true := by rfl
def row1723 : Row := ⟨1723, 4280351744, 941629440⟩
theorem derived1723 : clause1723.row = row1723 := by rfl
def entry1723 : CheckedRow := ⟨raw1723, clause1723, row1723, checked1723, derived1723⟩

def raw1724 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "0110", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1724", ") = {\n    SEE = ", "1724", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_long_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1724 : Clause := ⟨[.fixed "0", .any 1, .fixed "101111", .any 8, .fixed "0110", .any 1, .fixed "0", .any 10], 1724, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_long_decode"⟩
theorem checked1724 : check raw1724 clause1724 = true := by rfl
def row1724 : Row := ⟨1724, 3204510720, 788553728⟩
theorem derived1724 : clause1724.row = row1724 := by rfl
def entry1724 : CheckedRow := ⟨raw1724, clause1724, row1724, checked1724, derived1724⟩

def raw1725 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110011", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1725", ") = {\n    SEE = ", "1725", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc2", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_logical_bsleor_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "opc2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1725 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110011", .any 5, .fixed "000111", .any 10], 1725, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc2", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_logical_bsleor_decode"⟩
theorem checked1725 : check raw1725 clause1725 = true := by rfl
def row1725 : Row := ⟨1725, 3219192832, 778050560⟩
theorem derived1725 : clause1725.row = row1725 := by rfl
def entry1725 : CheckedRow := ⟨raw1725, clause1725, row1725, checked1725, derived1725⟩

def raw1726 : List String := ["function clause decode64 ((", "0b", "11010110100111110000001111100000", " as op_code) if SEE < ", "1726", ") = {\n    SEE = ", "1726", ";\n", "    ", "op4", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "branch_unconditional_eret_decode", "(", "op4", ", ", "Rn", ", ", "M", ", ", "A", ", ", "op2", ")\n}\n"]
def clause1726 : Clause := ⟨[.fixed "11010110100111110000001111100000"], 1726, [⟨"op4", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"M", 1, 10, 10, true⟩, ⟨"A", 1, 11, 11, true⟩, ⟨"op2", 5, 20, 16, false⟩], "branch_unconditional_eret_decode"⟩
theorem checked1726 : check raw1726 clause1726 = true := by rfl
def row1726 : Row := ⟨1726, 4294967295, 3600745440⟩
theorem derived1726 : clause1726.row = row1726 := by rfl
def entry1726 : CheckedRow := ⟨raw1726, clause1726, row1726, checked1726, derived1726⟩

def raw1727 : List String := ["function clause decode64 ((", "0b", "010111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1727", ") = {\n    SEE = ", "1727", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1727 : Clause := ⟨[.fixed "010111101", .any 1, .fixed "100001101010", .any 10], 1727, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode"⟩
theorem checked1727 : check raw1727 clause1727 = true := by rfl
def row1727 : Row := ⟨1727, 4290771968, 1587652608⟩
theorem derived1727 : clause1727.row = row1727 := by rfl
def entry1727 : CheckedRow := ⟨raw1727, clause1727, row1727, checked1727, derived1727⟩

def raw1728 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1728", ") = {\n    SEE = ", "1728", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_int_accum_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1728 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "100101", .any 10], 1728, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_int_accum_decode"⟩
theorem checked1728 : check raw1728 clause1728 = true := by rfl
def row1728 : Row := ⟨1728, 3206609920, 773886976⟩
theorem derived1728 : clause1728.row = row1728 := by rfl
def entry1728 : CheckedRow := ⟨raw1728, clause1728, row1728, checked1728, derived1728⟩

def raw1729 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1729", ") = {\n    SEE = ", "1729", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_right_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1729 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "000101", .any 10], 1729, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_right_sisd_decode"⟩
theorem checked1729 : check raw1729 clause1729 = true := by rfl
def row1729 : Row := ⟨1729, 4286643200, 2130711552⟩
theorem derived1729 : clause1729.row = row1729 := by rfl
def entry1729 : CheckedRow := ⟨raw1729, clause1729, row1729, checked1729, derived1729⟩

def entries87 : List CheckedRow := [entry1722, entry1723, entry1724, entry1725, entry1726, entry1727, entry1728, entry1729]
def rows87 : List Row := [row1722, row1723, row1724, row1725, row1726, row1727, row1728, row1729]
theorem indices87 : rows87.map Row.index = [1722, 1723, 1724, 1725, 1726, 1727, 1728, 1729] := by rfl
theorem bound87 : entries87.map CheckedRow.row = rows87 := by rfl
theorem choices_and_87 : choices rows87 167837696#32 (-1) = [] := by rfl
theorem choices_orr_87 : choices rows87 704708608#32 (-1) = [] := by rfl
theorem choices_eor_87 : choices rows87 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_87 : choices rows87 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
