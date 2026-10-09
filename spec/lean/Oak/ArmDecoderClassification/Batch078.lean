import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1650 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1650", ") = {\n    SEE = ", "1650", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_rightnarrow_uniform_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1650 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "100101", .any 10], 1650, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_rightnarrow_uniform_sisd_decode"⟩
theorem checked1650 : check raw1650 clause1650 = true := by rfl
def row1650 : Row := ⟨1650, 4286643200, 2130744320⟩
theorem derived1650 : clause1650.row = row1650 := by rfl
def entry1650 : CheckedRow := ⟨raw1650, clause1650, row1650, checked1650, derived1650⟩

def raw1651 : List String := ["function clause decode64 ((", "0b", "1101010100000011001000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1651", ") = {\n    SEE = ", "1651", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "integer_pac_pacib_hint_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1651 : Clause := ⟨[.fixed "1101010100000011001000", .any 1, .fixed "101", .any 1, .fixed "11111"], 1651, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "integer_pac_pacib_hint_decode"⟩
theorem checked1651 : check raw1651 clause1651 = true := by rfl
def row1651 : Row := ⟨1651, 4294966751, 3573752159⟩
theorem derived1651 : clause1651.row = row1651 := by rfl
def entry1651 : CheckedRow := ⟨raw1651, clause1651, row1651, checked1651, derived1651⟩

def raw1652 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "0010", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1652", ") = {\n    SEE = ", "1652", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_long_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1652 : Clause := ⟨[.fixed "0", .any 1, .fixed "101111", .any 8, .fixed "0010", .any 1, .fixed "0", .any 10], 1652, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_long_decode"⟩
theorem checked1652 : check raw1652 clause1652 = true := by rfl
def row1652 : Row := ⟨1652, 3204510720, 788537344⟩
theorem derived1652 : clause1652.row = row1652 := by rfl
def entry1652 : CheckedRow := ⟨raw1652, clause1652, row1652, checked1652, derived1652⟩

def raw1653 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1653", ") = {\n    SEE = ", "1653", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "13", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_maxmin_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1653 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "010110", .any 10], 1653, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 2, 13, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_maxmin_decode"⟩
theorem checked1653 : check raw1653 clause1653 = true := by rfl
def row1653 : Row := ⟨1653, 4280351744, 505436160⟩
theorem derived1653 : clause1653.row = row1653 := by rfl
def entry1653 : CheckedRow := ⟨raw1653, clause1653, row1653, checked1653, derived1653⟩

def raw1654 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000011110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1654", ") = {\n    SEE = ", "1654", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_sat_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1654 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100000011110", .any 10], 1654, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_diffneg_sat_simd_decode"⟩
theorem checked1654 : check raw1654 clause1654 = true := by rfl
def row1654 : Row := ⟨1654, 3208641536, 773879808⟩
theorem derived1654 : clause1654.row = row1654 := by rfl
def entry1654 : CheckedRow := ⟨raw1654, clause1654, row1654, checked1654, derived1654⟩

def raw1655 : List String := ["function clause decode64 ((", "0b", "11010100010", " @ ", "_ : bits(", "16", ")", " @ ", "0b", "00000", " as op_code) if SEE < ", "1655", ") = {\n    SEE = ", "1655", ";\n", "    ", "LL", " : bits(", "2", ") = ", "op_code[", "1", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "4", " .. ", "2", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "23", " .. ", "21", "]", ";\n", "    ", "system_exceptions_debug_halt_decode", "(", "LL", ", ", "op2", ", ", "imm16", ", ", "opc", ")\n}\n"]
def clause1655 : Clause := ⟨[.fixed "11010100010", .any 16, .fixed "00000"], 1655, [⟨"LL", 2, 1, 0, false⟩, ⟨"op2", 3, 4, 2, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"opc", 3, 23, 21, false⟩], "system_exceptions_debug_halt_decode"⟩
theorem checked1655 : check raw1655 clause1655 = true := by rfl
def row1655 : Row := ⟨1655, 4292870175, 3560964096⟩
theorem derived1655 : clause1655.row = row1655 := by rfl
def entry1655 : CheckedRow := ⟨raw1655, clause1655, row1655, checked1655, derived1655⟩

def raw1656 : List String := ["function clause decode64 ((", "0b", "11010101000000110010000000111111", " as op_code) if SEE < ", "1656", ") = {\n    SEE = ", "1656", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_hints_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1656 : Clause := ⟨[.fixed "11010101000000110010000000111111"], 1656, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_hints_decode"⟩
theorem checked1656 : check raw1656 clause1656 = true := by rfl
def row1656 : Row := ⟨1656, 4294967295, 3573751871⟩
theorem derived1656 : clause1656.row = row1656 := by rfl
def entry1656 : CheckedRow := ⟨raw1656, clause1656, row1656, checked1656, derived1656⟩

def raw1657 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1657", ") = {\n    SEE = ", "1657", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1657 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "100001101110", .any 10], 1657, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_simd_decode"⟩
theorem checked1657 : check raw1657 clause1657 = true := by rfl
def row1657 : Row := ⟨1657, 3217030144, 773961728⟩
theorem derived1657 : clause1657.row = row1657 := by rfl
def entry1657 : CheckedRow := ⟨raw1657, clause1657, row1657, checked1657, derived1657⟩

def entries78 : List CheckedRow := [entry1650, entry1651, entry1652, entry1653, entry1654, entry1655, entry1656, entry1657]
def rows78 : List Row := [row1650, row1651, row1652, row1653, row1654, row1655, row1656, row1657]
theorem indices78 : rows78.map Row.index = [1650, 1651, 1652, 1653, 1654, 1655, 1656, 1657] := by rfl
theorem bound78 : entries78.map CheckedRow.row = rows78 := by rfl
theorem choices_and_78 : choices rows78 167837696#32 (-1) = [] := by rfl
theorem choices_orr_78 : choices rows78 704708608#32 (-1) = [] := by rfl
theorem choices_eor_78 : choices rows78 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_78 : choices rows78 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
