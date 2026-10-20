import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1746 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1746", ") = {\n    SEE = ", "1746", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1746 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "100000000000", .any 10], 1746, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1746 : check raw1746 clause1746 = true := by rfl
def row1746 : Row := ⟨1746, 2134899712, 505413632⟩
theorem derived1746 : clause1746.row = row1746 := by rfl
def entry1746 : CheckedRow := ⟨raw1746, clause1746, row1746, checked1746, derived1746⟩

def raw1747 : List String := ["function clause decode64 ((", "0b", "11010100001", " @ ", "_ : bits(", "16", ")", " @ ", "0b", "00000", " as op_code) if SEE < ", "1747", ") = {\n    SEE = ", "1747", ";\n", "    ", "LL", " : bits(", "2", ") = ", "op_code[", "1", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "4", " .. ", "2", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "23", " .. ", "21", "]", ";\n", "    ", "system_exceptions_debug_breakpoint_decode", "(", "LL", ", ", "op2", ", ", "imm16", ", ", "opc", ")\n}\n"]
def clause1747 : Clause := ⟨[.fixed "11010100001", .any 16, .fixed "00000"], 1747, [⟨"LL", 2, 1, 0, false⟩, ⟨"op2", 3, 4, 2, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"opc", 3, 23, 21, false⟩], "system_exceptions_debug_breakpoint_decode"⟩
theorem checked1747 : check raw1747 clause1747 = true := by rfl
def row1747 : Row := ⟨1747, 4292870175, 3558866944⟩
theorem derived1747 : clause1747.row = row1747 := by rfl
def entry1747 : CheckedRow := ⟨raw1747, clause1747, row1747, checked1747, derived1747⟩

def raw1748 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "010001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1748", ") = {\n    SEE = ", "1748", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_rightinsert_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1748 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "010001", .any 10], 1748, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_rightinsert_sisd_decode"⟩
theorem checked1748 : check raw1748 clause1748 = true := by rfl
def row1748 : Row := ⟨1748, 4286643200, 2130723840⟩
theorem derived1748 : clause1748.row = row1748 := by rfl
def entry1748 : CheckedRow := ⟨raw1748, clause1748, row1748, checked1748, derived1748⟩

def raw1749 : List String := ["function clause decode64 ((", "0b", "11111000100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1749", ") = {\n    SEE = ", "1749", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1749 : Clause := ⟨[.fixed "11111000100", .any 9, .fixed "00", .any 10], 1749, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1749 : check raw1749 clause1749 = true := by rfl
def row1749 : Row := ⟨1749, 4292873216, 4169138176⟩
theorem derived1749 : clause1749.row = row1749 := by rfl
def entry1749 : CheckedRow := ⟨raw1749, clause1749, row1749, checked1749, derived1749⟩

def raw1750 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1750", ") = {\n    SEE = ", "1750", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1750 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "100001000000", .any 10], 1750, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1750 : check raw1750 clause1750 = true := by rfl
def row1750 : Row := ⟨1750, 2134899712, 505479168⟩
theorem derived1750 : clause1750.row = row1750 := by rfl
def entry1750 : CheckedRow := ⟨raw1750, clause1750, row1750, checked1750, derived1750⟩

def raw1751 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1751", ") = {\n    SEE = ", "1751", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_rightnarrow_logical_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1751 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "100001", .any 10], 1751, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_rightnarrow_logical_decode"⟩
theorem checked1751 : check raw1751 clause1751 = true := by rfl
def row1751 : Row := ⟨1751, 3212901376, 251692032⟩
theorem derived1751 : clause1751.row = row1751 := by rfl
def entry1751 : CheckedRow := ⟨raw1751, clause1751, row1751, checked1751, derived1751⟩

def raw1752 : List String := ["function clause decode64 ((", "0b", "110110101100000100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1752", ") = {\n    SEE = ", "1752", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_pacda_dp_1src_decode", "(", "Rd", ", ", "Rn", ", ", "Z", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1752 : Clause := ⟨[.fixed "110110101100000100", .any 1, .fixed "010", .any 10], 1752, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Z", 1, 13, 13, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_pacda_dp_1src_decode"⟩
theorem checked1752 : check raw1752 clause1752 = true := by rfl
def row1752 : Row := ⟨1752, 4294958080, 3670083584⟩
theorem derived1752 : clause1752.row = row1752 := by rfl
def entry1752 : CheckedRow := ⟨raw1752, clause1752, row1752, checked1752, derived1752⟩

def raw1753 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1753", ") = {\n    SEE = ", "1753", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_special_recip_float_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1753 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "100001110110", .any 10], 1753, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_special_recip_float_simd_decode"⟩
theorem checked1753 : check raw1753 clause1753 = true := by rfl
def row1753 : Row := ⟨1753, 3217030144, 245487616⟩
theorem derived1753 : clause1753.row = row1753 := by rfl
def entry1753 : CheckedRow := ⟨raw1753, clause1753, row1753, checked1753, derived1753⟩

def entries90 : List CheckedRow := [entry1746, entry1747, entry1748, entry1749, entry1750, entry1751, entry1752, entry1753]
def rows90 : List Row := [row1746, row1747, row1748, row1749, row1750, row1751, row1752, row1753]
theorem indices90 : rows90.map Row.index = [1746, 1747, 1748, 1749, 1750, 1751, 1752, 1753] := by rfl
theorem bound90 : entries90.map CheckedRow.row = rows90 := by rfl
theorem choices_and_90 : choices rows90 167837696#32 (-1) = [] := by rfl
theorem choices_orr_90 : choices rows90 704708608#32 (-1) = [] := by rfl
theorem choices_eor_90 : choices rows90 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_90 : choices rows90 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
