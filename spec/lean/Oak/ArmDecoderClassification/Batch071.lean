import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1594 : List String := ["function clause decode64 ((", "0b", "11010101000000110010", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1594", ") = {\n    SEE = ", "1594", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_hints_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1594 : Clause := ⟨[.fixed "11010101000000110010", .any 7, .fixed "11111"], 1594, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_hints_decode"⟩
theorem checked1594 : check raw1594 clause1594 = true := by rfl
def row1594 : Row := ⟨1594, 4294963231, 3573751839⟩
theorem derived1594 : clause1594.row = row1594 := by rfl
def entry1594 : CheckedRow := ⟨raw1594, clause1594, row1594, checked1594, derived1594⟩

def raw1595 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00110101000000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1595", ") = {\n    SEE = ", "1595", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1595 : Clause := ⟨[.fixed "0", .any 1, .fixed "00110101000000", .any 2, .fixed "1", .any 13], 1595, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1595 : check raw1595 clause1595 = true := by rfl
def row1595 : Row := ⟨1595, 3221168128, 222306304⟩
theorem derived1595 : clause1595.row = row1595 := by rfl
def entry1595 : CheckedRow := ⟨raw1595, clause1595, row1595, checked1595, derived1595⟩

def raw1596 : List String := ["function clause decode64 ((", "0b", "010010001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "11111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1596", ") = {\n    SEE = ", "1596", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_cas_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1596 : Clause := ⟨[.fixed "010010001", .any 1, .fixed "1", .any 6, .fixed "11111", .any 10], 1596, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_cas_single_decode"⟩
theorem checked1596 : check raw1596 clause1596 = true := by rfl
def row1596 : Row := ⟨1596, 4288707584, 1218477056⟩
theorem derived1596 : clause1596.row = row1596 := by rfl
def entry1596 : CheckedRow := ⟨raw1596, clause1596, row1596, checked1596, derived1596⟩

def raw1597 : List String := ["function clause decode64 ((", "0b", "100101", " @ ", "_ : bits(", "26", ")", " as op_code) if SEE < ", "1597", ") = {\n    SEE = ", "1597", ";\n", "    ", "imm26", " : bits(", "26", ") = ", "op_code[", "25", " .. ", "0", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "branch_unconditional_immediate_decode", "(", "imm26", ", ", "op", ")\n}\n"]
def clause1597 : Clause := ⟨[.fixed "100101", .any 26], 1597, [⟨"imm26", 26, 25, 0, false⟩, ⟨"op", 1, 31, 31, true⟩], "branch_unconditional_immediate_decode"⟩
theorem checked1597 : check raw1597 clause1597 = true := by rfl
def row1597 : Row := ⟨1597, 4227858432, 2483027968⟩
theorem derived1597 : clause1597.row = row1597 := by rfl
def entry1597 : CheckedRow := ⟨raw1597, clause1597, row1597, checked1597, derived1597⟩

def raw1598 : List String := ["function clause decode64 ((", "0b", "01111000010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1598", ") = {\n    SEE = ", "1598", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1598 : Clause := ⟨[.fixed "01111000010", .any 9, .fixed "10", .any 10], 1598, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode"⟩
theorem checked1598 : check raw1598 clause1598 = true := by rfl
def row1598 : Row := ⟨1598, 4292873216, 2017462272⟩
theorem derived1598 : clause1598.row = row1598 := by rfl
def entry1598 : CheckedRow := ⟨raw1598, clause1598, row1598, checked1598, derived1598⟩

def raw1599 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001011010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1599", ") = {\n    SEE = ", "1599", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_xtn_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1599 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "100001011010", .any 10], 1599, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_xtn_simd_decode"⟩
theorem checked1599 : check raw1599 clause1599 = true := by rfl
def row1599 : Row := ⟨1599, 3217030144, 773941248⟩
theorem derived1599 : clause1599.row = row1599 := by rfl
def entry1599 : CheckedRow := ⟨raw1599, clause1599, row1599, checked1599, derived1599⟩

def raw1600 : List String := ["function clause decode64 ((", "0b", "110110101100000100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1600", ") = {\n    SEE = ", "1600", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_pacia_dp_1src_decode", "(", "Rd", ", ", "Rn", ", ", "Z", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1600 : Clause := ⟨[.fixed "110110101100000100", .any 1, .fixed "000", .any 10], 1600, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Z", 1, 13, 13, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_pacia_dp_1src_decode"⟩
theorem checked1600 : check raw1600 clause1600 = true := by rfl
def row1600 : Row := ⟨1600, 4294958080, 3670081536⟩
theorem derived1600 : clause1600.row = row1600 := by rfl
def entry1600 : CheckedRow := ⟨raw1600, clause1600, row1600, checked1600, derived1600⟩

def raw1601 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1601", ") = {\n    SEE = ", "1601", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1601 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "100000110010", .any 10], 1601, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_float_bulk_simd_decode"⟩
theorem checked1601 : check raw1601 clause1601 = true := by rfl
def row1601 : Row := ⟨1601, 3217030144, 245417984⟩
theorem derived1601 : clause1601.row = row1601 := by rfl
def entry1601 : CheckedRow := ⟨raw1601, clause1601, row1601, checked1601, derived1601⟩

def entries71 : List CheckedRow := [entry1594, entry1595, entry1596, entry1597, entry1598, entry1599, entry1600, entry1601]
def rows71 : List Row := [row1594, row1595, row1596, row1597, row1598, row1599, row1600, row1601]
theorem indices71 : rows71.map Row.index = [1594, 1595, 1596, 1597, 1598, 1599, 1600, 1601] := by rfl
theorem bound71 : entries71.map CheckedRow.row = rows71 := by rfl
theorem choices_and_71 : choices rows71 167837696#32 (-1) = [] := by rfl
theorem choices_orr_71 : choices rows71 704708608#32 (-1) = [] := by rfl
theorem choices_eor_71 : choices rows71 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_71 : choices rows71 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
