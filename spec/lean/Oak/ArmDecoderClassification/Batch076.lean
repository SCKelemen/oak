import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1634 : List String := ["function clause decode64 ((", "0b", "011111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1634", ") = {\n    SEE = ", "1634", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ")\n}\n"]
def clause1634 : Clause := ⟨[.fixed "011111100", .any 1, .fixed "1", .any 5, .fixed "111001", .any 10], 1634, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode"⟩
theorem checked1634 : check raw1634 clause1634 = true := by rfl
def row1634 : Row := ⟨1634, 4288740352, 2116084736⟩
theorem derived1634 : clause1634.row = row1634 := by rfl
def entry1634 : CheckedRow := ⟨raw1634, clause1634, row1634, checked1634, derived1634⟩

def raw1635 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1635", ") = {\n    SEE = ", "1635", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1635 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "1", .any 5, .fixed "010001", .any 10], 1635, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_shift_sisd_decode"⟩
theorem checked1635 : check raw1635 clause1635 = true := by rfl
def row1635 : Row := ⟨1635, 4280351744, 2116043776⟩
theorem derived1635 : clause1635.row = row1635 := by rfl
def entry1635 : CheckedRow := ⟨raw1635, clause1635, row1635, checked1635, derived1635⟩

def raw1636 : List String := ["function clause decode64 ((", "0b", "1101010100001", " @ ", "_ : bits(", "19", ")", " as op_code) if SEE < ", "1636", ") = {\n    SEE = ", "1636", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_sysops_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1636 : Clause := ⟨[.fixed "1101010100001", .any 19], 1636, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_sysops_decode"⟩
theorem checked1636 : check raw1636 clause1636 = true := by rfl
def row1636 : Row := ⟨1636, 4294443008, 3574071296⟩
theorem derived1636 : clause1636.row = row1636 := by rfl
def entry1636 : CheckedRow := ⟨raw1636, clause1636, row1636, checked1636, derived1636⟩

def raw1637 : List String := ["function clause decode64 ((", "0b", "1101011000011111000000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "00000", " as op_code) if SEE < ", "1637", ") = {\n    SEE = ", "1637", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "22", " .. ", "21", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "branch_unconditional_register_decode", "(", "Rm", ", ", "Rn", ", ", "M", ", ", "A", ", ", "op2", ", ", "op", ", ", "Z", ")\n}\n"]
def clause1637 : Clause := ⟨[.fixed "1101011000011111000000", .any 5, .fixed "00000"], 1637, [⟨"Rm", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"M", 1, 10, 10, true⟩, ⟨"A", 1, 11, 11, true⟩, ⟨"op2", 5, 20, 16, false⟩, ⟨"op", 2, 22, 21, false⟩, ⟨"Z", 1, 24, 24, true⟩], "branch_unconditional_register_decode"⟩
theorem checked1637 : check raw1637 clause1637 = true := by rfl
def row1637 : Row := ⟨1637, 4294966303, 3592355840⟩
theorem derived1637 : clause1637.row = row1637 := by rfl
def entry1637 : CheckedRow := ⟨raw1637, clause1637, row1637, checked1637, derived1637⟩

def raw1638 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1638", ") = {\n    SEE = ", "1638", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_fp_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1638 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "1", .any 5, .fixed "110101", .any 10], 1638, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_fp_decode"⟩
theorem checked1638 : check raw1638 clause1638 = true := by rfl
def row1638 : Row := ⟨1638, 3214998528, 237032448⟩
theorem derived1638 : clause1638.row = row1638 := by rfl
def entry1638 : CheckedRow := ⟨raw1638, clause1638, row1638, checked1638, derived1638⟩

def raw1639 : List String := ["function clause decode64 ((", "0b", "01011001000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1639", ") = {\n    SEE = ", "1639", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1639 : Clause := ⟨[.fixed "01011001000", .any 9, .fixed "00", .any 10], 1639, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1639 : check raw1639 clause1639 = true := by rfl
def row1639 : Row := ⟨1639, 4292873216, 1493172224⟩
theorem derived1639 : clause1639.row = row1639 := by rfl
def entry1639 : CheckedRow := ⟨raw1639, clause1639, row1639, checked1639, derived1639⟩

def raw1640 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1640", ") = {\n    SEE = ", "1640", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_simd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1640 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "010111", .any 10], 1640, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_shift_simd_decode"⟩
theorem checked1640 : check raw1640 clause1640 = true := by rfl
def row1640 : Row := ⟨1640, 3206609920, 773872640⟩
theorem derived1640 : clause1640.row = row1640 := by rfl
def entry1640 : CheckedRow := ⟨raw1640, clause1640, row1640, checked1640, derived1640⟩

def raw1641 : List String := ["function clause decode64 ((", "0b", "0101111011111001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1641", ") = {\n    SEE = ", "1641", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1641 : Clause := ⟨[.fixed "0101111011111001101010", .any 10], 1641, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode"⟩
theorem checked1641 : check raw1641 clause1641 = true := by rfl
def row1641 : Row := ⟨1641, 4294966272, 1593419776⟩
theorem derived1641 : clause1641.row = row1641 := by rfl
def entry1641 : CheckedRow := ⟨raw1641, clause1641, row1641, checked1641, derived1641⟩

def entries76 : List CheckedRow := [entry1634, entry1635, entry1636, entry1637, entry1638, entry1639, entry1640, entry1641]
def rows76 : List Row := [row1634, row1635, row1636, row1637, row1638, row1639, row1640, row1641]
theorem indices76 : rows76.map Row.index = [1634, 1635, 1636, 1637, 1638, 1639, 1640, 1641] := by rfl
theorem bound76 : entries76.map CheckedRow.row = rows76 := by rfl
theorem choices_and_76 : choices rows76 167837696#32 (-1) = [] := by rfl
theorem choices_orr_76 : choices rows76 704708608#32 (-1) = [] := by rfl
theorem choices_eor_76 : choices rows76 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_76 : choices rows76 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
