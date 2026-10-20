import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1666 : List String := ["function clause decode64 ((", "0b", "11011001000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1666", ") = {\n    SEE = ", "1666", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1666 : Clause := ⟨[.fixed "11011001000", .any 9, .fixed "00", .any 10], 1666, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1666 : check raw1666 clause1666 = true := by rfl
def row1666 : Row := ⟨1666, 4292873216, 3640655872⟩
theorem derived1666 : clause1666.row = row1666 := by rfl
def entry1666 : CheckedRow := ⟨raw1666, clause1666, row1666, checked1666, derived1666⟩

def raw1667 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1101010", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1667", ") = {\n    SEE = ", "1667", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "N", ", ", "shift", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1667 : Clause := ⟨[.any 1, .fixed "1101010", .any 2, .fixed "0", .any 21], 1667, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"N", 1, 21, 21, true⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_shiftedreg_decode"⟩
theorem checked1667 : check raw1667 clause1667 = true := by rfl
def row1667 : Row := ⟨1667, 2132803584, 1778384896⟩
theorem derived1667 : clause1667.row = row1667 := by rfl
def entry1667 : CheckedRow := ⟨raw1667, clause1667, row1667, checked1667, derived1667⟩

def raw1668 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "4", ")", " as op_code) if SEE < ", "1668", ") = {\n    SEE = ", "1668", ";\n", "    ", "nzcv", " : bits(", "4", ") = ", "op_code[", "3", " .. ", "0", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "4", "]]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_compare_cond_decode", "(", "nzcv", ", ", "op", ", ", "Rn", ", ", "cond", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1668 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 9, .fixed "01", .any 5, .fixed "1", .any 4], 1668, [⟨"nzcv", 4, 3, 0, false⟩, ⟨"op", 1, 4, 4, true⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_compare_cond_decode"⟩
theorem checked1668 : check raw1668 clause1668 = true := by rfl
def row1668 : Row := ⟨1668, 4280290320, 505414672⟩
theorem derived1668 : clause1668.row = row1668 := by rfl
def entry1668 : CheckedRow := ⟨raw1668, clause1668, row1668, checked1668, derived1668⟩

def raw1669 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1669", ") = {\n    SEE = ", "1669", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1669 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000", .any 2, .fixed "1", .any 5, .fixed "011100", .any 10], 1669, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1669 : check raw1669 clause1669 = true := by rfl
def row1669 : Row := ⟨1669, 3206609920, 3089133568⟩
theorem derived1669 : clause1669.row = row1669 := by rfl
def entry1669 : CheckedRow := ⟨raw1669, clause1669, row1669, checked1669, derived1669⟩

def raw1670 : List String := ["function clause decode64 ((", "0b", "010111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "010101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1670", ") = {\n    SEE = ", "1670", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_left_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1670 : Clause := ⟨[.fixed "010111110", .any 7, .fixed "010101", .any 10], 1670, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_left_sisd_decode"⟩
theorem checked1670 : check raw1670 clause1670 = true := by rfl
def row1670 : Row := ⟨1670, 4286643200, 1593857024⟩
theorem derived1670 : clause1670.row = row1670 := by rfl
def entry1670 : CheckedRow := ⟨raw1670, clause1670, row1670, checked1670, derived1670⟩

def raw1671 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1671", ") = {\n    SEE = ", "1671", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_accum_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1671 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "100000", .any 10], 1671, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_mul_accum_decode"⟩
theorem checked1671 : check raw1671 clause1671 = true := by rfl
def row1671 : Row := ⟨1671, 3206609920, 237010944⟩
theorem derived1671 : clause1671.row = row1671 := by rfl
def entry1671 : CheckedRow := ⟨raw1671, clause1671, row1671, checked1671, derived1671⟩

def raw1672 : List String := ["function clause decode64 ((", "0b", "010111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1672", ") = {\n    SEE = ", "1672", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_special_frecpx_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1672 : Clause := ⟨[.fixed "010111101", .any 1, .fixed "100001111110", .any 10], 1672, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_special_frecpx_decode"⟩
theorem checked1672 : check raw1672 clause1672 = true := by rfl
def row1672 : Row := ⟨1672, 4290771968, 1587673088⟩
theorem derived1672 : clause1672.row = row1672 := by rfl
def entry1672 : CheckedRow := ⟨raw1672, clause1672, row1672, checked1672, derived1672⟩

def raw1673 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001100110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1673", ") = {\n    SEE = ", "1673", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1673 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "100001100110", .any 10], 1673, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_round_decode"⟩
theorem checked1673 : check raw1673 clause1673 = true := by rfl
def row1673 : Row := ⟨1673, 3217030144, 782342144⟩
theorem derived1673 : clause1673.row = row1673 := by rfl
def entry1673 : CheckedRow := ⟨raw1673, clause1673, row1673, checked1673, derived1673⟩

def entries80 : List CheckedRow := [entry1666, entry1667, entry1668, entry1669, entry1670, entry1671, entry1672, entry1673]
def rows80 : List Row := [row1666, row1667, row1668, row1669, row1670, row1671, row1672, row1673]
theorem indices80 : rows80.map Row.index = [1666, 1667, 1668, 1669, 1670, 1671, 1672, 1673] := by rfl
theorem bound80 : entries80.map CheckedRow.row = rows80 := by rfl
theorem choices_and_80 : choices rows80 167837696#32 (-1) = [] := by rfl
theorem choices_orr_80 : choices rows80 704708608#32 (-1) = [] := by rfl
theorem choices_eor_80 : choices rows80 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_80 : choices rows80 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
