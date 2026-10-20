import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1570 : List String := ["function clause decode64 ((", "0b", "01111000010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1570", ") = {\n    SEE = ", "1570", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1570 : Clause := ⟨[.fixed "01111000010", .any 9, .fixed "11", .any 10], 1570, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1570 : check raw1570 clause1570 = true := by rfl
def row1570 : Row := ⟨1570, 4292873216, 2017463296⟩
theorem derived1570 : clause1570.row = row1570 := by rfl
def entry1570 : CheckedRow := ⟨raw1570, clause1570, row1570, checked1570, derived1570⟩

def raw1571 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1571", ") = {\n    SEE = ", "1571", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_rightnarrow_uniform_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1571 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "100111", .any 10], 1571, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_rightnarrow_uniform_simd_decode"⟩
theorem checked1571 : check raw1571 clause1571 = true := by rfl
def row1571 : Row := ⟨1571, 3212901376, 251698176⟩
theorem derived1571 : clause1571.row = row1571 := by rfl
def entry1571 : CheckedRow := ⟨raw1571, clause1571, row1571, checked1571, derived1571⟩

def raw1572 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "101011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1572", ") = {\n    SEE = ", "1572", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_pair_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1572 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "101011", .any 10], 1572, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_pair_decode"⟩
theorem checked1572 : check raw1572 clause1572 = true := by rfl
def row1572 : Row := ⟨1572, 3206609920, 237022208⟩
theorem derived1572 : clause1572.row = row1572 := by rfl
def entry1572 : CheckedRow := ⟨raw1572, clause1572, row1572, checked1572, derived1572⟩

def raw1573 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1573", ") = {\n    SEE = ", "1573", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1573 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "100001100010", .any 10], 1573, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_round_decode"⟩
theorem checked1573 : check raw1573 clause1573 = true := by rfl
def row1573 : Row := ⟨1573, 3217030144, 237078528⟩
theorem derived1573 : clause1573.row = row1573 := by rfl
def entry1573 : CheckedRow := ⟨raw1573, clause1573, row1573, checked1573, derived1573⟩

def raw1574 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110000001110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1574", ") = {\n    SEE = ", "1574", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_addlong_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1574 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "110000001110", .any 10], 1574, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_addlong_decode"⟩
theorem checked1574 : check raw1574 clause1574 = true := by rfl
def row1574 : Row := ⟨1574, 3208641536, 774912000⟩
theorem derived1574 : clause1574.row = row1574 := by rfl
def entry1574 : CheckedRow := ⟨raw1574, clause1574, row1574, checked1574, derived1574⟩

def raw1575 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111011111001111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1575", ") = {\n    SEE = ", "1575", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_special_sqrtfp16_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1575 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111011111001111110", .any 10], 1575, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_special_sqrtfp16_decode"⟩
theorem checked1575 : check raw1575 clause1575 = true := by rfl
def row1575 : Row := ⟨1575, 3221224448, 788133888⟩
theorem derived1575 : clause1575.row = row1575 := by rfl
def entry1575 : CheckedRow := ⟨raw1575, clause1575, row1575, checked1575, derived1575⟩

def raw1576 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000001010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1576", ") = {\n    SEE = ", "1576", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_add_pairwise_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1576 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100000001010", .any 10], 1576, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_add_pairwise_decode"⟩
theorem checked1576 : check raw1576 clause1576 = true := by rfl
def row1576 : Row := ⟨1576, 3208641536, 773859328⟩
theorem derived1576 : clause1576.row = row1576 := by rfl
def entry1576 : CheckedRow := ⟨raw1576, clause1576, row1576, checked1576, derived1576⟩

def raw1577 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1577", ") = {\n    SEE = ", "1577", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_conv_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1577 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "111001", .any 10], 1577, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_conv_int_simd_decode"⟩
theorem checked1577 : check raw1577 clause1577 = true := by rfl
def row1577 : Row := ⟨1577, 3212901376, 251716608⟩
theorem derived1577 : clause1577.row = row1577 := by rfl
def entry1577 : CheckedRow := ⟨raw1577, clause1577, row1577, checked1577, derived1577⟩

def entries68 : List CheckedRow := [entry1570, entry1571, entry1572, entry1573, entry1574, entry1575, entry1576, entry1577]
def rows68 : List Row := [row1570, row1571, row1572, row1573, row1574, row1575, row1576, row1577]
theorem indices68 : rows68.map Row.index = [1570, 1571, 1572, 1573, 1574, 1575, 1576, 1577] := by rfl
theorem bound68 : entries68.map CheckedRow.row = rows68 := by rfl
theorem choices_and_68 : choices rows68 167837696#32 (-1) = [] := by rfl
theorem choices_orr_68 : choices rows68 704708608#32 (-1) = [] := by rfl
theorem choices_eor_68 : choices rows68 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_68 : choices rows68 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
