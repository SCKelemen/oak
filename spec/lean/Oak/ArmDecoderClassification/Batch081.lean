import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1674 : List String := ["function clause decode64 ((", "0b", "0011100101", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1674", ") = {\n    SEE = ", "1674", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1674 : Clause := ⟨[.fixed "0011100101", .any 22], 1674, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1674 : check raw1674 clause1674 = true := by rfl
def row1674 : Row := ⟨1674, 4290772992, 960495616⟩
theorem derived1674 : clause1674.row = row1674 := by rfl
def entry1674 : CheckedRow := ⟨raw1674, clause1674, row1674, checked1674, derived1674⟩

def raw1675 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "0100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1675", ") = {\n    SEE = ", "1675", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_int_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1675 : Clause := ⟨[.fixed "0", .any 1, .fixed "101111", .any 8, .fixed "0100", .any 1, .fixed "0", .any 10], 1675, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_int_decode"⟩
theorem checked1675 : check raw1675 clause1675 = true := by rfl
def row1675 : Row := ⟨1675, 3204510720, 788545536⟩
theorem derived1675 : clause1675.row = row1675 := by rfl
def entry1675 : CheckedRow := ⟨raw1675, clause1675, row1675, checked1675, derived1675⟩

def raw1676 : List String := ["function clause decode64 ((", "0b", "0111111001111001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1676", ") = {\n    SEE = ", "1676", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size_1_", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size_1_", ", ", "U", ")\n}\n"]
def clause1676 : Clause := ⟨[.fixed "0111111001111001110010", .any 10], 1676, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size_1_", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode"⟩
theorem checked1676 : check raw1676 clause1676 = true := by rfl
def row1676 : Row := ⟨1676, 4294966272, 2121910272⟩
theorem derived1676 : clause1676.row = row1676 := by rfl
def entry1676 : CheckedRow := ⟨raw1676, clause1676, row1676, checked1676, derived1676⟩

def raw1677 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001000011", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1677", ") = {\n    SEE = ", "1677", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_exclusive_pair_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "sz", ")\n}\n"]
def clause1677 : Clause := ⟨[.fixed "1", .any 1, .fixed "001000011", .any 5, .fixed "1", .any 15], 1677, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"sz", 1, 30, 30, true⟩], "memory_exclusive_pair_decode"⟩
theorem checked1677 : check raw1677 clause1677 = true := by rfl
def row1677 : Row := ⟨1677, 3219161088, 2288025600⟩
theorem derived1677 : clause1677.row = row1677 := by rfl
def entry1677 : CheckedRow := ⟨raw1677, clause1677, row1677, checked1677, derived1677⟩

def raw1678 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101111", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1678", ") = {\n    SEE = ", "1678", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1678 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101111", .any 7, .fixed "1", .any 13], 1678, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1678 : check raw1678 clause1678 = true := by rfl
def row1678 : Row := ⟨1678, 3219136512, 232792064⟩
theorem derived1678 : clause1678.row = row1678 := by rfl
def entry1678 : CheckedRow := ⟨raw1678, clause1678, row1678, checked1678, derived1678⟩

def raw1679 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00110100100000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1679", ") = {\n    SEE = ", "1679", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1679 : Clause := ⟨[.fixed "0", .any 1, .fixed "00110100100000", .any 2, .fixed "1", .any 13], 1679, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1679 : check raw1679 clause1679 = true := by rfl
def row1679 : Row := ⟨1679, 3221168128, 220209152⟩
theorem derived1679 : clause1679.row = row1679 := by rfl
def entry1679 : CheckedRow := ⟨raw1679, clause1679, row1679, checked1679, derived1679⟩

def raw1680 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1680", ") = {\n    SEE = ", "1680", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1680 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110010", .any 5, .fixed "001101", .any 10], 1680, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode"⟩
theorem checked1680 : check raw1680 clause1680 = true := by rfl
def row1680 : Row := ⟨1680, 3219192832, 239088640⟩
theorem derived1680 : clause1680.row = row1680 := by rfl
def entry1680 : CheckedRow := ⟨raw1680, clause1680, row1680, checked1680, derived1680⟩

def raw1681 : List String := ["function clause decode64 ((", "0b", "11010101000000000100000000011111", " as op_code) if SEE < ", "1681", ") = {\n    SEE = ", "1681", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "integer_flags_cfinv_decode", "(", "CRm", ")\n}\n"]
def clause1681 : Clause := ⟨[.fixed "11010101000000000100000000011111"], 1681, [⟨"CRm", 4, 11, 8, false⟩], "integer_flags_cfinv_decode"⟩
theorem checked1681 : check raw1681 clause1681 = true := by rfl
def row1681 : Row := ⟨1681, 4294967295, 3573563423⟩
theorem derived1681 : clause1681.row = row1681 := by rfl
def entry1681 : CheckedRow := ⟨raw1681, clause1681, row1681, checked1681, derived1681⟩

def entries81 : List CheckedRow := [entry1674, entry1675, entry1676, entry1677, entry1678, entry1679, entry1680, entry1681]
def rows81 : List Row := [row1674, row1675, row1676, row1677, row1678, row1679, row1680, row1681]
theorem indices81 : rows81.map Row.index = [1674, 1675, 1676, 1677, 1678, 1679, 1680, 1681] := by rfl
theorem bound81 : entries81.map CheckedRow.row = rows81 := by rfl
theorem choices_and_81 : choices rows81 167837696#32 (-1) = [] := by rfl
theorem choices_orr_81 : choices rows81 704708608#32 (-1) = [] := by rfl
theorem choices_eor_81 : choices rows81 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_81 : choices rows81 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
