import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1682 : List String := ["function clause decode64 ((", "0b", "011111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110000110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1682", ") = {\n    SEE = ", "1682", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fpadd_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1682 : Clause := ⟨[.fixed "011111100", .any 1, .fixed "110000110110", .any 10], 1682, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fpadd_sisd_decode"⟩
theorem checked1682 : check raw1682 clause1682 = true := by rfl
def row1682 : Row := ⟨1682, 4290771968, 2117130240⟩
theorem derived1682 : clause1682.row = row1682 := by rfl
def entry1682 : CheckedRow := ⟨raw1682, clause1682, row1682, checked1682, derived1682⟩

def raw1683 : List String := ["function clause decode64 ((", "0b", "00111000010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1683", ") = {\n    SEE = ", "1683", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1683 : Clause := ⟨[.fixed "00111000010", .any 9, .fixed "11", .any 10], 1683, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1683 : check raw1683 clause1683 = true := by rfl
def row1683 : Row := ⟨1683, 4292873216, 943721472⟩
theorem derived1683 : clause1683.row = row1683 := by rfl
def entry1683 : CheckedRow := ⟨raw1683, clause1683, row1683, checked1683, derived1683⟩

def raw1684 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1684", ") = {\n    SEE = ", "1684", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_single_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1684 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "011011", .any 10], 1684, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_single_decode"⟩
theorem checked1684 : check raw1684 clause1684 = true := by rfl
def row1684 : Row := ⟨1684, 3206609920, 237005824⟩
theorem derived1684 : clause1684.row = row1684 := by rfl
def entry1684 : CheckedRow := ⟨raw1684, clause1684, row1684, checked1684, derived1684⟩

def raw1685 : List String := ["function clause decode64 ((", "0b", "10011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1685", ") = {\n    SEE = ", "1685", ";\n", "    ", "Xd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Xm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "integer_tags_mcinsertrandomtag_decode", "(", "Xd", ", ", "Xn", ", ", "Xm", ")\n}\n"]
def clause1685 : Clause := ⟨[.fixed "10011010110", .any 5, .fixed "000100", .any 10], 1685, [⟨"Xd", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"Xm", 5, 20, 16, false⟩], "integer_tags_mcinsertrandomtag_decode"⟩
theorem checked1685 : check raw1685 clause1685 = true := by rfl
def row1685 : Row := ⟨1685, 4292934656, 2596278272⟩
theorem derived1685 : clause1685.row = row1685 := by rfl
def entry1685 : CheckedRow := ⟨raw1685, clause1685, row1685, checked1685, derived1685⟩

def raw1686 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111001111001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1686", ") = {\n    SEE = ", "1686", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1686 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111001111001110110", .any 10], 1686, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_conv_int_simd_decode"⟩
theorem checked1686 : check raw1686 clause1686 = true := by rfl
def row1686 : Row := ⟨1686, 3221224448, 242866176⟩
theorem derived1686 : clause1686.row = row1686 := by rfl
def entry1686 : CheckedRow := ⟨raw1686, clause1686, row1686, checked1686, derived1686⟩

def raw1687 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0001011", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1687", ") = {\n    SEE = ", "1687", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "shift", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1687 : Clause := ⟨[.any 1, .fixed "0001011", .any 2, .fixed "0", .any 21], 1687, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_shiftedreg_decode"⟩
theorem checked1687 : check raw1687 clause1687 = true := by rfl
def row1687 : Row := ⟨1687, 2132803584, 184549376⟩
theorem derived1687 : clause1687.row = row1687 := by rfl
def entry1687 : CheckedRow := ⟨raw1687, clause1687, row1687, checked1687, derived1687⟩

def raw1688 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1688", ") = {\n    SEE = ", "1688", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "13", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_maxmin_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1688 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "011010", .any 10], 1688, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 2, 13, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_maxmin_decode"⟩
theorem checked1688 : check raw1688 clause1688 = true := by rfl
def row1688 : Row := ⟨1688, 4280351744, 505440256⟩
theorem derived1688 : clause1688.row = row1688 := by rfl
def entry1688 : CheckedRow := ⟨raw1688, clause1688, row1688, checked1688, derived1688⟩

def raw1689 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1011010100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1689", ") = {\n    SEE = ", "1689", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_conditional_select_decode", "(", "Rd", ", ", "Rn", ", ", "o2", ", ", "cond", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1689 : Clause := ⟨[.any 1, .fixed "1011010100", .any 9, .fixed "01", .any 10], 1689, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o2", 1, 10, 10, true⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_conditional_select_decode"⟩
theorem checked1689 : check raw1689 clause1689 = true := by rfl
def row1689 : Row := ⟨1689, 2145389568, 1518339072⟩
theorem derived1689 : clause1689.row = row1689 := by rfl
def entry1689 : CheckedRow := ⟨raw1689, clause1689, row1689, checked1689, derived1689⟩

def entries82 : List CheckedRow := [entry1682, entry1683, entry1684, entry1685, entry1686, entry1687, entry1688, entry1689]
def rows82 : List Row := [row1682, row1683, row1684, row1685, row1686, row1687, row1688, row1689]
theorem indices82 : rows82.map Row.index = [1682, 1683, 1684, 1685, 1686, 1687, 1688, 1689] := by rfl
theorem bound82 : entries82.map CheckedRow.row = rows82 := by rfl
theorem choices_and_82 : choices rows82 167837696#32 (-1) = [] := by rfl
theorem choices_orr_82 : choices rows82 704708608#32 (-1) = [] := by rfl
theorem choices_eor_82 : choices rows82 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_82 : choices rows82 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
