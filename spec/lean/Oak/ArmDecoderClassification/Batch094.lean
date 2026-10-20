import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1778 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1778", ") = {\n    SEE = ", "1778", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "E", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1778 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110010", .any 5, .fixed "001001", .any 10], 1778, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_fp16_simd_decode"⟩
theorem checked1778 : check raw1778 clause1778 = true := by rfl
def row1778 : Row := ⟨1778, 3219192832, 775955456⟩
theorem derived1778 : clause1778.row = row1778 := by rfl
def entry1778 : CheckedRow := ⟨raw1778, clause1778, row1778, checked1778, derived1778⟩

def raw1779 : List String := ["function clause decode64 ((", "0b", "0101111000110000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1779", ") = {\n    SEE = ", "1779", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fp16maxnm_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ")\n}\n"]
def clause1779 : Clause := ⟨[.fixed "0101111000110000110010", .any 10], 1779, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fp16maxnm_sisd_decode"⟩
theorem checked1779 : check raw1779 clause1779 = true := by rfl
def row1779 : Row := ⟨1779, 4294966272, 1580255232⟩
theorem derived1779 : clause1779.row = row1779 := by rfl
def entry1779 : CheckedRow := ⟨raw1779, clause1779, row1779, checked1779, derived1779⟩

def raw1780 : List String := ["function clause decode64 ((", "0b", "110110101100000101000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "11111", " @ ", "_ : bits(", "5", ")", " as op_code) if SEE < ", "1780", ") = {\n    SEE = ", "1780", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "D", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_strip_dp_1src_decode", "(", "Rd", ", ", "Rn", ", ", "D", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1780 : Clause := ⟨[.fixed "110110101100000101000", .any 1, .fixed "11111", .any 5], 1780, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"D", 1, 10, 10, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_strip_dp_1src_decode"⟩
theorem checked1780 : check raw1780 clause1780 = true := by rfl
def row1780 : Row := ⟨1780, 4294966240, 3670098912⟩
theorem derived1780 : clause1780.row = row1780 := by rfl
def entry1780 : CheckedRow := ⟨raw1780, clause1780, row1780, checked1780, derived1780⟩

def raw1781 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1781", ") = {\n    SEE = ", "1781", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_simdfp_immediate_signed_preidx_memory_single_simdfp_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1781 : Clause := ⟨[.any 2, .fixed "111100", .any 1, .fixed "00", .any 9, .fixed "11", .any 10], 1781, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_simdfp_immediate_signed_preidx_memory_single_simdfp_immediate_signed_postidx__decode"⟩
theorem checked1781 : check raw1781 clause1781 = true := by rfl
def row1781 : Row := ⟨1781, 1063259136, 1006636032⟩
theorem derived1781 : clause1781.row = row1781 := by rfl
def entry1781 : CheckedRow := ⟨raw1781, clause1781, row1781, checked1781, derived1781⟩

def raw1782 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1782", ") = {\n    SEE = ", "1782", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1782 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "100001110110", .any 10], 1782, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_int_simd_decode"⟩
theorem checked1782 : check raw1782 clause1782 = true := by rfl
def row1782 : Row := ⟨1782, 3217030144, 237099008⟩
theorem derived1782 : clause1782.row = row1782 := by rfl
def entry1782 : CheckedRow := ⟨raw1782, clause1782, row1782, checked1782, derived1782⟩

def raw1783 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1783", ") = {\n    SEE = ", "1783", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1783 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "100001110110", .any 10], 1783, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_int_simd_decode"⟩
theorem checked1783 : check raw1783 clause1783 = true := by rfl
def row1783 : Row := ⟨1783, 3217030144, 773969920⟩
theorem derived1783 : clause1783.row = row1783 := by rfl
def entry1783 : CheckedRow := ⟨raw1783, clause1783, row1783, checked1783, derived1783⟩

def raw1784 : List String := ["function clause decode64 ((", "0b", "110110101100000100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1784", ") = {\n    SEE = ", "1784", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_pacdb_dp_1src_decode", "(", "Rd", ", ", "Rn", ", ", "Z", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1784 : Clause := ⟨[.fixed "110110101100000100", .any 1, .fixed "011", .any 10], 1784, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Z", 1, 13, 13, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_pacdb_dp_1src_decode"⟩
theorem checked1784 : check raw1784 clause1784 = true := by rfl
def row1784 : Row := ⟨1784, 4294958080, 3670084608⟩
theorem derived1784 : clause1784.row = row1784 := by rfl
def entry1784 : CheckedRow := ⟨raw1784, clause1784, row1784, checked1784, derived1784⟩

def raw1785 : List String := ["function clause decode64 ((", "0b", "00011001100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1785", ") = {\n    SEE = ", "1785", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagandzerodatapost_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1785 : Clause := ⟨[.fixed "00011001100", .any 9, .fixed "01", .any 10], 1785, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagandzerodatapost_decode"⟩
theorem checked1785 : check raw1785 clause1785 = true := by rfl
def row1785 : Row := ⟨1785, 4292873216, 427820032⟩
theorem derived1785 : clause1785.row = row1785 := by rfl
def entry1785 : CheckedRow := ⟨raw1785, clause1785, row1785, checked1785, derived1785⟩

def entries94 : List CheckedRow := [entry1778, entry1779, entry1780, entry1781, entry1782, entry1783, entry1784, entry1785]
def rows94 : List Row := [row1778, row1779, row1780, row1781, row1782, row1783, row1784, row1785]
theorem indices94 : rows94.map Row.index = [1778, 1779, 1780, 1781, 1782, 1783, 1784, 1785] := by rfl
theorem bound94 : entries94.map CheckedRow.row = rows94 := by rfl
theorem choices_and_94 : choices rows94 167837696#32 (-1) = [] := by rfl
theorem choices_orr_94 : choices rows94 704708608#32 (-1) = [] := by rfl
theorem choices_eor_94 : choices rows94 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_94 : choices rows94 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
