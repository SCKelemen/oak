import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1738 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1738", ") = {\n    SEE = ", "1738", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode_0_", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode_1_", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode_2_", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "opcode_3_", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_product_decode", "(", "Rd", ", ", "Rn", ", ", "opcode_0_", ", ", "opcode_1_", ", ", "opcode_2_", ", ", "opcode_3_", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1738 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "110000", .any 10], 1738, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode_0_", 1, 12, 12, true⟩, ⟨"opcode_1_", 1, 13, 13, true⟩, ⟨"opcode_2_", 1, 14, 14, true⟩, ⟨"opcode_3_", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_mul_product_decode"⟩
theorem checked1738 : check raw1738 clause1738 = true := by rfl
def row1738 : Row := ⟨1738, 3206609920, 237027328⟩
theorem derived1738 : clause1738.row = row1738 := by rfl
def entry1738 : CheckedRow := ⟨raw1738, clause1738, row1738, checked1738, derived1738⟩

def raw1739 : List String := ["function clause decode64 ((", "0b", "010111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1739", ") = {\n    SEE = ", "1739", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1739 : Clause := ⟨[.fixed "010111100", .any 1, .fixed "100001101010", .any 10], 1739, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode"⟩
theorem checked1739 : check raw1739 clause1739 = true := by rfl
def row1739 : Row := ⟨1739, 4290771968, 1579264000⟩
theorem derived1739 : clause1739.row = row1739 := by rfl
def entry1739 : CheckedRow := ⟨raw1739, clause1739, row1739, checked1739, derived1739⟩

def raw1740 : List String := ["function clause decode64 ((", "0b", "0101111000110000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1740", ") = {\n    SEE = ", "1740", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fp16max_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ")\n}\n"]
def clause1740 : Clause := ⟨[.fixed "0101111000110000111110", .any 10], 1740, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fp16max_sisd_decode"⟩
theorem checked1740 : check raw1740 clause1740 = true := by rfl
def row1740 : Row := ⟨1740, 4294966272, 1580267520⟩
theorem derived1740 : clause1740.row = row1740 := by rfl
def entry1740 : CheckedRow := ⟨raw1740, clause1740, row1740, checked1740, derived1740⟩

def raw1741 : List String := ["function clause decode64 ((", "0b", "011111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1741", ") = {\n    SEE = ", "1741", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ")\n}\n"]
def clause1741 : Clause := ⟨[.fixed "011111100", .any 1, .fixed "1", .any 5, .fixed "111011", .any 10], 1741, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode"⟩
theorem checked1741 : check raw1741 clause1741 = true := by rfl
def row1741 : Row := ⟨1741, 4288740352, 2116086784⟩
theorem derived1741 : clause1741.row = row1741 := by rfl
def entry1741 : CheckedRow := ⟨raw1741, clause1741, row1741, checked1741, derived1741⟩

def raw1742 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000010000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1742", ") = {\n    SEE = ", "1742", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "16", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_unary_decode", "(", "Rd", ", ", "Rn", ", ", "opc", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1742 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100000010000", .any 10], 1742, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 2, 16, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_unary_decode"⟩
theorem checked1742 : check raw1742 clause1742 = true := by rfl
def row1742 : Row := ⟨1742, 4282383360, 505430016⟩
theorem derived1742 : clause1742.row = row1742 := by rfl
def entry1742 : CheckedRow := ⟨raw1742, clause1742, row1742, checked1742, derived1742⟩

def raw1743 : List String := ["function clause decode64 ((", "0b", "01011001100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1743", ") = {\n    SEE = ", "1743", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1743 : Clause := ⟨[.fixed "01011001100", .any 9, .fixed "00", .any 10], 1743, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1743 : check raw1743 clause1743 = true := by rfl
def row1743 : Row := ⟨1743, 4292873216, 1501560832⟩
theorem derived1743 : clause1743.row = row1743 := by rfl
def entry1743 : CheckedRow := ⟨raw1743, clause1743, row1743, checked1743, derived1743⟩

def raw1744 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0111010000000000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "01101", " as op_code) if SEE < ", "1744", ") = {\n    SEE = ", "1744", ";\n", "    ", "mask", " : bits(", "4", ") = ", "op_code[", "3", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode2", " : bits(", "4", ") = ", "op_code[", "13", " .. ", "10", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "20", " .. ", "15", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_flags_setf_decode", "(", "mask", ", ", "Rn", ", ", "opcode2", ", ", "sz", ", ", "imm6", ", ", "sf", ")\n}\n"]
def clause1744 : Clause := ⟨[.any 1, .fixed "0111010000000000", .any 1, .fixed "0010", .any 5, .fixed "01101"], 1744, [⟨"mask", 4, 3, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode2", 4, 13, 10, false⟩, ⟨"sz", 1, 14, 14, true⟩, ⟨"imm6", 6, 20, 15, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_flags_setf_decode"⟩
theorem checked1744 : check raw1744 clause1744 = true := by rfl
def row1744 : Row := ⟨1744, 2147466271, 973080589⟩
theorem derived1744 : clause1744.row = row1744 := by rfl
def entry1744 : CheckedRow := ⟨raw1744, clause1744, row1744, checked1744, derived1744⟩

def raw1745 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1745", ") = {\n    SEE = ", "1745", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm4_0_", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "imm4_1_", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "imm4_3_2_", " : bits(", "2", ") = ", "op_code[", "14", " .. ", "13", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_integer_move_signed_decode", "(", "Rd", ", ", "Rn", ", ", "imm4_0_", ", ", "imm4_1_", ", ", "imm4_3_2_", ", ", "imm5", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1745 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110000", .any 5, .fixed "001011", .any 10], 1745, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm4_0_", 1, 11, 11, true⟩, ⟨"imm4_1_", 1, 12, 12, true⟩, ⟨"imm4_3_2_", 2, 14, 13, false⟩, ⟨"imm5", 5, 20, 16, false⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_integer_move_signed_decode"⟩
theorem checked1745 : check raw1745 clause1745 = true := by rfl
def row1745 : Row := ⟨1745, 3219192832, 234892288⟩
theorem derived1745 : clause1745.row = row1745 := by rfl
def entry1745 : CheckedRow := ⟨raw1745, clause1745, row1745, checked1745, derived1745⟩

def entries89 : List CheckedRow := [entry1738, entry1739, entry1740, entry1741, entry1742, entry1743, entry1744, entry1745]
def rows89 : List Row := [row1738, row1739, row1740, row1741, row1742, row1743, row1744, row1745]
theorem indices89 : rows89.map Row.index = [1738, 1739, 1740, 1741, 1742, 1743, 1744, 1745] := by rfl
theorem bound89 : entries89.map CheckedRow.row = rows89 := by rfl
theorem choices_and_89 : choices rows89 167837696#32 (-1) = [] := by rfl
theorem choices_orr_89 : choices rows89 704708608#32 (-1) = [] := by rfl
theorem choices_eor_89 : choices rows89 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_89 : choices rows89 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
