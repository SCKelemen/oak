import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1106 : List String := ["function clause decode64 ((", "0b", "11010101000000110010000000011111", " as op_code) if SEE < ", "1106", ") = {\n    SEE = ", "1106", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_hints_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1106 : Clause := ⟨[.fixed "11010101000000110010000000011111"], 1106, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_hints_decode"⟩
theorem checked1106 : check raw1106 clause1106 = true := by rfl
def row1106 : Row := ⟨1106, 4294967295, 3573751839⟩
theorem derived1106 : clause1106.row = row1106 := by rfl
def entry1106 : CheckedRow := ⟨raw1106, clause1106, row1106, checked1106, derived1106⟩

def raw1107 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111000110000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1107", ") = {\n    SEE = ", "1107", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_fp16maxnm_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1107 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111000110000110010", .any 10], 1107, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_fp16maxnm_simd_decode"⟩
theorem checked1107 : check raw1107 clause1107 = true := by rfl
def row1107 : Row := ⟨1107, 3221224448, 238077952⟩
theorem derived1107 : clause1107.row = row1107 := by rfl
def entry1107 : CheckedRow := ⟨raw1107, clause1107, row1107, checked1107, derived1107⟩

def raw1108 : List String := ["function clause decode64 ((", "0b", "0101111001111001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1108", ") = {\n    SEE = ", "1108", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size_1_", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size_1_", ", ", "U", ")\n}\n"]
def clause1108 : Clause := ⟨[.fixed "0101111001111001110010", .any 10], 1108, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size_1_", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_float_tieaway_sisd_decode"⟩
theorem checked1108 : check raw1108 clause1108 = true := by rfl
def row1108 : Row := ⟨1108, 4294966272, 1585039360⟩
theorem derived1108 : clause1108.row = row1108 := by rfl
def entry1108 : CheckedRow := ⟨raw1108, clause1108, row1108, checked1108, derived1108⟩

def raw1109 : List String := ["function clause decode64 ((", "0b", "00011001001", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1109", ") = {\n    SEE = ", "1109", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagpairpre_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1109 : Clause := ⟨[.fixed "00011001001", .any 9, .fixed "11", .any 10], 1109, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagpairpre_decode"⟩
theorem checked1109 : check raw1109 clause1109 = true := by rfl
def row1109 : Row := ⟨1109, 4292873216, 421530624⟩
theorem derived1109 : clause1109.row = row1109 := by rfl
def entry1109 : CheckedRow := ⟨raw1109, clause1109, row1109, checked1109, derived1109⟩

def raw1110 : List String := ["function clause decode64 ((", "0b", "00001000000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1110", ") = {\n    SEE = ", "1110", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1110 : Clause := ⟨[.fixed "00001000000", .any 5, .fixed "0", .any 15], 1110, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1110 : check raw1110 clause1110 = true := by rfl
def row1110 : Row := ⟨1110, 4292902912, 134217728⟩
theorem derived1110 : clause1110.row = row1110 := by rfl
def entry1110 : CheckedRow := ⟨raw1110, clause1110, row1110, checked1110, derived1110⟩

def raw1111 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000100110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1111", ") = {\n    SEE = ", "1111", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1111 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000100110", .any 10], 1111, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_int_bulk_simd_decode"⟩
theorem checked1111 : check raw1111 clause1111 = true := by rfl
def row1111 : Row := ⟨1111, 3208641536, 237017088⟩
theorem derived1111 : clause1111.row = row1111 := by rfl
def entry1111 : CheckedRow := ⟨raw1111, clause1111, row1111, checked1111, derived1111⟩

def raw1112 : List String := ["function clause decode64 ((", "0b", "00011001101", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1112", ") = {\n    SEE = ", "1112", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagpairandzerodatapost_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1112 : Clause := ⟨[.fixed "00011001101", .any 9, .fixed "01", .any 10], 1112, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagpairandzerodatapost_decode"⟩
theorem checked1112 : check raw1112 clause1112 = true := by rfl
def row1112 : Row := ⟨1112, 4292873216, 429917184⟩
theorem derived1112 : clause1112.row = row1112 := by rfl
def entry1112 : CheckedRow := ⟨raw1112, clause1112, row1112, checked1112, derived1112⟩

def raw1113 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001001010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1113", ") = {\n    SEE = ", "1113", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_extract_sqxtun_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1113 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "100001001010", .any 10], 1113, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_extract_sqxtun_sisd_decode"⟩
theorem checked1113 : check raw1113 clause1113 = true := by rfl
def row1113 : Row := ⟨1113, 4282383360, 2116102144⟩
theorem derived1113 : clause1113.row = row1113 := by rfl
def entry1113 : CheckedRow := ⟨raw1113, clause1113, row1113, checked1113, derived1113⟩

def entries10 : List CheckedRow := [entry1106, entry1107, entry1108, entry1109, entry1110, entry1111, entry1112, entry1113]
def rows10 : List Row := [row1106, row1107, row1108, row1109, row1110, row1111, row1112, row1113]
theorem indices10 : rows10.map Row.index = [1106, 1107, 1108, 1109, 1110, 1111, 1112, 1113] := by rfl
theorem bound10 : entries10.map CheckedRow.row = rows10 := by rfl
theorem choices_and_10 : choices rows10 167837696#32 (-1) = [] := by rfl
theorem choices_orr_10 : choices rows10 704708608#32 (-1) = [] := by rfl
theorem choices_eor_10 : choices rows10 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_10 : choices rows10 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
