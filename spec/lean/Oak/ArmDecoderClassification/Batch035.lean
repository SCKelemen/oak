import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1306 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1306", ") = {\n    SEE = ", "1306", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower_decode", "(", "Rd", ", ", "Rn", ", ", "Rm", ", ", "sz", ", ", "S", ", ", "Q", ")\n}\n"]
def clause1306 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "111011", .any 10], 1306, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"S", 1, 23, 23, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp_mul_norounding_lower_decode"⟩
theorem checked1306 : check raw1306 clause1306 = true := by rfl
def row1306 : Row := ⟨1306, 3206609920, 237038592⟩
theorem derived1306 : clause1306.row = row1306 := by rfl
def entry1306 : CheckedRow := ⟨raw1306, clause1306, row1306, checked1306, derived1306⟩

def raw1307 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011011000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1307", ") = {\n    SEE = ", "1307", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op31", " : bits(", "3", ") = ", "op_code[", "23", " .. ", "21", "]", ";\n", "    ", "op54", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_mul_uniform_addsub_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "op31", ", ", "op54", ", ", "sf", ")\n}\n"]
def clause1307 : Clause := ⟨[.any 1, .fixed "0011011000", .any 5, .fixed "0", .any 15], 1307, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"op31", 3, 23, 21, false⟩, ⟨"op54", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_mul_uniform_addsub_decode"⟩
theorem checked1307 : check raw1307 clause1307 = true := by rfl
def row1307 : Row := ⟨1307, 2145419264, 452984832⟩
theorem derived1307 : clause1307.row = row1307 := by rfl
def entry1307 : CheckedRow := ⟨raw1307, clause1307, row1307, checked1307, derived1307⟩

def raw1308 : List String := ["function clause decode64 ((", "0b", "00011001000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1308", ") = {\n    SEE = ", "1308", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1308 : Clause := ⟨[.fixed "00011001000", .any 9, .fixed "00", .any 10], 1308, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1308 : check raw1308 clause1308 = true := by rfl
def row1308 : Row := ⟨1308, 4292873216, 419430400⟩
theorem derived1308 : clause1308.row = row1308 := by rfl
def entry1308 : CheckedRow := ⟨raw1308, clause1308, row1308, checked1308, derived1308⟩

def raw1309 : List String := ["function clause decode64 ((", "0b", "00011001010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1309", ") = {\n    SEE = ", "1309", ";\n", "    ", "Xt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcgettag_decode", "(", "Xt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1309 : Clause := ⟨[.fixed "00011001010", .any 9, .fixed "10", .any 10], 1309, [⟨"Xt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcgettag_decode"⟩
theorem checked1309 : check raw1309 clause1309 = true := by rfl
def row1309 : Row := ⟨1309, 4292873216, 423626752⟩
theorem derived1309 : clause1309.row = row1309 := by rfl
def entry1309 : CheckedRow := ⟨raw1309, clause1309, row1309, checked1309, derived1309⟩

def raw1310 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000011010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1310", ") = {\n    SEE = ", "1310", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_add_pairwise_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1310 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100000011010", .any 10], 1310, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_add_pairwise_decode"⟩
theorem checked1310 : check raw1310 clause1310 = true := by rfl
def row1310 : Row := ⟨1310, 3208641536, 773875712⟩
theorem derived1310 : clause1310.row = row1310 := by rfl
def entry1310 : CheckedRow := ⟨raw1310, clause1310, row1310, checked1310, derived1310⟩

def raw1311 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100010000001000", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1311", ") = {\n    SEE = ", "1311", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1311 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100010000001000", .any 12], 1311, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode"⟩
theorem checked1311 : check raw1311 clause1311 = true := by rfl
def row1311 : Row := ⟨1311, 3221221376, 205553664⟩
theorem derived1311 : clause1311.row = row1311 := by rfl
def entry1311 : CheckedRow := ⟨raw1311, clause1311, row1311, checked1311, derived1311⟩

def raw1312 : List String := ["function clause decode64 ((", "0b", "01011111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "0111", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1312", ") = {\n    SEE = ", "1312", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_double_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1312 : Clause := ⟨[.fixed "01011111", .any 8, .fixed "0111", .any 1, .fixed "0", .any 10], 1312, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mulacc_double_sisd_decode"⟩
theorem checked1312 : check raw1312 clause1312 = true := by rfl
def row1312 : Row := ⟨1312, 4278252544, 1593864192⟩
theorem derived1312 : clause1312.row = row1312 := by rfl
def entry1312 : CheckedRow := ⟨raw1312, clause1312, row1312, checked1312, derived1312⟩

def raw1313 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1313", ") = {\n    SEE = ", "1313", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "rot", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_fp_complex_decode", "(", "Rd", ", ", "Rn", ", ", "rot", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1313 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "0", .any 5, .fixed "111", .any 1, .fixed "01", .any 10], 1313, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"rot", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_fp_complex_decode"⟩
theorem checked1313 : check raw1313 clause1313 = true := by rfl
def row1313 : Row := ⟨1313, 3206605824, 771810304⟩
theorem derived1313 : clause1313.row = row1313 := by rfl
def entry1313 : CheckedRow := ⟨raw1313, clause1313, row1313, checked1313, derived1313⟩

def entries35 : List CheckedRow := [entry1306, entry1307, entry1308, entry1309, entry1310, entry1311, entry1312, entry1313]
def rows35 : List Row := [row1306, row1307, row1308, row1309, row1310, row1311, row1312, row1313]
theorem indices35 : rows35.map Row.index = [1306, 1307, 1308, 1309, 1310, 1311, 1312, 1313] := by rfl
theorem bound35 : entries35.map CheckedRow.row = rows35 := by rfl
theorem choices_and_35 : choices rows35 167837696#32 (-1) = [] := by rfl
theorem choices_orr_35 : choices rows35 704708608#32 (-1) = [] := by rfl
theorem choices_eor_35 : choices rows35 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_35 : choices rows35 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
