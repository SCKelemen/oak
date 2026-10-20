import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1626 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1626", ") = {\n    SEE = ", "1626", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_mul_product_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1626 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "100010", .any 10], 1626, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_mul_product_decode"⟩
theorem checked1626 : check raw1626 clause1626 = true := by rfl
def row1626 : Row := ⟨1626, 4280351744, 505448448⟩
theorem derived1626 : clause1626.row = row1626 := by rfl
def entry1626 : CheckedRow := ⟨raw1626, clause1626, row1626, checked1626, derived1626⟩

def raw1627 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000001110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1627", ") = {\n    SEE = ", "1627", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_add_saturating_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1627 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000001110", .any 10], 1627, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_add_saturating_simd_decode"⟩
theorem checked1627 : check raw1627 clause1627 = true := by rfl
def row1627 : Row := ⟨1627, 3208641536, 236992512⟩
theorem derived1627 : clause1627.row = row1627 := by rfl
def entry1627 : CheckedRow := ⟨raw1627, clause1627, row1627, checked1627, derived1627⟩

def raw1628 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "0011", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1628", ") = {\n    SEE = ", "1628", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_double_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1628 : Clause := ⟨[.fixed "0", .any 1, .fixed "001111", .any 8, .fixed "0011", .any 1, .fixed "0", .any 10], 1628, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_double_simd_decode"⟩
theorem checked1628 : check raw1628 clause1628 = true := by rfl
def row1628 : Row := ⟨1628, 3204510720, 251670528⟩
theorem derived1628 : clause1628.row = row1628 := by rfl
def entry1628 : CheckedRow := ⟨raw1628, clause1628, row1628, checked1628, derived1628⟩

def raw1629 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1629", ") = {\n    SEE = ", "1629", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_poly_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1629 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "111000", .any 10], 1629, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_mul_poly_decode"⟩
theorem checked1629 : check raw1629 clause1629 = true := by rfl
def row1629 : Row := ⟨1629, 3206609920, 237035520⟩
theorem derived1629 : clause1629.row = row1629 := by rfl
def entry1629 : CheckedRow := ⟨raw1629, clause1629, row1629, checked1629, derived1629⟩

def raw1630 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100111010000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1630", ") = {\n    SEE = ", "1630", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "rmode", " : bits(", "3", ") = ", "op_code[", "17", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_round_frint_decode", "(", "Rd", ", ", "Rn", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1630 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100111010000", .any 10], 1630, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"rmode", 3, 17, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_round_frint_decode"⟩
theorem checked1630 : check raw1630 clause1630 = true := by rfl
def row1630 : Row := ⟨1630, 4282383360, 505888768⟩
theorem derived1630 : clause1630.row = row1630 := by rfl
def entry1630 : CheckedRow := ⟨raw1630, clause1630, row1630, checked1630, derived1630⟩

def raw1631 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00110000000000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1631", ") = {\n    SEE = ", "1631", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1631 : Clause := ⟨[.fixed "0", .any 1, .fixed "00110000000000", .any 2, .fixed "1", .any 13], 1631, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode"⟩
theorem checked1631 : check raw1631 clause1631 = true := by rfl
def row1631 : Row := ⟨1631, 3221168128, 201334784⟩
theorem derived1631 : clause1631.row = row1631 := by rfl
def entry1631 : CheckedRow := ⟨raw1631, clause1631, row1631, checked1631, derived1631⟩

def raw1632 : List String := ["function clause decode64 ((", "0b", "11111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "10", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1632", ") = {\n    SEE = ", "1632", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "W", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_pac_decode", "(", "Rt", ", ", "Rn", ", ", "W", ", ", "imm9", ", ", "S", ", ", "M", ", ", "V", ", ", "size", ")\n}\n"]
def clause1632 : Clause := ⟨[.fixed "11111000", .any 2, .fixed "1", .any 10, .fixed "1", .any 10], 1632, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"W", 1, 11, 11, true⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"S", 1, 22, 22, true⟩, ⟨"M", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_pac_decode"⟩
theorem checked1632 : check raw1632 clause1632 = true := by rfl
def row1632 : Row := ⟨1632, 4280288256, 4162847744⟩
theorem derived1632 : clause1632.row = row1632 := by rfl
def entry1632 : CheckedRow := ⟨raw1632, clause1632, row1632, checked1632, derived1632⟩

def raw1633 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100100", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1633", ") = {\n    SEE = ", "1633", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "Rm", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1633 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100100", .any 7, .fixed "1", .any 13], 1633, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode"⟩
theorem checked1633 : check raw1633 clause1633 = true := by rfl
def row1633 : Row := ⟨1633, 3219136512, 209723392⟩
theorem derived1633 : clause1633.row = row1633 := by rfl
def entry1633 : CheckedRow := ⟨raw1633, clause1633, row1633, checked1633, derived1633⟩

def entries75 : List CheckedRow := [entry1626, entry1627, entry1628, entry1629, entry1630, entry1631, entry1632, entry1633]
def rows75 : List Row := [row1626, row1627, row1628, row1629, row1630, row1631, row1632, row1633]
theorem indices75 : rows75.map Row.index = [1626, 1627, 1628, 1629, 1630, 1631, 1632, 1633] := by rfl
theorem bound75 : entries75.map CheckedRow.row = rows75 := by rfl
theorem choices_and_75 : choices rows75 167837696#32 (-1) = [] := by rfl
theorem choices_orr_75 : choices rows75 704708608#32 (-1) = [] := by rfl
theorem choices_eor_75 : choices rows75 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_75 : choices rows75 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
