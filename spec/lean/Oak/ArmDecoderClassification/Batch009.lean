import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1098 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1098", ") = {\n    SEE = ", "1098", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ")\n}\n"]
def clause1098 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "1", .any 5, .fixed "111001", .any 10], 1098, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode"⟩
theorem checked1098 : check raw1098 clause1098 = true := by rfl
def row1098 : Row := ⟨1098, 4288740352, 2124473344⟩
theorem derived1098 : clause1098.row = row1098 := by rfl
def entry1098 : CheckedRow := ⟨raw1098, clause1098, row1098, checked1098, derived1098⟩

def raw1099 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1099", ") = {\n    SEE = ", "1099", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1099 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "100001101010", .any 10], 1099, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_simd_decode"⟩
theorem checked1099 : check raw1099 clause1099 = true := by rfl
def row1099 : Row := ⟨1099, 3217030144, 237086720⟩
theorem derived1099 : clause1099.row = row1099 := by rfl
def entry1099 : CheckedRow := ⟨raw1099, clause1099, row1099, checked1099, derived1099⟩

def raw1100 : List String := ["function clause decode64 ((", "0b", "0111111011111001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1100", ") = {\n    SEE = ", "1100", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1100 : Clause := ⟨[.fixed "0111111011111001101010", .any 10], 1100, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode"⟩
theorem checked1100 : check raw1100 clause1100 = true := by rfl
def row1100 : Row := ⟨1100, 4294966272, 2130290688⟩
theorem derived1100 : clause1100.row = row1100 := by rfl
def entry1100 : CheckedRow := ⟨raw1100, clause1100, row1100, checked1100, derived1100⟩

def raw1101 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1101", ") = {\n    SEE = ", "1101", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "16", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_unary_decode", "(", "Rd", ", ", "Rn", ", ", "opc", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1101 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100000110000", .any 10], 1101, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 2, 16, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_unary_decode"⟩
theorem checked1101 : check raw1101 clause1101 = true := by rfl
def row1101 : Row := ⟨1101, 4282383360, 505462784⟩
theorem derived1101 : clause1101.row = row1101 := by rfl
def entry1101 : CheckedRow := ⟨raw1101, clause1101, row1101, checked1101, derived1101⟩

def raw1102 : List String := ["function clause decode64 ((", "0b", "01111111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1102", ") = {\n    SEE = ", "1102", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_high_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "S", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1102 : Clause := ⟨[.fixed "01111111", .any 8, .fixed "1101", .any 1, .fixed "0", .any 10], 1102, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"S", 1, 13, 13, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mulacc_high_sisd_decode"⟩
theorem checked1102 : check raw1102 clause1102 = true := by rfl
def row1102 : Row := ⟨1102, 4278252544, 2130759680⟩
theorem derived1102 : clause1102.row = row1102 := by rfl
def entry1102 : CheckedRow := ⟨raw1102, clause1102, row1102, checked1102, derived1102⟩

def raw1103 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000011010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1103", ") = {\n    SEE = ", "1103", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_add_pairwise_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1103 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000011010", .any 10], 1103, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_add_pairwise_decode"⟩
theorem checked1103 : check raw1103 clause1103 = true := by rfl
def row1103 : Row := ⟨1103, 3208641536, 237004800⟩
theorem derived1103 : clause1103.row = row1103 := by rfl
def entry1103 : CheckedRow := ⟨raw1103, clause1103, row1103, checked1103, derived1103⟩

def raw1104 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1104", ") = {\n    SEE = ", "1104", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "16", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_unary_decode", "(", "Rd", ", ", "Rn", ", ", "opc", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1104 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100001110000", .any 10], 1104, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 2, 16, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_unary_decode"⟩
theorem checked1104 : check raw1104 clause1104 = true := by rfl
def row1104 : Row := ⟨1104, 4282383360, 505528320⟩
theorem derived1104 : clause1104.row = row1104 := by rfl
def entry1104 : CheckedRow := ⟨raw1104, clause1104, row1104, checked1104, derived1104⟩

def raw1105 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1105", ") = {\n    SEE = ", "1105", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "rot", " : bits(", "2", ") = ", "op_code[", "12", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp_complex_decode", "(", "Rd", ", ", "Rn", ", ", "rot", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1105 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "0", .any 5, .fixed "110", .any 2, .fixed "1", .any 10], 1105, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"rot", 2, 12, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp_complex_decode"⟩
theorem checked1105 : check raw1105 clause1105 = true := by rfl
def row1105 : Row := ⟨1105, 3206603776, 771802112⟩
theorem derived1105 : clause1105.row = row1105 := by rfl
def entry1105 : CheckedRow := ⟨raw1105, clause1105, row1105, checked1105, derived1105⟩

def entries9 : List CheckedRow := [entry1098, entry1099, entry1100, entry1101, entry1102, entry1103, entry1104, entry1105]
def rows9 : List Row := [row1098, row1099, row1100, row1101, row1102, row1103, row1104, row1105]
theorem indices9 : rows9.map Row.index = [1098, 1099, 1100, 1101, 1102, 1103, 1104, 1105] := by rfl
theorem bound9 : entries9.map CheckedRow.row = rows9 := by rfl
theorem choices_and_9 : choices rows9 167837696#32 (-1) = [] := by rfl
theorem choices_orr_9 : choices rows9 704708608#32 (-1) = [] := by rfl
theorem choices_eor_9 : choices rows9 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_9 : choices rows9 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
