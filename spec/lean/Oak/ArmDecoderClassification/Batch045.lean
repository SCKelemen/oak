import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1386 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "0010", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1386", ") = {\n    SEE = ", "1386", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_long_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1386 : Clause := ⟨[.fixed "0", .any 1, .fixed "001111", .any 8, .fixed "0010", .any 1, .fixed "0", .any 10], 1386, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_long_decode"⟩
theorem checked1386 : check raw1386 clause1386 = true := by rfl
def row1386 : Row := ⟨1386, 3204510720, 251666432⟩
theorem derived1386 : clause1386.row = row1386 := by rfl
def entry1386 : CheckedRow := ⟨raw1386, clause1386, row1386, checked1386, derived1386⟩

def raw1387 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1387", ") = {\n    SEE = ", "1387", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1387 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "1", .any 5, .fixed "111001", .any 10], 1387, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_simd_decode"⟩
theorem checked1387 : check raw1387 clause1387 = true := by rfl
def row1387 : Row := ⟨1387, 3214998528, 782296064⟩
theorem derived1387 : clause1387.row = row1387 := by rfl
def entry1387 : CheckedRow := ⟨raw1387, clause1387, row1387, checked1387, derived1387⟩

def raw1388 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111011111001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1388", ") = {\n    SEE = ", "1388", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1388 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111011111001101010", .any 10], 1388, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode"⟩
theorem checked1388 : check raw1388 clause1388 = true := by rfl
def row1388 : Row := ⟨1388, 3221224448, 788113408⟩
theorem derived1388 : clause1388.row = row1388 := by rfl
def entry1388 : CheckedRow := ⟨raw1388, clause1388, row1388, checked1388, derived1388⟩

def raw1389 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1389", ") = {\n    SEE = ", "1389", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_addsub_long_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1389 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "000000", .any 10], 1389, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_addsub_long_decode"⟩
theorem checked1389 : check raw1389 clause1389 = true := by rfl
def row1389 : Row := ⟨1389, 3206609920, 773849088⟩
theorem derived1389 : clause1389.row = row1389 := by rfl
def entry1389 : CheckedRow := ⟨raw1389, clause1389, row1389, checked1389, derived1389⟩

def raw1390 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0101011001", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1390", ") = {\n    SEE = ", "1390", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm3", " : bits(", "3", ") = ", "op_code[", "12", " .. ", "10", "]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opt", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_extendedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm3", ", ", "option_name", ", ", "Rm", ", ", "opt", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1390 : Clause := ⟨[.any 1, .fixed "0101011001", .any 21], 1390, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm3", 3, 12, 10, false⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opt", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_extendedreg_decode"⟩
theorem checked1390 : check raw1390 clause1390 = true := by rfl
def row1390 : Row := ⟨1390, 2145386496, 723517440⟩
theorem derived1390 : clause1390.row = row1390 := by rfl
def entry1390 : CheckedRow := ⟨raw1390, clause1390, row1390, checked1390, derived1390⟩

def raw1391 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1391", ") = {\n    SEE = ", "1391", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1391 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000", .any 2, .fixed "1", .any 5, .fixed "001100", .any 10], 1391, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1391 : check raw1391 clause1391 = true := by rfl
def row1391 : Row := ⟨1391, 3206609920, 3089117184⟩
theorem derived1391 : clause1391.row = row1391 := by rfl
def entry1391 : CheckedRow := ⟨raw1391, clause1391, row1391, checked1391, derived1391⟩

def raw1392 : List String := ["function clause decode64 ((", "0b", "0111111001111001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1392", ") = {\n    SEE = ", "1392", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1392 : Clause := ⟨[.fixed "0111111001111001101110", .any 10], 1392, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode"⟩
theorem checked1392 : check raw1392 clause1392 = true := by rfl
def row1392 : Row := ⟨1392, 4294966272, 2121906176⟩
theorem derived1392 : clause1392.row = row1392 := by rfl
def entry1392 : CheckedRow := ⟨raw1392, clause1392, row1392, checked1392, derived1392⟩

def raw1393 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1010001", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1393", ") = {\n    SEE = ", "1393", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_immediate_decode", "(", "Rd", ", ", "Rn", ", ", "imm12", ", ", "shift", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1393 : Clause := ⟨[.any 1, .fixed "1010001", .any 24], 1393, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_immediate_decode"⟩
theorem checked1393 : check raw1393 clause1393 = true := by rfl
def row1393 : Row := ⟨1393, 2130706432, 1358954496⟩
theorem derived1393 : clause1393.row = row1393 := by rfl
def entry1393 : CheckedRow := ⟨raw1393, clause1393, row1393, checked1393, derived1393⟩

def entries45 : List CheckedRow := [entry1386, entry1387, entry1388, entry1389, entry1390, entry1391, entry1392, entry1393]
def rows45 : List Row := [row1386, row1387, row1388, row1389, row1390, row1391, row1392, row1393]
theorem indices45 : rows45.map Row.index = [1386, 1387, 1388, 1389, 1390, 1391, 1392, 1393] := by rfl
theorem bound45 : entries45.map CheckedRow.row = rows45 := by rfl
theorem choices_and_45 : choices rows45 167837696#32 (-1) = [] := by rfl
theorem choices_orr_45 : choices rows45 704708608#32 (-1) = [] := by rfl
theorem choices_eor_45 : choices rows45 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_45 : choices rows45 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
