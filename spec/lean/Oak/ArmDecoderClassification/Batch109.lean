import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1898 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1898", ") = {\n    SEE = ", "1898", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1898 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000000", .any 9, .fixed "01", .any 10], 1898, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1898 : check raw1898 clause1898 = true := by rfl
def row1898 : Row := ⟨1898, 3219131392, 3087008768⟩
theorem derived1898 : clause1898.row = row1898 := by rfl
def entry1898 : CheckedRow := ⟨raw1898, clause1898, row1898, checked1898, derived1898⟩

def raw1899 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111100000", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1899", ") = {\n    SEE = ", "1899", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "h", " : bits(", "1", ") = ", "[op_code[", "5", "]]", ";\n", "    ", "g", " : bits(", "1", ") = ", "[op_code[", "6", "]]", ";\n", "    ", "f", " : bits(", "1", ") = ", "[op_code[", "7", "]]", ";\n", "    ", "e", " : bits(", "1", ") = ", "[op_code[", "8", "]]", ";\n", "    ", "d", " : bits(", "1", ") = ", "[op_code[", "9", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "cmode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "c", " : bits(", "1", ") = ", "[op_code[", "16", "]]", ";\n", "    ", "b", " : bits(", "1", ") = ", "[op_code[", "17", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "18", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_logical_decode", "(", "Rd", ", ", "h", ", ", "g", ", ", "f", ", ", "e", ", ", "d", ", ", "o2", ", ", "cmode", ", ", "c", ", ", "b", ", ", "a", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1899 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111100000", .any 6, .fixed "101", .any 10], 1899, [⟨"Rd", 5, 4, 0, false⟩, ⟨"h", 1, 5, 5, true⟩, ⟨"g", 1, 6, 6, true⟩, ⟨"f", 1, 7, 7, true⟩, ⟨"e", 1, 8, 8, true⟩, ⟨"d", 1, 9, 9, true⟩, ⟨"o2", 1, 11, 11, true⟩, ⟨"cmode", 4, 15, 12, false⟩, ⟨"c", 1, 16, 16, true⟩, ⟨"b", 1, 17, 17, true⟩, ⟨"a", 1, 18, 18, true⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_logical_decode"⟩
theorem checked1899 : check raw1899 clause1899 = true := by rfl
def row1899 : Row := ⟨1899, 3220708352, 788534272⟩
theorem derived1899 : clause1899.row = row1899 := by rfl
def entry1899 : CheckedRow := ⟨raw1899, clause1899, row1899, checked1899, derived1899⟩

def raw1900 : List String := ["function clause decode64 ((", "0b", "01011111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1011", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1900", ") = {\n    SEE = ", "1900", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_double_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1900 : Clause := ⟨[.fixed "01011111", .any 8, .fixed "1011", .any 1, .fixed "0", .any 10], 1900, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mul_double_sisd_decode"⟩
theorem checked1900 : check raw1900 clause1900 = true := by rfl
def row1900 : Row := ⟨1900, 4278252544, 1593880576⟩
theorem derived1900 : clause1900.row = row1900 := by rfl
def entry1900 : CheckedRow := ⟨raw1900, clause1900, row1900, checked1900, derived1900⟩

def raw1901 : List String := ["function clause decode64 ((", "0b", "01001000100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1901", ") = {\n    SEE = ", "1901", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_ordered_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1901 : Clause := ⟨[.fixed "01001000100", .any 5, .fixed "1", .any 15], 1901, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_ordered_decode"⟩
theorem checked1901 : check raw1901 clause1901 = true := by rfl
def row1901 : Row := ⟨1901, 4292902912, 1216380928⟩
theorem derived1901 : clause1901.row = row1901 := by rfl
def entry1901 : CheckedRow := ⟨raw1901, clause1901, row1901, checked1901, derived1901⟩

def raw1902 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1001010", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1902", ") = {\n    SEE = ", "1902", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "N", ", ", "shift", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1902 : Clause := ⟨[.any 1, .fixed "1001010", .any 2, .fixed "1", .any 21], 1902, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"N", 1, 21, 21, true⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_shiftedreg_decode"⟩
theorem checked1902 : check raw1902 clause1902 = true := by rfl
def row1902 : Row := ⟨1902, 2132803584, 1243611136⟩
theorem derived1902 : clause1902.row = row1902 := by rfl
def entry1902 : CheckedRow := ⟨raw1902, clause1902, row1902, checked1902, derived1902⟩

def raw1903 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1903", ") = {\n    SEE = ", "1903", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_halving_truncating_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1903 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "000001", .any 10], 1903, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_halving_truncating_decode"⟩
theorem checked1903 : check raw1903 clause1903 = true := by rfl
def row1903 : Row := ⟨1903, 3206609920, 236979200⟩
theorem derived1903 : clause1903.row = row1903 := by rfl
def entry1903 : CheckedRow := ⟨raw1903, clause1903, row1903, checked1903, derived1903⟩

def raw1904 : List String := ["function clause decode64 ((", "0b", "1111100110", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1904", ") = {\n    SEE = ", "1904", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_unsigned_memory_single_general_immediate_unsigned__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1904 : Clause := ⟨[.fixed "1111100110", .any 22], 1904, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_unsigned_memory_single_general_immediate_unsigned__decode"⟩
theorem checked1904 : check raw1904 clause1904 = true := by rfl
def row1904 : Row := ⟨1904, 4290772992, 4185915392⟩
theorem derived1904 : clause1904.row = row1904 := by rfl
def entry1904 : CheckedRow := ⟨raw1904, clause1904, row1904, checked1904, derived1904⟩

def raw1905 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1905", ") = {\n    SEE = ", "1905", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_special_sqrtest_float_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1905 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "100001110110", .any 10], 1905, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_special_sqrtest_float_sisd_decode"⟩
theorem checked1905 : check raw1905 clause1905 = true := by rfl
def row1905 : Row := ⟨1905, 4290771968, 2124535808⟩
theorem derived1905 : clause1905.row = row1905 := by rfl
def entry1905 : CheckedRow := ⟨raw1905, clause1905, row1905, checked1905, derived1905⟩

def entries109 : List CheckedRow := [entry1898, entry1899, entry1900, entry1901, entry1902, entry1903, entry1904, entry1905]
def rows109 : List Row := [row1898, row1899, row1900, row1901, row1902, row1903, row1904, row1905]
theorem indices109 : rows109.map Row.index = [1898, 1899, 1900, 1901, 1902, 1903, 1904, 1905] := by rfl
theorem bound109 : entries109.map CheckedRow.row = rows109 := by rfl
theorem choices_and_109 : choices rows109 167837696#32 (-1) = [] := by rfl
theorem choices_orr_109 : choices rows109 704708608#32 (-1) = [] := by rfl
theorem choices_eor_109 : choices rows109 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_109 : choices rows109 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
