import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1866 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1866", ") = {\n    SEE = ", "1866", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_halving_rounding_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1866 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "000101", .any 10], 1866, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_halving_rounding_decode"⟩
theorem checked1866 : check raw1866 clause1866 = true := by rfl
def row1866 : Row := ⟨1866, 3206609920, 773854208⟩
theorem derived1866 : clause1866.row = row1866 := by rfl
def entry1866 : CheckedRow := ⟨raw1866, clause1866, row1866, checked1866, derived1866⟩

def raw1867 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1867", ") = {\n    SEE = ", "1867", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp_2008_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1867 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "1", .any 5, .fixed "110001", .any 10], 1867, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp_2008_decode"⟩
theorem checked1867 : check raw1867 clause1867 = true := by rfl
def row1867 : Row := ⟨1867, 3214998528, 245416960⟩
theorem derived1867 : clause1867.row = row1867 := by rfl
def entry1867 : CheckedRow := ⟨raw1867, clause1867, row1867, checked1867, derived1867⟩

def raw1868 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000000010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1868", ") = {\n    SEE = ", "1868", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_rev_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1868 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000000010", .any 10], 1868, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_rev_decode"⟩
theorem checked1868 : check raw1868 clause1868 = true := by rfl
def row1868 : Row := ⟨1868, 3208641536, 236980224⟩
theorem derived1868 : clause1868.row = row1868 := by rfl
def entry1868 : CheckedRow := ⟨raw1868, clause1868, row1868, checked1868, derived1868⟩

def raw1869 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1869", ") = {\n    SEE = ", "1869", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_right_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1869 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "001101", .any 10], 1869, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_right_simd_decode"⟩
theorem checked1869 : check raw1869 clause1869 = true := by rfl
def row1869 : Row := ⟨1869, 3212901376, 788542464⟩
theorem derived1869 : clause1869.row = row1869 := by rfl
def entry1869 : CheckedRow := ⟨raw1869, clause1869, row1869, checked1869, derived1869⟩

def raw1870 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "011101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1870", ") = {\n    SEE = ", "1870", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_leftsat_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1870 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "011101", .any 10], 1870, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_leftsat_sisd_decode"⟩
theorem checked1870 : check raw1870 clause1870 = true := by rfl
def row1870 : Row := ⟨1870, 4286643200, 2130736128⟩
theorem derived1870 : clause1870.row = row1870 := by rfl
def entry1870 : CheckedRow := ⟨raw1870, clause1870, row1870, checked1870, derived1870⟩

def raw1871 : List String := ["function clause decode64 ((", "0b", "11011000", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1871", ") = {\n    SEE = ", "1871", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm19", " : bits(", "19", ") = ", "op_code[", "23", " .. ", "5", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_literal_general_decode", "(", "Rt", ", ", "imm19", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1871 : Clause := ⟨[.fixed "11011000", .any 24], 1871, [⟨"Rt", 5, 4, 0, false⟩, ⟨"imm19", 19, 23, 5, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_literal_general_decode"⟩
theorem checked1871 : check raw1871 clause1871 = true := by rfl
def row1871 : Row := ⟨1871, 4278190080, 3623878656⟩
theorem derived1871 : clause1871.row = row1871 := by rfl
def entry1871 : CheckedRow := ⟨raw1871, clause1871, row1871, checked1871, derived1871⟩

def raw1872 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1872", ") = {\n    SEE = ", "1872", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fpmaxnm_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ")\n}\n"]
def clause1872 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "110000110010", .any 10], 1872, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fpmaxnm_sisd_decode"⟩
theorem checked1872 : check raw1872 clause1872 = true := by rfl
def row1872 : Row := ⟨1872, 4290771968, 2125514752⟩
theorem derived1872 : clause1872.row = row1872 := by rfl
def entry1872 : CheckedRow := ⟨raw1872, clause1872, row1872, checked1872, derived1872⟩

def raw1873 : List String := ["function clause decode64 ((", "0b", "010111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1873", ") = {\n    SEE = ", "1873", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp_extended_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1873 : Clause := ⟨[.fixed "010111100", .any 1, .fixed "1", .any 5, .fixed "110111", .any 10], 1873, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_mul_fp_extended_sisd_decode"⟩
theorem checked1873 : check raw1873 clause1873 = true := by rfl
def row1873 : Row := ⟨1873, 4288740352, 1579211776⟩
theorem derived1873 : clause1873.row = row1873 := by rfl
def entry1873 : CheckedRow := ⟨raw1873, clause1873, row1873, checked1873, derived1873⟩

def entries105 : List CheckedRow := [entry1866, entry1867, entry1868, entry1869, entry1870, entry1871, entry1872, entry1873]
def rows105 : List Row := [row1866, row1867, row1868, row1869, row1870, row1871, row1872, row1873]
theorem indices105 : rows105.map Row.index = [1866, 1867, 1868, 1869, 1870, 1871, 1872, 1873] := by rfl
theorem bound105 : entries105.map CheckedRow.row = rows105 := by rfl
theorem choices_and_105 : choices rows105 167837696#32 (-1) = [] := by rfl
theorem choices_orr_105 : choices rows105 704708608#32 (-1) = [] := by rfl
theorem choices_eor_105 : choices rows105 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_105 : choices rows105 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
