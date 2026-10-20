import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1914 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1914", ") = {\n    SEE = ", "1914", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_simd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1914 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "010001", .any 10], 1914, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_shift_simd_decode"⟩
theorem checked1914 : check raw1914 clause1914 = true := by rfl
def row1914 : Row := ⟨1914, 3206609920, 773866496⟩
theorem derived1914 : clause1914.row = row1914 := by rfl
def entry1914 : CheckedRow := ⟨raw1914, clause1914, row1914, checked1914, derived1914⟩

def raw1915 : List String := ["function clause decode64 ((", "0b", "00011001000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1915", ") = {\n    SEE = ", "1915", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagpre_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1915 : Clause := ⟨[.fixed "00011001000", .any 9, .fixed "11", .any 10], 1915, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagpre_decode"⟩
theorem checked1915 : check raw1915 clause1915 = true := by rfl
def row1915 : Row := ⟨1915, 4292873216, 419433472⟩
theorem derived1915 : clause1915.row = row1915 := by rfl
def entry1915 : CheckedRow := ⟨raw1915, clause1915, row1915, checked1915, derived1915⟩

def raw1916 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000010110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1916", ") = {\n    SEE = ", "1916", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cnt_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1916 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000010110", .any 10], 1916, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cnt_decode"⟩
theorem checked1916 : check raw1916 clause1916 = true := by rfl
def row1916 : Row := ⟨1916, 3208641536, 237000704⟩
theorem derived1916 : clause1916.row = row1916 := by rfl
def entry1916 : CheckedRow := ⟨raw1916, clause1916, row1916, checked1916, derived1916⟩

def raw1917 : List String := ["function clause decode64 ((", "0b", "010111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "011101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1917", ") = {\n    SEE = ", "1917", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_leftsat_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1917 : Clause := ⟨[.fixed "010111110", .any 7, .fixed "011101", .any 10], 1917, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_leftsat_sisd_decode"⟩
theorem checked1917 : check raw1917 clause1917 = true := by rfl
def row1917 : Row := ⟨1917, 4286643200, 1593865216⟩
theorem derived1917 : clause1917.row = row1917 := by rfl
def entry1917 : CheckedRow := ⟨raw1917, clause1917, row1917, checked1917, derived1917⟩

def raw1918 : List String := ["function clause decode64 ((", "0b", "010111111", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "0001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1918", ") = {\n    SEE = ", "1918", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_fp_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1918 : Clause := ⟨[.fixed "010111111", .any 7, .fixed "0001", .any 1, .fixed "0", .any 10], 1918, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mulacc_fp_sisd_decode"⟩
theorem checked1918 : check raw1918 clause1918 = true := by rfl
def row1918 : Row := ⟨1918, 4286641152, 1602228224⟩
theorem derived1918 : clause1918.row = row1918 := by rfl
def entry1918 : CheckedRow := ⟨raw1918, clause1918, row1918, checked1918, derived1918⟩

def raw1919 : List String := ["function clause decode64 ((", "0b", "011110001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1919", ") = {\n    SEE = ", "1919", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_register_memory_single_general_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1919 : Clause := ⟨[.fixed "011110001", .any 1, .fixed "1", .any 9, .fixed "10", .any 10], 1919, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_register_memory_single_general_register__decode"⟩
theorem checked1919 : check raw1919 clause1919 = true := by rfl
def row1919 : Row := ⟨1919, 4288678912, 2023753728⟩
theorem derived1919 : clause1919.row = row1919 := by rfl
def entry1919 : CheckedRow := ⟨raw1919, clause1919, row1919, checked1919, derived1919⟩

def raw1920 : List String := ["function clause decode64 ((", "0b", "10011011010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1920", ") = {\n    SEE = ", "1920", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "op54", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_mul_widening_64128hi_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "U", ", ", "op54", ", ", "sf", ")\n}\n"]
def clause1920 : Clause := ⟨[.fixed "10011011010", .any 5, .fixed "0", .any 15], 1920, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"U", 1, 23, 23, true⟩, ⟨"op54", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_mul_widening_64128hi_decode"⟩
theorem checked1920 : check raw1920 clause1920 = true := by rfl
def row1920 : Row := ⟨1920, 4292902912, 2604662784⟩
theorem derived1920 : clause1920.row = row1920 := by rfl
def entry1920 : CheckedRow := ⟨raw1920, clause1920, row1920, checked1920, derived1920⟩

def raw1921 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1921", ") = {\n    SEE = ", "1921", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_float_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1921 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "100000111110", .any 10], 1921, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_diffneg_float_decode"⟩
theorem checked1921 : check raw1921 clause1921 = true := by rfl
def row1921 : Row := ⟨1921, 3217030144, 245430272⟩
theorem derived1921 : clause1921.row = row1921 := by rfl
def entry1921 : CheckedRow := ⟨raw1921, clause1921, row1921, checked1921, derived1921⟩

def entries111 : List CheckedRow := [entry1914, entry1915, entry1916, entry1917, entry1918, entry1919, entry1920, entry1921]
def rows111 : List Row := [row1914, row1915, row1916, row1917, row1918, row1919, row1920, row1921]
theorem indices111 : rows111.map Row.index = [1914, 1915, 1916, 1917, 1918, 1919, 1920, 1921] := by rfl
theorem bound111 : entries111.map CheckedRow.row = rows111 := by rfl
theorem choices_and_111 : choices rows111 167837696#32 (-1) = [] := by rfl
theorem choices_orr_111 : choices rows111 704708608#32 (-1) = [] := by rfl
theorem choices_eor_111 : choices rows111 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_111 : choices rows111 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
