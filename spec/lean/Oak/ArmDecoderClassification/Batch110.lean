import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1906 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1906", ") = {\n    SEE = ", "1906", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1906 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "1", .any 5, .fixed "100001", .any 10], 1906, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode"⟩
theorem checked1906 : check raw1906 clause1906 = true := by rfl
def row1906 : Row := ⟨1906, 4280351744, 2116060160⟩
theorem derived1906 : clause1906.row = row1906 := by rfl
def entry1906 : CheckedRow := ⟨raw1906, clause1906, row1906, checked1906, derived1906⟩

def raw1907 : List String := ["function clause decode64 ((", "0b", "010111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1907", ") = {\n    SEE = ", "1907", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_right_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1907 : Clause := ⟨[.fixed "010111110", .any 7, .fixed "001101", .any 10], 1907, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_right_sisd_decode"⟩
theorem checked1907 : check raw1907 clause1907 = true := by rfl
def row1907 : Row := ⟨1907, 4286643200, 1593848832⟩
theorem derived1907 : clause1907.row = row1907 := by rfl
def entry1907 : CheckedRow := ⟨raw1907, clause1907, row1907, checked1907, derived1907⟩

def raw1908 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1908", ") = {\n    SEE = ", "1908", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1908 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "100001101110", .any 10], 1908, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_simd_decode"⟩
theorem checked1908 : check raw1908 clause1908 = true := by rfl
def row1908 : Row := ⟨1908, 3217030144, 782350336⟩
theorem derived1908 : clause1908.row = row1908 := by rfl
def entry1908 : CheckedRow := ⟨raw1908, clause1908, row1908, checked1908, derived1908⟩

def raw1909 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1909", ") = {\n    SEE = ", "1909", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_simdfp_immediate_unsigned_memory_single_simdfp_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1909 : Clause := ⟨[.any 2, .fixed "111101", .any 1, .fixed "1", .any 22], 1909, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_simdfp_immediate_unsigned_memory_single_simdfp_immediate_signed_postidx__decode"⟩
theorem checked1909 : check raw1909 clause1909 = true := by rfl
def row1909 : Row := ⟨1909, 1061158912, 1027604480⟩
theorem derived1909 : clause1909.row = row1909 := by rfl
def entry1909 : CheckedRow := ⟨raw1909, clause1909, row1909, checked1909, derived1909⟩

def raw1910 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "10110000", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1910", ") = {\n    SEE = ", "1910", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_simdfp_noalloc_memory_pair_simdfp_noalloc__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1910 : Clause := ⟨[.any 2, .fixed "10110000", .any 22], 1910, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_simdfp_noalloc_memory_pair_simdfp_noalloc__decode"⟩
theorem checked1910 : check raw1910 clause1910 = true := by rfl
def row1910 : Row := ⟨1910, 1069547520, 738197504⟩
theorem derived1910 : clause1910.row = row1910 := by rfl
def entry1910 : CheckedRow := ⟨raw1910, clause1910, row1910, checked1910, derived1910⟩

def raw1911 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111100", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "0101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1911", ") = {\n    SEE = ", "1911", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1911 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111100", .any 6, .fixed "0101", .any 1, .fixed "0", .any 10], 1911, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_fp16_simd_decode"⟩
theorem checked1911 : check raw1911 clause1911 = true := by rfl
def row1911 : Row := ⟨1911, 3217093632, 251678720⟩
theorem derived1911 : clause1911.row = row1911 := by rfl
def entry1911 : CheckedRow := ⟨raw1911, clause1911, row1911, checked1911, derived1911⟩

def raw1912 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "010100101", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1912", ") = {\n    SEE = ", "1912", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_general_offset_memory_pair_general_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1912 : Clause := ⟨[.any 1, .fixed "010100101", .any 22], 1912, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_general_offset_memory_pair_general_postidx__decode"⟩
theorem checked1912 : check raw1912 clause1912 = true := by rfl
def row1912 : Row := ⟨1912, 2143289344, 692060160⟩
theorem derived1912 : clause1912.row = row1912 := by rfl
def entry1912 : CheckedRow := ⟨raw1912, clause1912, row1912, checked1912, derived1912⟩

def raw1913 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1913", ") = {\n    SEE = ", "1913", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "opcode2_5_1_", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_div_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "opcode2_5_1_", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1913 : Clause := ⟨[.any 1, .fixed "0011010110", .any 5, .fixed "000010", .any 10], 1913, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 10, 10, true⟩, ⟨"opcode2_5_1_", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_div_decode"⟩
theorem checked1913 : check raw1913 clause1913 = true := by rfl
def row1913 : Row := ⟨1913, 2145451008, 448792576⟩
theorem derived1913 : clause1913.row = row1913 := by rfl
def entry1913 : CheckedRow := ⟨raw1913, clause1913, row1913, checked1913, derived1913⟩

def entries110 : List CheckedRow := [entry1906, entry1907, entry1908, entry1909, entry1910, entry1911, entry1912, entry1913]
def rows110 : List Row := [row1906, row1907, row1908, row1909, row1910, row1911, row1912, row1913]
theorem indices110 : rows110.map Row.index = [1906, 1907, 1908, 1909, 1910, 1911, 1912, 1913] := by rfl
theorem bound110 : entries110.map CheckedRow.row = rows110 := by rfl
theorem choices_and_110 : choices rows110 167837696#32 (-1) = [] := by rfl
theorem choices_orr_110 : choices rows110 704708608#32 (-1) = [] := by rfl
theorem choices_eor_110 : choices rows110 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_110 : choices rows110 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
