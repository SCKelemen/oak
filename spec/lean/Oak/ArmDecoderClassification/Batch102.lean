import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1842 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111011111001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1842", ") = {\n    SEE = ", "1842", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1842 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111011111001101110", .any 10], 1842, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode"⟩
theorem checked1842 : check raw1842 clause1842 = true := by rfl
def row1842 : Row := ⟨1842, 3221224448, 251246592⟩
theorem derived1842 : clause1842.row = row1842 := by rfl
def entry1842 : CheckedRow := ⟨raw1842, clause1842, row1842, checked1842, derived1842⟩

def raw1843 : List String := ["function clause decode64 ((", "0b", "01011110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1843", ") = {\n    SEE = ", "1843", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm4", " : bits(", "4", ") = ", "op_code[", "14", " .. ", "11", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_transfer_vector_cpydup_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "imm4", ", ", "imm5", ", ", "op", ")\n}\n"]
def clause1843 : Clause := ⟨[.fixed "01011110000", .any 5, .fixed "000001", .any 10], 1843, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm4", 4, 14, 11, false⟩, ⟨"imm5", 5, 20, 16, false⟩, ⟨"op", 1, 29, 29, true⟩], "vector_transfer_vector_cpydup_sisd_decode"⟩
theorem checked1843 : check raw1843 clause1843 = true := by rfl
def row1843 : Row := ⟨1843, 4292934656, 1577059328⟩
theorem derived1843 : clause1843.row = row1843 := by rfl
def entry1843 : CheckedRow := ⟨raw1843, clause1843, row1843, checked1843, derived1843⟩

def raw1844 : List String := ["function clause decode64 ((", "0b", "01001000100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1844", ") = {\n    SEE = ", "1844", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_ordered_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1844 : Clause := ⟨[.fixed "01001000100", .any 5, .fixed "0", .any 15], 1844, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_ordered_decode"⟩
theorem checked1844 : check raw1844 clause1844 = true := by rfl
def row1844 : Row := ⟨1844, 4292902912, 1216348160⟩
theorem derived1844 : clause1844.row = row1844 := by rfl
def entry1844 : CheckedRow := ⟨raw1844, clause1844, row1844, checked1844, derived1844⟩

def raw1845 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0001010", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1845", ") = {\n    SEE = ", "1845", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "N", ", ", "shift", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1845 : Clause := ⟨[.any 1, .fixed "0001010", .any 2, .fixed "0", .any 21], 1845, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"N", 1, 21, 21, true⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_shiftedreg_decode"⟩
theorem checked1845 : check raw1845 clause1845 = true := by rfl
def row1845 : Row := ⟨1845, 2132803584, 167772160⟩
theorem derived1845 : clause1845.row = row1845 := by rfl
def entry1845 : CheckedRow := ⟨raw1845, clause1845, row1845, checked1845, derived1845⟩

def raw1846 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1846", ") = {\n    SEE = ", "1846", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1846 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "0", .any 5, .fixed "100001", .any 10], 1846, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode"⟩
theorem checked1846 : check raw1846 clause1846 = true := by rfl
def row1846 : Row := ⟨1846, 4280351744, 2113963008⟩
theorem derived1846 : clause1846.row = row1846 := by rfl
def entry1846 : CheckedRow := ⟨raw1846, clause1846, row1846, checked1846, derived1846⟩

def raw1847 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "101000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1847", ") = {\n    SEE = ", "1847", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_accum_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1847 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "101000", .any 10], 1847, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_mul_accum_decode"⟩
theorem checked1847 : check raw1847 clause1847 = true := by rfl
def row1847 : Row := ⟨1847, 3206609920, 773890048⟩
theorem derived1847 : clause1847.row = row1847 := by rfl
def entry1847 : CheckedRow := ⟨raw1847, clause1847, row1847, checked1847, derived1847⟩

def raw1848 : List String := ["function clause decode64 ((", "0b", "0101111000101000000110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1848", ") = {\n    SEE = ", "1848", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha2op_sha1sched1_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ")\n}\n"]
def clause1848 : Clause := ⟨[.fixed "0101111000101000000110", .any 10], 1848, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha2op_sha1sched1_decode"⟩
theorem checked1848 : check raw1848 clause1848 = true := by rfl
def row1848 : Row := ⟨1848, 4294966272, 1579685888⟩
theorem derived1848 : clause1848.row = row1848 := by rfl
def entry1848 : CheckedRow := ⟨raw1848, clause1848, row1848, checked1848, derived1848⟩

def raw1849 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111001111001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1849", ") = {\n    SEE = ", "1849", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1849 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111001111001101010", .any 10], 1849, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode"⟩
theorem checked1849 : check raw1849 clause1849 = true := by rfl
def row1849 : Row := ⟨1849, 3221224448, 242853888⟩
theorem derived1849 : clause1849.row = row1849 := by rfl
def entry1849 : CheckedRow := ⟨raw1849, clause1849, row1849, checked1849, derived1849⟩

def entries102 : List CheckedRow := [entry1842, entry1843, entry1844, entry1845, entry1846, entry1847, entry1848, entry1849]
def rows102 : List Row := [row1842, row1843, row1844, row1845, row1846, row1847, row1848, row1849]
theorem indices102 : rows102.map Row.index = [1842, 1843, 1844, 1845, 1846, 1847, 1848, 1849] := by rfl
theorem bound102 : entries102.map CheckedRow.row = rows102 := by rfl
theorem choices_and_102 : choices rows102 167837696#32 (-1) = [1845] := by rfl
theorem choices_orr_102 : choices rows102 704708608#32 (-1) = [] := by rfl
theorem choices_eor_102 : choices rows102 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_102 : choices rows102 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
