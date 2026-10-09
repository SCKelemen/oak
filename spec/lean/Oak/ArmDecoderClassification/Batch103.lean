import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1850 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100101010000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1850", ") = {\n    SEE = ", "1850", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "rmode", " : bits(", "3", ") = ", "op_code[", "17", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_round_frint_decode", "(", "Rd", ", ", "Rn", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1850 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100101010000", .any 10], 1850, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"rmode", 3, 17, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_round_frint_decode"⟩
theorem checked1850 : check raw1850 clause1850 = true := by rfl
def row1850 : Row := ⟨1850, 4282383360, 505757696⟩
theorem derived1850 : clause1850.row = row1850 := by rfl
def entry1850 : CheckedRow := ⟨raw1850, clause1850, row1850, checked1850, derived1850⟩

def raw1851 : List String := ["function clause decode64 ((", "0b", "00011001101", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1851", ") = {\n    SEE = ", "1851", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagpairandzerodatapre_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1851 : Clause := ⟨[.fixed "00011001101", .any 9, .fixed "11", .any 10], 1851, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagpairandzerodatapre_decode"⟩
theorem checked1851 : check raw1851 clause1851 = true := by rfl
def row1851 : Row := ⟨1851, 4292873216, 429919232⟩
theorem derived1851 : clause1851.row = row1851 := by rfl
def entry1851 : CheckedRow := ⟨raw1851, clause1851, row1851, checked1851, derived1851⟩

def raw1852 : List String := ["function clause decode64 ((", "0b", "0101111010110000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1852", ") = {\n    SEE = ", "1852", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fp16max_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ")\n}\n"]
def clause1852 : Clause := ⟨[.fixed "0101111010110000111110", .any 10], 1852, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fp16max_sisd_decode"⟩
theorem checked1852 : check raw1852 clause1852 = true := by rfl
def row1852 : Row := ⟨1852, 4294966272, 1588656128⟩
theorem derived1852 : clause1852.row = row1852 := by rfl
def entry1852 : CheckedRow := ⟨raw1852, clause1852, row1852, checked1852, derived1852⟩

def raw1853 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110101", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1853", ") = {\n    SEE = ", "1853", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_logical_andorr_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1853 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110101", .any 5, .fixed "000111", .any 10], 1853, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_logical_andorr_decode"⟩
theorem checked1853 : check raw1853 clause1853 = true := by rfl
def row1853 : Row := ⟨1853, 3219192832, 245373952⟩
theorem derived1853 : clause1853.row = row1853 := by rfl
def entry1853 : CheckedRow := ⟨raw1853, clause1853, row1853, checked1853, derived1853⟩

def raw1854 : List String := ["function clause decode64 ((", "0b", "011110001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1854", ") = {\n    SEE = ", "1854", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1854 : Clause := ⟨[.fixed "011110001", .any 1, .fixed "0", .any 9, .fixed "00", .any 10], 1854, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1854 : check raw1854 clause1854 = true := by rfl
def row1854 : Row := ⟨1854, 4288678912, 2021654528⟩
theorem derived1854 : clause1854.row = row1854 := by rfl
def entry1854 : CheckedRow := ⟨raw1854, clause1854, row1854, checked1854, derived1854⟩

def raw1855 : List String := ["function clause decode64 ((", "0b", "011110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1855", ") = {\n    SEE = ", "1855", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1855 : Clause := ⟨[.fixed "011110000", .any 1, .fixed "1", .any 5, .fixed "001100", .any 5, .fixed "11111"], 1855, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1855 : check raw1855 clause1855 = true := by rfl
def row1855 : Row := ⟨1855, 4288740383, 2015375391⟩
theorem derived1855 : clause1855.row = row1855 := by rfl
def entry1855 : CheckedRow := ⟨raw1855, clause1855, row1855, checked1855, derived1855⟩

def raw1856 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1000", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1856", ") = {\n    SEE = ", "1856", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "Rm", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1856 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100100", .any 5, .fixed "1000", .any 12], 1856, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode"⟩
theorem checked1856 : check raw1856 clause1856 = true := by rfl
def row1856 : Row := ⟨1856, 3219189760, 209747968⟩
theorem derived1856 : clause1856.row = row1856 := by rfl
def entry1856 : CheckedRow := ⟨raw1856, clause1856, row1856, checked1856, derived1856⟩

def raw1857 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1857", ") = {\n    SEE = ", "1857", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1857 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "100000110010", .any 10], 1857, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_float_bulk_sisd_decode"⟩
theorem checked1857 : check raw1857 clause1857 = true := by rfl
def row1857 : Row := ⟨1857, 4290771968, 2124466176⟩
theorem derived1857 : clause1857.row = row1857 := by rfl
def entry1857 : CheckedRow := ⟨raw1857, clause1857, row1857, checked1857, derived1857⟩

def entries103 : List CheckedRow := [entry1850, entry1851, entry1852, entry1853, entry1854, entry1855, entry1856, entry1857]
def rows103 : List Row := [row1850, row1851, row1852, row1853, row1854, row1855, row1856, row1857]
theorem indices103 : rows103.map Row.index = [1850, 1851, 1852, 1853, 1854, 1855, 1856, 1857] := by rfl
theorem bound103 : entries103.map CheckedRow.row = rows103 := by rfl
theorem choices_and_103 : choices rows103 167837696#32 (-1) = [] := by rfl
theorem choices_orr_103 : choices rows103 704708608#32 (-1) = [] := by rfl
theorem choices_eor_103 : choices rows103 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_103 : choices rows103 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
