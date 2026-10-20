import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1754 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1754", ") = {\n    SEE = ", "1754", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_diff_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1754 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "011101", .any 10], 1754, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_diff_decode"⟩
theorem checked1754 : check raw1754 clause1754 = true := by rfl
def row1754 : Row := ⟨1754, 3206609920, 237007872⟩
theorem derived1754 : clause1754.row = row1754 := by rfl
def entry1754 : CheckedRow := ⟨raw1754, clause1754, row1754, checked1754, derived1754⟩

def raw1755 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1755", ") = {\n    SEE = ", "1755", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_add_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1755 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "110001101110", .any 10], 1755, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_add_sisd_decode"⟩
theorem checked1755 : check raw1755 clause1755 = true := by rfl
def row1755 : Row := ⟨1755, 4282383360, 1580316672⟩
theorem derived1755 : clause1755.row = row1755 := by rfl
def entry1755 : CheckedRow := ⟨raw1755, clause1755, row1755, checked1755, derived1755⟩

def raw1756 : List String := ["function clause decode64 ((", "0b", "01111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1756", ") = {\n    SEE = ", "1756", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1756 : Clause := ⟨[.fixed "01111000000", .any 9, .fixed "01", .any 10], 1756, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1756 : check raw1756 clause1756 = true := by rfl
def row1756 : Row := ⟨1756, 4292873216, 2013266944⟩
theorem derived1756 : clause1756.row = row1756 := by rfl
def entry1756 : CheckedRow := ⟨raw1756, clause1756, row1756, checked1756, derived1756⟩

def raw1757 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1757", ") = {\n    SEE = ", "1757", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_simd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1757 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "010111", .any 10], 1757, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_shift_simd_decode"⟩
theorem checked1757 : check raw1757 clause1757 = true := by rfl
def row1757 : Row := ⟨1757, 3206609920, 237001728⟩
theorem derived1757 : clause1757.row = row1757 := by rfl
def entry1757 : CheckedRow := ⟨raw1757, clause1757, row1757, checked1757, derived1757⟩

def raw1758 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001000010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1758", ") = {\n    SEE = ", "1758", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1758 : Clause := ⟨[.fixed "1", .any 1, .fixed "001000010", .any 5, .fixed "0", .any 15], 1758, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1758 : check raw1758 clause1758 = true := by rfl
def row1758 : Row := ⟨1758, 3219161088, 2285895680⟩
theorem derived1758 : clause1758.row = row1758 := by rfl
def entry1758 : CheckedRow := ⟨raw1758, clause1758, row1758, checked1758, derived1758⟩

def raw1759 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1759", ") = {\n    SEE = ", "1759", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp_1985_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1759 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "1", .any 5, .fixed "111101", .any 10], 1759, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp_1985_decode"⟩
theorem checked1759 : check raw1759 clause1759 = true := by rfl
def row1759 : Row := ⟨1759, 3214998528, 782300160⟩
theorem derived1759 : clause1759.row = row1759 := by rfl
def entry1759 : CheckedRow := ⟨raw1759, clause1759, row1759, checked1759, derived1759⟩

def raw1760 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1760", ") = {\n    SEE = ", "1760", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1760 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "0", .any 5, .fixed "100011", .any 10], 1760, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_mul_int_doubling_accum_sisd_decode"⟩
theorem checked1760 : check raw1760 clause1760 = true := by rfl
def row1760 : Row := ⟨1760, 4280351744, 2113965056⟩
theorem derived1760 : clause1760.row = row1760 := by rfl
def entry1760 : CheckedRow := ⟨raw1760, clause1760, row1760, checked1760, derived1760⟩

def raw1761 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101111", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1100", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1761", ") = {\n    SEE = ", "1761", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1761 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101111", .any 5, .fixed "1100", .any 12], 1761, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1761 : check raw1761 clause1761 = true := by rfl
def row1761 : Row := ⟨1761, 3219189760, 232833024⟩
theorem derived1761 : clause1761.row = row1761 := by rfl
def entry1761 : CheckedRow := ⟨raw1761, clause1761, row1761, checked1761, derived1761⟩

def entries91 : List CheckedRow := [entry1754, entry1755, entry1756, entry1757, entry1758, entry1759, entry1760, entry1761]
def rows91 : List Row := [row1754, row1755, row1756, row1757, row1758, row1759, row1760, row1761]
theorem indices91 : rows91.map Row.index = [1754, 1755, 1756, 1757, 1758, 1759, 1760, 1761] := by rfl
theorem bound91 : entries91.map CheckedRow.row = rows91 := by rfl
theorem choices_and_91 : choices rows91 167837696#32 (-1) = [] := by rfl
theorem choices_orr_91 : choices rows91 704708608#32 (-1) = [] := by rfl
theorem choices_eor_91 : choices rows91 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_91 : choices rows91 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
