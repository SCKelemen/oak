import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1818 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110111", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1818", ") = {\n    SEE = ", "1818", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_logical_andorr_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1818 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110111", .any 5, .fixed "000111", .any 10], 1818, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_logical_andorr_decode"⟩
theorem checked1818 : check raw1818 clause1818 = true := by rfl
def row1818 : Row := ⟨1818, 3219192832, 249568256⟩
theorem derived1818 : clause1818.row = row1818 := by rfl
def entry1818 : CheckedRow := ⟨raw1818, clause1818, row1818, checked1818, derived1818⟩

def raw1819 : List String := ["function clause decode64 ((", "0b", "01001000110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1819", ") = {\n    SEE = ", "1819", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_ordered_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1819 : Clause := ⟨[.fixed "01001000110", .any 5, .fixed "1", .any 15], 1819, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_ordered_decode"⟩
theorem checked1819 : check raw1819 clause1819 = true := by rfl
def row1819 : Row := ⟨1819, 4292902912, 1220575232⟩
theorem derived1819 : clause1819.row = row1819 := by rfl
def entry1819 : CheckedRow := ⟨raw1819, clause1819, row1819, checked1819, derived1819⟩

def raw1820 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1820", ") = {\n    SEE = ", "1820", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1820 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101110", .any 7, .fixed "1", .any 13], 1820, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1820 : check raw1820 clause1820 = true := by rfl
def row1820 : Row := ⟨1820, 3219136512, 230694912⟩
theorem derived1820 : clause1820.row = row1820 := by rfl
def entry1820 : CheckedRow := ⟨raw1820, clause1820, row1820, checked1820, derived1820⟩

def raw1821 : List String := ["function clause decode64 ((", "0b", "00111000010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1821", ") = {\n    SEE = ", "1821", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1821 : Clause := ⟨[.fixed "00111000010", .any 9, .fixed "01", .any 10], 1821, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1821 : check raw1821 clause1821 = true := by rfl
def row1821 : Row := ⟨1821, 4292873216, 943719424⟩
theorem derived1821 : clause1821.row = row1821 := by rfl
def entry1821 : CheckedRow := ⟨raw1821, clause1821, row1821, checked1821, derived1821⟩

def raw1822 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1822", ") = {\n    SEE = ", "1822", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_saturating_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1822 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "1", .any 5, .fixed "001011", .any 10], 1822, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_sub_saturating_sisd_decode"⟩
theorem checked1822 : check raw1822 clause1822 = true := by rfl
def row1822 : Row := ⟨1822, 4280351744, 2116037632⟩
theorem derived1822 : clause1822.row = row1822 := by rfl
def entry1822 : CheckedRow := ⟨raw1822, clause1822, row1822, checked1822, derived1822⟩

def raw1823 : List String := ["function clause decode64 ((", "0b", "00111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1823", ") = {\n    SEE = ", "1823", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1823 : Clause := ⟨[.fixed "00111000000", .any 9, .fixed "00", .any 10], 1823, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1823 : check raw1823 clause1823 = true := by rfl
def row1823 : Row := ⟨1823, 4292873216, 939524096⟩
theorem derived1823 : clause1823.row = row1823 := by rfl
def entry1823 : CheckedRow := ⟨raw1823, clause1823, row1823, checked1823, derived1823⟩

def raw1824 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111100", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "1001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1824", ") = {\n    SEE = ", "1824", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1824 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111100", .any 6, .fixed "1001", .any 1, .fixed "0", .any 10], 1824, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mul_fp16_simd_decode"⟩
theorem checked1824 : check raw1824 clause1824 = true := by rfl
def row1824 : Row := ⟨1824, 3217093632, 251695104⟩
theorem derived1824 : clause1824.row = row1824 := by rfl
def entry1824 : CheckedRow := ⟨raw1824, clause1824, row1824, checked1824, derived1824⟩

def raw1825 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "10100", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "10000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1825", ") = {\n    SEE = ", "1825", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "16", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "float_arithmetic_round_frint_32_64_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "typ", ")\n}\n"]
def clause1825 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "10100", .any 2, .fixed "10000", .any 10], 1825, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 2, 16, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩], "float_arithmetic_round_frint_32_64_decode"⟩
theorem checked1825 : check raw1825 clause1825 = true := by rfl
def row1825 : Row := ⟨1825, 4282285056, 505954304⟩
theorem derived1825 : clause1825.row = row1825 := by rfl
def entry1825 : CheckedRow := ⟨raw1825, clause1825, row1825, checked1825, derived1825⟩

def entries99 : List CheckedRow := [entry1818, entry1819, entry1820, entry1821, entry1822, entry1823, entry1824, entry1825]
def rows99 : List Row := [row1818, row1819, row1820, row1821, row1822, row1823, row1824, row1825]
theorem indices99 : rows99.map Row.index = [1818, 1819, 1820, 1821, 1822, 1823, 1824, 1825] := by rfl
theorem bound99 : entries99.map CheckedRow.row = rows99 := by rfl
theorem choices_and_99 : choices rows99 167837696#32 (-1) = [] := by rfl
theorem choices_orr_99 : choices rows99 704708608#32 (-1) = [] := by rfl
theorem choices_eor_99 : choices rows99 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_99 : choices rows99 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
