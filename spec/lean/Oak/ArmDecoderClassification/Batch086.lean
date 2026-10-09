import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1714 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1714", ") = {\n    SEE = ", "1714", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_add_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1714 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "110001101110", .any 10], 1714, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_add_simd_decode"⟩
theorem checked1714 : check raw1714 clause1714 = true := by rfl
def row1714 : Row := ⟨1714, 3208641536, 238139392⟩
theorem derived1714 : clause1714.row = row1714 := by rfl
def entry1714 : CheckedRow := ⟨raw1714, clause1714, row1714, checked1714, derived1714⟩

def raw1715 : List String := ["function clause decode64 ((", "0b", "0101111011111000110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1715", ") = {\n    SEE = ", "1715", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "a", ", ", "U", ")\n}\n"]
def clause1715 : Clause := ⟨[.fixed "0101111011111000110110", .any 10], 1715, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode"⟩
theorem checked1715 : check raw1715 clause1715 = true := by rfl
def row1715 : Row := ⟨1715, 4294966272, 1593366528⟩
theorem derived1715 : clause1715.row = row1715 := by rfl
def entry1715 : CheckedRow := ⟨raw1715, clause1715, row1715, checked1715, derived1715⟩

def raw1716 : List String := ["function clause decode64 ((", "0b", "01111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1716", ") = {\n    SEE = ", "1716", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1716 : Clause := ⟨[.fixed "01111000", .any 2, .fixed "1", .any 5, .fixed "000100", .any 10], 1716, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1716 : check raw1716 clause1716 = true := by rfl
def row1716 : Row := ⟨1716, 4280351744, 2015367168⟩
theorem derived1716 : clause1716.row = row1716 := by rfl
def entry1716 : CheckedRow := ⟨raw1716, clause1716, row1716, checked1716, derived1716⟩

def raw1717 : List String := ["function clause decode64 ((", "0b", "00111000001", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1717", ") = {\n    SEE = ", "1717", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_register_memory_single_general_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1717 : Clause := ⟨[.fixed "00111000001", .any 9, .fixed "10", .any 10], 1717, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_register_memory_single_general_register__decode"⟩
theorem checked1717 : check raw1717 clause1717 = true := by rfl
def row1717 : Row := ⟨1717, 4292873216, 941623296⟩
theorem derived1717 : clause1717.row = row1717 := by rfl
def entry1717 : CheckedRow := ⟨raw1717, clause1717, row1717, checked1717, derived1717⟩

def raw1718 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1718", ") = {\n    SEE = ", "1718", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1718 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "100000101110", .any 10], 1718, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_diffneg_int_sisd_decode"⟩
theorem checked1718 : check raw1718 clause1718 = true := by rfl
def row1718 : Row := ⟨1718, 4282383360, 1579202560⟩
theorem derived1718 : clause1718.row = row1718 := by rfl
def entry1718 : CheckedRow := ⟨raw1718, clause1718, row1718, checked1718, derived1718⟩

def raw1719 : List String := ["function clause decode64 ((", "0b", "01111110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1719", ") = {\n    SEE = ", "1719", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ")\n}\n"]
def clause1719 : Clause := ⟨[.fixed "01111110110", .any 5, .fixed "000101", .any 10], 1719, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_sub_fp16_sisd_decode"⟩
theorem checked1719 : check raw1719 clause1719 = true := by rfl
def row1719 : Row := ⟨1719, 4292934656, 2126517248⟩
theorem derived1719 : clause1719.row = row1719 := by rfl
def entry1719 : CheckedRow := ⟨raw1719, clause1719, row1719, checked1719, derived1719⟩

def raw1720 : List String := ["function clause decode64 ((", "0b", "0100111000101000011110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1720", ") = {\n    SEE = ", "1720", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "D", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_aes_mix_decode", "(", "Rd", ", ", "Rn", ", ", "D", ", ", "size", ")\n}\n"]
def clause1720 : Clause := ⟨[.fixed "0100111000101000011110", .any 10], 1720, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"D", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_aes_mix_decode"⟩
theorem checked1720 : check raw1720 clause1720 = true := by rfl
def row1720 : Row := ⟨1720, 4294966272, 1311275008⟩
theorem derived1720 : clause1720.row = row1720 := by rfl
def entry1720 : CheckedRow := ⟨raw1720, clause1720, row1720, checked1720, derived1720⟩

def raw1721 : List String := ["function clause decode64 ((", "0b", "00111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1721", ") = {\n    SEE = ", "1721", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_swp_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1721 : Clause := ⟨[.fixed "00111000", .any 2, .fixed "1", .any 5, .fixed "100000", .any 10], 1721, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_swp_decode"⟩
theorem checked1721 : check raw1721 clause1721 = true := by rfl
def row1721 : Row := ⟨1721, 4280351744, 941654016⟩
theorem derived1721 : clause1721.row = row1721 := by rfl
def entry1721 : CheckedRow := ⟨raw1721, clause1721, row1721, checked1721, derived1721⟩

def entries86 : List CheckedRow := [entry1714, entry1715, entry1716, entry1717, entry1718, entry1719, entry1720, entry1721]
def rows86 : List Row := [row1714, row1715, row1716, row1717, row1718, row1719, row1720, row1721]
theorem indices86 : rows86.map Row.index = [1714, 1715, 1716, 1717, 1718, 1719, 1720, 1721] := by rfl
theorem bound86 : entries86.map CheckedRow.row = rows86 := by rfl
theorem choices_and_86 : choices rows86 167837696#32 (-1) = [] := by rfl
theorem choices_orr_86 : choices rows86 704708608#32 (-1) = [] := by rfl
theorem choices_eor_86 : choices rows86 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_86 : choices rows86 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
