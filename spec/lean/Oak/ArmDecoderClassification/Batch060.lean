import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1506 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1506", ") = {\n    SEE = ", "1506", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1506 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "010101", .any 10], 1506, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_shift_sisd_decode"⟩
theorem checked1506 : check raw1506 clause1506 = true := by rfl
def row1506 : Row := ⟨1506, 4280351744, 1579176960⟩
theorem derived1506 : clause1506.row = row1506 := by rfl
def entry1506 : CheckedRow := ⟨raw1506, clause1506, row1506, checked1506, derived1506⟩

def raw1507 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "10110001", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1507", ") = {\n    SEE = ", "1507", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_simdfp_noalloc_memory_pair_simdfp_noalloc__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1507 : Clause := ⟨[.any 2, .fixed "10110001", .any 22], 1507, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_simdfp_noalloc_memory_pair_simdfp_noalloc__decode"⟩
theorem checked1507 : check raw1507 clause1507 = true := by rfl
def row1507 : Row := ⟨1507, 1069547520, 742391808⟩
theorem derived1507 : clause1507.row = row1507 := by rfl
def entry1507 : CheckedRow := ⟨raw1507, clause1507, row1507, checked1507, derived1507⟩

def raw1508 : List String := ["function clause decode64 ((", "0b", "001110001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1508", ") = {\n    SEE = ", "1508", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_register_memory_single_general_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1508 : Clause := ⟨[.fixed "001110001", .any 1, .fixed "1", .any 9, .fixed "10", .any 10], 1508, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_register_memory_single_general_register__decode"⟩
theorem checked1508 : check raw1508 clause1508 = true := by rfl
def row1508 : Row := ⟨1508, 4288678912, 950011904⟩
theorem derived1508 : clause1508.row = row1508 := by rfl
def entry1508 : CheckedRow := ⟨raw1508, clause1508, row1508, checked1508, derived1508⟩

def raw1509 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011111", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1509", ") = {\n    SEE = ", "1509", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_mul_norounding_i_lower_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "S", ", ", "Rm", ", ", "M", ", ", "L", ", ", "sz", ", ", "Q", ")\n}\n"]
def clause1509 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011111", .any 7, .fixed "0", .any 1, .fixed "00", .any 1, .fixed "0", .any 10], 1509, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"S", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_mul_norounding_i_lower_decode"⟩
theorem checked1509 : check raw1509 clause1509 = true := by rfl
def row1509 : Row := ⟨1509, 3212882944, 260046848⟩
theorem derived1509 : clause1509.row = row1509 := by rfl
def entry1509 : CheckedRow := ⟨raw1509, clause1509, row1509, checked1509, derived1509⟩

def raw1510 : List String := ["function clause decode64 ((", "0b", "00011111", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1510", ") = {\n    SEE = ", "1510", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_mul_addsub_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "o1", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1510 : Clause := ⟨[.fixed "00011111", .any 2, .fixed "1", .any 5, .fixed "1", .any 15], 1510, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_mul_addsub_decode"⟩
theorem checked1510 : check raw1510 clause1510 = true := by rfl
def row1510 : Row := ⟨1510, 4280320000, 522223616⟩
theorem derived1510 : clause1510.row = row1510 := by rfl
def entry1510 : CheckedRow := ⟨raw1510, clause1510, row1510, checked1510, derived1510⟩

def raw1511 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1511", ") = {\n    SEE = ", "1511", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "eq", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "eq", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1511 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "001101", .any 10], 1511, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"eq", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_int_sisd_decode"⟩
theorem checked1511 : check raw1511 clause1511 = true := by rfl
def row1511 : Row := ⟨1511, 4280351744, 1579168768⟩
theorem derived1511 : clause1511.row = row1511 := by rfl
def entry1511 : CheckedRow := ⟨raw1511, clause1511, row1511, checked1511, derived1511⟩

def raw1512 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1512", ") = {\n    SEE = ", "1512", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_simdfp_immediate_signed_postidx_memory_single_simdfp_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1512 : Clause := ⟨[.any 2, .fixed "111100", .any 1, .fixed "00", .any 9, .fixed "01", .any 10], 1512, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_simdfp_immediate_signed_postidx_memory_single_simdfp_immediate_signed_postidx__decode"⟩
theorem checked1512 : check raw1512 clause1512 = true := by rfl
def row1512 : Row := ⟨1512, 1063259136, 1006633984⟩
theorem derived1512 : clause1512.row = row1512 := by rfl
def entry1512 : CheckedRow := ⟨raw1512, clause1512, row1512, checked1512, derived1512⟩

def raw1513 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1513", ") = {\n    SEE = ", "1513", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp_1985_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1513 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "1", .any 5, .fixed "111101", .any 10], 1513, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp_1985_decode"⟩
theorem checked1513 : check raw1513 clause1513 = true := by rfl
def row1513 : Row := ⟨1513, 3214998528, 773911552⟩
theorem derived1513 : clause1513.row = row1513 := by rfl
def entry1513 : CheckedRow := ⟨raw1513, clause1513, row1513, checked1513, derived1513⟩

def entries60 : List CheckedRow := [entry1506, entry1507, entry1508, entry1509, entry1510, entry1511, entry1512, entry1513]
def rows60 : List Row := [row1506, row1507, row1508, row1509, row1510, row1511, row1512, row1513]
theorem indices60 : rows60.map Row.index = [1506, 1507, 1508, 1509, 1510, 1511, 1512, 1513] := by rfl
theorem bound60 : entries60.map CheckedRow.row = rows60 := by rfl
theorem choices_and_60 : choices rows60 167837696#32 (-1) = [] := by rfl
theorem choices_orr_60 : choices rows60 704708608#32 (-1) = [] := by rfl
theorem choices_eor_60 : choices rows60 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_60 : choices rows60 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
