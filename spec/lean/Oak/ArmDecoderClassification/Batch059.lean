import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1498 : List String := ["function clause decode64 ((", "0b", "01010100", " @ ", "_ : bits(", "19", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "4", ")", " as op_code) if SEE < ", "1498", ") = {\n    SEE = ", "1498", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "3", " .. ", "0", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "4", "]]", ";\n", "    ", "imm19", " : bits(", "19", ") = ", "op_code[", "23", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "branch_conditional_cond_decode", "(", "cond", ", ", "o0", ", ", "imm19", ", ", "o1", ")\n}\n"]
def clause1498 : Clause := ⟨[.fixed "01010100", .any 19, .fixed "0", .any 4], 1498, [⟨"cond", 4, 3, 0, false⟩, ⟨"o0", 1, 4, 4, true⟩, ⟨"imm19", 19, 23, 5, false⟩, ⟨"o1", 1, 24, 24, true⟩], "branch_conditional_cond_decode"⟩
theorem checked1498 : check raw1498 clause1498 = true := by rfl
def row1498 : Row := ⟨1498, 4278190096, 1409286144⟩
theorem derived1498 : clause1498.row = row1498 := by rfl
def entry1498 : CheckedRow := ⟨raw1498, clause1498, row1498, checked1498, derived1498⟩

def raw1499 : List String := ["function clause decode64 ((", "0b", "0101111100", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "1001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1499", ") = {\n    SEE = ", "1499", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1499 : Clause := ⟨[.fixed "0101111100", .any 6, .fixed "1001", .any 1, .fixed "0", .any 10], 1499, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mul_fp16_sisd_decode"⟩
theorem checked1499 : check raw1499 clause1499 = true := by rfl
def row1499 : Row := ⟨1499, 4290835456, 1593872384⟩
theorem derived1499 : clause1499.row = row1499 := by rfl
def entry1499 : CheckedRow := ⟨raw1499, clause1499, row1499, checked1499, derived1499⟩

def raw1500 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "011001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1500", ") = {\n    SEE = ", "1500", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_leftsat_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1500 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "011001", .any 10], 1500, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_leftsat_simd_decode"⟩
theorem checked1500 : check raw1500 clause1500 = true := by rfl
def row1500 : Row := ⟨1500, 3212901376, 788554752⟩
theorem derived1500 : clause1500.row = row1500 := by rfl
def entry1500 : CheckedRow := ⟨raw1500, clause1500, row1500, checked1500, derived1500⟩

def raw1501 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1501", ") = {\n    SEE = ", "1501", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_simdfp_register_memory_single_simdfp_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1501 : Clause := ⟨[.any 2, .fixed "111100", .any 1, .fixed "11", .any 9, .fixed "10", .any 10], 1501, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_simdfp_register_memory_single_simdfp_register__decode"⟩
theorem checked1501 : check raw1501 clause1501 = true := by rfl
def row1501 : Row := ⟨1501, 1063259136, 1012926464⟩
theorem derived1501 : clause1501.row = row1501 := by rfl
def entry1501 : CheckedRow := ⟨raw1501, clause1501, row1501, checked1501, derived1501⟩

def raw1502 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1000", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1502", ") = {\n    SEE = ", "1502", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "Rm", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1502 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100110", .any 5, .fixed "1000", .any 12], 1502, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode"⟩
theorem checked1502 : check raw1502 clause1502 = true := by rfl
def row1502 : Row := ⟨1502, 3219189760, 213942272⟩
theorem derived1502 : clause1502.row = row1502 := by rfl
def entry1502 : CheckedRow := ⟨raw1502, clause1502, row1502, checked1502, derived1502⟩

def raw1503 : List String := ["function clause decode64 ((", "0b", "01001110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1503", ") = {\n    SEE = ", "1503", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm4", " : bits(", "4", ") = ", "op_code[", "14", " .. ", "11", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_integer_insert_decode", "(", "Rd", ", ", "Rn", ", ", "imm4", ", ", "imm5", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1503 : Clause := ⟨[.fixed "01001110000", .any 5, .fixed "000111", .any 10], 1503, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm4", 4, 14, 11, false⟩, ⟨"imm5", 5, 20, 16, false⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_integer_insert_decode"⟩
theorem checked1503 : check raw1503 clause1503 = true := by rfl
def row1503 : Row := ⟨1503, 4292934656, 1308630016⟩
theorem derived1503 : clause1503.row = row1503 := by rfl
def entry1503 : CheckedRow := ⟨raw1503, clause1503, row1503, checked1503, derived1503⟩

def raw1504 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1504", ") = {\n    SEE = ", "1504", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_saturating_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1504 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "000011", .any 10], 1504, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_saturating_simd_decode"⟩
theorem checked1504 : check raw1504 clause1504 = true := by rfl
def row1504 : Row := ⟨1504, 3206609920, 773852160⟩
theorem derived1504 : clause1504.row = row1504 := by rfl
def entry1504 : CheckedRow := ⟨raw1504, clause1504, row1504, checked1504, derived1504⟩

def raw1505 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1505", ") = {\n    SEE = ", "1505", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fpmax_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ")\n}\n"]
def clause1505 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "110000111110", .any 10], 1505, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fpmax_sisd_decode"⟩
theorem checked1505 : check raw1505 clause1505 = true := by rfl
def row1505 : Row := ⟨1505, 4290771968, 2125527040⟩
theorem derived1505 : clause1505.row = row1505 := by rfl
def entry1505 : CheckedRow := ⟨raw1505, clause1505, row1505, checked1505, derived1505⟩

def entries59 : List CheckedRow := [entry1498, entry1499, entry1500, entry1501, entry1502, entry1503, entry1504, entry1505]
def rows59 : List Row := [row1498, row1499, row1500, row1501, row1502, row1503, row1504, row1505]
theorem indices59 : rows59.map Row.index = [1498, 1499, 1500, 1501, 1502, 1503, 1504, 1505] := by rfl
theorem bound59 : entries59.map CheckedRow.row = rows59 := by rfl
theorem choices_and_59 : choices rows59 167837696#32 (-1) = [] := by rfl
theorem choices_orr_59 : choices rows59 704708608#32 (-1) = [] := by rfl
theorem choices_eor_59 : choices rows59 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_59 : choices rows59 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
