import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1426 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1426", ") = {\n    SEE = ", "1426", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp16_fused_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1426 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110010", .any 5, .fixed "000011", .any 10], 1426, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_fp16_fused_decode"⟩
theorem checked1426 : check raw1426 clause1426 = true := by rfl
def row1426 : Row := ⟨1426, 3219192832, 239078400⟩
theorem derived1426 : clause1426.row = row1426 := by rfl
def entry1426 : CheckedRow := ⟨raw1426, clause1426, row1426, checked1426, derived1426⟩

def raw1427 : List String := ["function clause decode64 ((", "0b", "001110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1427", ") = {\n    SEE = ", "1427", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1427 : Clause := ⟨[.fixed "001110000", .any 1, .fixed "1", .any 5, .fixed "001000", .any 5, .fixed "11111"], 1427, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1427 : check raw1427 clause1427 = true := by rfl
def row1427 : Row := ⟨1427, 4288740383, 941629471⟩
theorem derived1427 : clause1427.row = row1427 := by rfl
def entry1427 : CheckedRow := ⟨raw1427, clause1427, row1427, checked1427, derived1427⟩

def raw1428 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00110101100000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1428", ") = {\n    SEE = ", "1428", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1428 : Clause := ⟨[.fixed "0", .any 1, .fixed "00110101100000", .any 2, .fixed "0", .any 13], 1428, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1428 : check raw1428 clause1428 = true := by rfl
def row1428 : Row := ⟨1428, 3221168128, 224395264⟩
theorem derived1428 : clause1428.row = row1428 := by rfl
def entry1428 : CheckedRow := ⟨raw1428, clause1428, row1428, checked1428, derived1428⟩

def raw1429 : List String := ["function clause decode64 ((", "0b", "00111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1429", ") = {\n    SEE = ", "1429", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1429 : Clause := ⟨[.fixed "00111000000", .any 9, .fixed "10", .any 10], 1429, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode"⟩
theorem checked1429 : check raw1429 clause1429 = true := by rfl
def row1429 : Row := ⟨1429, 4292873216, 939526144⟩
theorem derived1429 : clause1429.row = row1429 := by rfl
def entry1429 : CheckedRow := ⟨raw1429, clause1429, row1429, checked1429, derived1429⟩

def raw1430 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1430", ") = {\n    SEE = ", "1430", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_int_product_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1430 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "100111", .any 10], 1430, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_int_product_decode"⟩
theorem checked1430 : check raw1430 clause1430 = true := by rfl
def row1430 : Row := ⟨1430, 3206609920, 237018112⟩
theorem derived1430 : clause1430.row = row1430 := by rfl
def entry1430 : CheckedRow := ⟨raw1430, clause1430, row1430, checked1430, derived1430⟩

def raw1431 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1431", ") = {\n    SEE = ", "1431", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_right_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1431 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "001001", .any 10], 1431, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_right_simd_decode"⟩
theorem checked1431 : check raw1431 clause1431 = true := by rfl
def row1431 : Row := ⟨1431, 3212901376, 788538368⟩
theorem derived1431 : clause1431.row = row1431 := by rfl
def entry1431 : CheckedRow := ⟨raw1431, clause1431, row1431, checked1431, derived1431⟩

def raw1432 : List String := ["function clause decode64 ((", "0b", "010111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1432", ") = {\n    SEE = ", "1432", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_right_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1432 : Clause := ⟨[.fixed "010111110", .any 7, .fixed "000001", .any 10], 1432, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_right_sisd_decode"⟩
theorem checked1432 : check raw1432 clause1432 = true := by rfl
def row1432 : Row := ⟨1432, 4286643200, 1593836544⟩
theorem derived1432 : clause1432.row = row1432 := by rfl
def entry1432 : CheckedRow := ⟨raw1432, clause1432, row1432, checked1432, derived1432⟩

def raw1433 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1433", ") = {\n    SEE = ", "1433", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_conditional_select_decode", "(", "Rd", ", ", "Rn", ", ", "o2", ", ", "cond", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1433 : Clause := ⟨[.any 1, .fixed "0011010100", .any 9, .fixed "00", .any 10], 1433, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o2", 1, 10, 10, true⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_conditional_select_decode"⟩
theorem checked1433 : check raw1433 clause1433 = true := by rfl
def row1433 : Row := ⟨1433, 2145389568, 444596224⟩
theorem derived1433 : clause1433.row = row1433 := by rfl
def entry1433 : CheckedRow := ⟨raw1433, clause1433, row1433, checked1433, derived1433⟩

def entries50 : List CheckedRow := [entry1426, entry1427, entry1428, entry1429, entry1430, entry1431, entry1432, entry1433]
def rows50 : List Row := [row1426, row1427, row1428, row1429, row1430, row1431, row1432, row1433]
theorem indices50 : rows50.map Row.index = [1426, 1427, 1428, 1429, 1430, 1431, 1432, 1433] := by rfl
theorem bound50 : entries50.map CheckedRow.row = rows50 := by rfl
theorem choices_and_50 : choices rows50 167837696#32 (-1) = [] := by rfl
theorem choices_orr_50 : choices rows50 704708608#32 (-1) = [] := by rfl
theorem choices_eor_50 : choices rows50 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_50 : choices rows50 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
