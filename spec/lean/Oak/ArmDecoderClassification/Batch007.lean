import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1082 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1082", ") = {\n    SEE = ", "1082", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_conv_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1082 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "111001", .any 10], 1082, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_conv_int_sisd_decode"⟩
theorem checked1082 : check raw1082 clause1082 = true := by rfl
def row1082 : Row := ⟨1082, 4286643200, 2130764800⟩
theorem derived1082 : clause1082.row = row1082 := by rfl
def entry1082 : CheckedRow := ⟨raw1082, clause1082, row1082, checked1082, derived1082⟩

def raw1083 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0000", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1083", ") = {\n    SEE = ", "1083", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "Rm", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1083 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100110", .any 5, .fixed "0000", .any 12], 1083, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_postinc_memory_vector_multiple_nowb__decode"⟩
theorem checked1083 : check raw1083 clause1083 = true := by rfl
def row1083 : Row := ⟨1083, 3219189760, 213909504⟩
theorem derived1083 : clause1083.row = row1083 := by rfl
def entry1083 : CheckedRow := ⟨raw1083, clause1083, row1083, checked1083, derived1083⟩

def raw1084 : List String := ["function clause decode64 ((", "0b", "01111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1084", ") = {\n    SEE = ", "1084", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_swp_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1084 : Clause := ⟨[.fixed "01111000", .any 2, .fixed "1", .any 5, .fixed "100000", .any 10], 1084, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_swp_decode"⟩
theorem checked1084 : check raw1084 clause1084 = true := by rfl
def row1084 : Row := ⟨1084, 4280351744, 2015395840⟩
theorem derived1084 : clause1084.row = row1084 := by rfl
def entry1084 : CheckedRow := ⟨raw1084, clause1084, row1084, checked1084, derived1084⟩

def raw1085 : List String := ["function clause decode64 ((", "0b", "010111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1085", ") = {\n    SEE = ", "1085", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_right_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1085 : Clause := ⟨[.fixed "010111110", .any 7, .fixed "000101", .any 10], 1085, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_right_sisd_decode"⟩
theorem checked1085 : check raw1085 clause1085 = true := by rfl
def row1085 : Row := ⟨1085, 4286643200, 1593840640⟩
theorem derived1085 : clause1085.row = row1085 := by rfl
def entry1085 : CheckedRow := ⟨raw1085, clause1085, row1085, checked1085, derived1085⟩

def raw1086 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0111010010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "4", ")", " as op_code) if SEE < ", "1086", ") = {\n    SEE = ", "1086", ";\n", "    ", "nzcv", " : bits(", "4", ") = ", "op_code[", "3", " .. ", "0", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "4", "]]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_conditional_compare_immediate_decode", "(", "nzcv", ", ", "o3", ", ", "Rn", ", ", "o2", ", ", "cond", ", ", "imm5", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1086 : Clause := ⟨[.any 1, .fixed "0111010010", .any 9, .fixed "10", .any 5, .fixed "0", .any 4], 1086, [⟨"nzcv", 4, 3, 0, false⟩, ⟨"o3", 1, 4, 4, true⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o2", 1, 10, 10, true⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"imm5", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_conditional_compare_immediate_decode"⟩
theorem checked1086 : check raw1086 clause1086 = true := by rfl
def row1086 : Row := ⟨1086, 2145389584, 977274880⟩
theorem derived1086 : clause1086.row = row1086 := by rfl
def entry1086 : CheckedRow := ⟨raw1086, clause1086, row1086, checked1086, derived1086⟩

def raw1087 : List String := ["function clause decode64 ((", "0b", "010111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1087", ") = {\n    SEE = ", "1087", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1087 : Clause := ⟨[.fixed "010111100", .any 1, .fixed "100001101110", .any 10], 1087, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode"⟩
theorem checked1087 : check raw1087 clause1087 = true := by rfl
def row1087 : Row := ⟨1087, 4290771968, 1579268096⟩
theorem derived1087 : clause1087.row = row1087 := by rfl
def entry1087 : CheckedRow := ⟨raw1087, clause1087, row1087, checked1087, derived1087⟩

def raw1088 : List String := ["function clause decode64 ((", "0b", "10111000100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1088", ") = {\n    SEE = ", "1088", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1088 : Clause := ⟨[.fixed "10111000100", .any 9, .fixed "01", .any 10], 1088, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1088 : check raw1088 clause1088 = true := by rfl
def row1088 : Row := ⟨1088, 4292873216, 3095397376⟩
theorem derived1088 : clause1088.row = row1088 := by rfl
def entry1088 : CheckedRow := ⟨raw1088, clause1088, row1088, checked1088, derived1088⟩

def raw1089 : List String := ["function clause decode64 ((", "0b", "01111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1089", ") = {\n    SEE = ", "1089", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1089 : Clause := ⟨[.fixed "01111000000", .any 9, .fixed "10", .any 10], 1089, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode"⟩
theorem checked1089 : check raw1089 clause1089 = true := by rfl
def row1089 : Row := ⟨1089, 4292873216, 2013267968⟩
theorem derived1089 : clause1089.row = row1089 := by rfl
def entry1089 : CheckedRow := ⟨raw1089, clause1089, row1089, checked1089, derived1089⟩

def entries7 : List CheckedRow := [entry1082, entry1083, entry1084, entry1085, entry1086, entry1087, entry1088, entry1089]
def rows7 : List Row := [row1082, row1083, row1084, row1085, row1086, row1087, row1088, row1089]
theorem indices7 : rows7.map Row.index = [1082, 1083, 1084, 1085, 1086, 1087, 1088, 1089] := by rfl
theorem bound7 : entries7.map CheckedRow.row = rows7 := by rfl
theorem choices_and_7 : choices rows7 167837696#32 (-1) = [] := by rfl
theorem choices_orr_7 : choices rows7 704708608#32 (-1) = [] := by rfl
theorem choices_eor_7 : choices rows7 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_7 : choices rows7 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
