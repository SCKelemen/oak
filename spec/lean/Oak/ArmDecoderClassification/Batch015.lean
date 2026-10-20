import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1146 : List String := ["function clause decode64 ((", "0b", "01111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1146", ") = {\n    SEE = ", "1146", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1146 : Clause := ⟨[.fixed "01111000", .any 2, .fixed "1", .any 5, .fixed "011100", .any 10], 1146, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1146 : check raw1146 clause1146 = true := by rfl
def row1146 : Row := ⟨1146, 4280351744, 2015391744⟩
theorem derived1146 : clause1146.row = row1146 := by rfl
def entry1146 : CheckedRow := ⟨raw1146, clause1146, row1146, checked1146, derived1146⟩

def raw1147 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001000001", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1147", ") = {\n    SEE = ", "1147", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_exclusive_pair_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "sz", ")\n}\n"]
def clause1147 : Clause := ⟨[.fixed "1", .any 1, .fixed "001000001", .any 5, .fixed "1", .any 15], 1147, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"sz", 1, 30, 30, true⟩], "memory_exclusive_pair_decode"⟩
theorem checked1147 : check raw1147 clause1147 = true := by rfl
def row1147 : Row := ⟨1147, 3219161088, 2283831296⟩
theorem derived1147 : clause1147.row = row1147 := by rfl
def entry1147 : CheckedRow := ⟨raw1147, clause1147, row1147, checked1147, derived1147⟩

def raw1148 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1148", ") = {\n    SEE = ", "1148", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "eq", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "eq", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1148 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "001111", .any 10], 1148, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"eq", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_int_simd_decode"⟩
theorem checked1148 : check raw1148 clause1148 = true := by rfl
def row1148 : Row := ⟨1148, 3206609920, 773864448⟩
theorem derived1148 : clause1148.row = row1148 := by rfl
def entry1148 : CheckedRow := ⟨raw1148, clause1148, row1148, checked1148, derived1148⟩

def raw1149 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1149", ") = {\n    SEE = ", "1149", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm4_0_", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "imm4_1_", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "imm4_3_2_", " : bits(", "2", ") = ", "op_code[", "14", " .. ", "13", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_integer_move_unsigned_decode", "(", "Rd", ", ", "Rn", ", ", "imm4_0_", ", ", "imm4_1_", ", ", "imm4_3_2_", ", ", "imm5", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1149 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110000", .any 5, .fixed "001111", .any 10], 1149, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm4_0_", 1, 11, 11, true⟩, ⟨"imm4_1_", 1, 12, 12, true⟩, ⟨"imm4_3_2_", 2, 14, 13, false⟩, ⟨"imm5", 5, 20, 16, false⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_integer_move_unsigned_decode"⟩
theorem checked1149 : check raw1149 clause1149 = true := by rfl
def row1149 : Row := ⟨1149, 3219192832, 234896384⟩
theorem derived1149 : clause1149.row = row1149 := by rfl
def entry1149 : CheckedRow := ⟨raw1149, clause1149, row1149, checked1149, derived1149⟩

def raw1150 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1150", ") = {\n    SEE = ", "1150", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "16", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_intmax_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1150 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "110001101010", .any 10], 1150, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 16, 16, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_intmax_decode"⟩
theorem checked1150 : check raw1150 clause1150 = true := by rfl
def row1150 : Row := ⟨1150, 3208641536, 775006208⟩
theorem derived1150 : clause1150.row = row1150 := by rfl
def entry1150 : CheckedRow := ⟨raw1150, clause1150, row1150, checked1150, derived1150⟩

def raw1151 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111011111001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1151", ") = {\n    SEE = ", "1151", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1151 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111011111001101110", .any 10], 1151, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode"⟩
theorem checked1151 : check raw1151 clause1151 = true := by rfl
def row1151 : Row := ⟨1151, 3221224448, 788117504⟩
theorem derived1151 : clause1151.row = row1151 := by rfl
def entry1151 : CheckedRow := ⟨raw1151, clause1151, row1151, checked1151, derived1151⟩

def raw1152 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1152", ") = {\n    SEE = ", "1152", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1152 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "1", .any 5, .fixed "010111", .any 10], 1152, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_shift_sisd_decode"⟩
theorem checked1152 : check raw1152 clause1152 = true := by rfl
def row1152 : Row := ⟨1152, 4280351744, 2116049920⟩
theorem derived1152 : clause1152.row = row1152 := by rfl
def entry1152 : CheckedRow := ⟨raw1152, clause1152, row1152, checked1152, derived1152⟩

def raw1153 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001100110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1153", ") = {\n    SEE = ", "1153", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1153 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "100001100110", .any 10], 1153, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_round_decode"⟩
theorem checked1153 : check raw1153 clause1153 = true := by rfl
def row1153 : Row := ⟨1153, 3217030144, 773953536⟩
theorem derived1153 : clause1153.row = row1153 := by rfl
def entry1153 : CheckedRow := ⟨raw1153, clause1153, row1153, checked1153, derived1153⟩

def entries15 : List CheckedRow := [entry1146, entry1147, entry1148, entry1149, entry1150, entry1151, entry1152, entry1153]
def rows15 : List Row := [row1146, row1147, row1148, row1149, row1150, row1151, row1152, row1153]
theorem indices15 : rows15.map Row.index = [1146, 1147, 1148, 1149, 1150, 1151, 1152, 1153] := by rfl
theorem bound15 : entries15.map CheckedRow.row = rows15 := by rfl
theorem choices_and_15 : choices rows15 167837696#32 (-1) = [] := by rfl
theorem choices_orr_15 : choices rows15 704708608#32 (-1) = [] := by rfl
theorem choices_eor_15 : choices rows15 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_15 : choices rows15 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
