import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1234 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1234", ") = {\n    SEE = ", "1234", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_permute_transpose_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "size", ", ", "Q", ")\n}\n"]
def clause1234 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "0", .any 5, .fixed "011010", .any 10], 1234, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_permute_transpose_decode"⟩
theorem checked1234 : check raw1234 clause1234 = true := by rfl
def row1234 : Row := ⟨1234, 3206609920, 234907648⟩
theorem derived1234 : clause1234.row = row1234 := by rfl
def entry1234 : CheckedRow := ⟨raw1234, clause1234, row1234, checked1234, derived1234⟩

def raw1235 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1235", ") = {\n    SEE = ", "1235", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_addsub_long_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1235 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "000000", .any 10], 1235, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_addsub_long_decode"⟩
theorem checked1235 : check raw1235 clause1235 = true := by rfl
def row1235 : Row := ⟨1235, 3206609920, 236978176⟩
theorem derived1235 : clause1235.row = row1235 := by rfl
def entry1235 : CheckedRow := ⟨raw1235, clause1235, row1235, checked1235, derived1235⟩

def raw1236 : List String := ["function clause decode64 ((", "0b", "0111100101", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1236", ") = {\n    SEE = ", "1236", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1236 : Clause := ⟨[.fixed "0111100101", .any 22], 1236, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1236 : check raw1236 clause1236 = true := by rfl
def row1236 : Row := ⟨1236, 4290772992, 2034237440⟩
theorem derived1236 : clause1236.row = row1236 := by rfl
def entry1236 : CheckedRow := ⟨raw1236, clause1236, row1236, checked1236, derived1236⟩

def raw1237 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1237", ") = {\n    SEE = ", "1237", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1237 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "100000110010", .any 10], 1237, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_float_bulk_simd_decode"⟩
theorem checked1237 : check raw1237 clause1237 = true := by rfl
def row1237 : Row := ⟨1237, 3217030144, 782288896⟩
theorem derived1237 : clause1237.row = row1237 := by rfl
def entry1237 : CheckedRow := ⟨raw1237, clause1237, row1237, checked1237, derived1237⟩

def raw1238 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1238", ") = {\n    SEE = ", "1238", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_rightnarrow_nonuniform_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1238 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "100011", .any 10], 1238, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_rightnarrow_nonuniform_sisd_decode"⟩
theorem checked1238 : check raw1238 clause1238 = true := by rfl
def row1238 : Row := ⟨1238, 4286643200, 2130742272⟩
theorem derived1238 : clause1238.row = row1238 := by rfl
def entry1238 : CheckedRow := ⟨raw1238, clause1238, row1238, checked1238, derived1238⟩

def raw1239 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111011111000111010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1239", ") = {\n    SEE = ", "1239", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_fp16_lessthan_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1239 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111011111000111010", .any 10], 1239, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_fp16_lessthan_simd_decode"⟩
theorem checked1239 : check raw1239 clause1239 = true := by rfl
def row1239 : Row := ⟨1239, 3221224448, 251193344⟩
theorem derived1239 : clause1239.row = row1239 := by rfl
def entry1239 : CheckedRow := ⟨raw1239, clause1239, row1239, checked1239, derived1239⟩

def raw1240 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001000011", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1240", ") = {\n    SEE = ", "1240", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_exclusive_pair_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "sz", ")\n}\n"]
def clause1240 : Clause := ⟨[.fixed "1", .any 1, .fixed "001000011", .any 5, .fixed "0", .any 15], 1240, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"sz", 1, 30, 30, true⟩], "memory_exclusive_pair_decode"⟩
theorem checked1240 : check raw1240 clause1240 = true := by rfl
def row1240 : Row := ⟨1240, 3219161088, 2287992832⟩
theorem derived1240 : clause1240.row = row1240 := by rfl
def entry1240 : CheckedRow := ⟨raw1240, clause1240, row1240, checked1240, derived1240⟩

def raw1241 : List String := ["function clause decode64 ((", "0b", "10111000100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1241", ") = {\n    SEE = ", "1241", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1241 : Clause := ⟨[.fixed "10111000100", .any 9, .fixed "10", .any 10], 1241, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode"⟩
theorem checked1241 : check raw1241 clause1241 = true := by rfl
def row1241 : Row := ⟨1241, 4292873216, 3095398400⟩
theorem derived1241 : clause1241.row = row1241 := by rfl
def entry1241 : CheckedRow := ⟨raw1241, clause1241, row1241, checked1241, derived1241⟩

def entries26 : List CheckedRow := [entry1234, entry1235, entry1236, entry1237, entry1238, entry1239, entry1240, entry1241]
def rows26 : List Row := [row1234, row1235, row1236, row1237, row1238, row1239, row1240, row1241]
theorem indices26 : rows26.map Row.index = [1234, 1235, 1236, 1237, 1238, 1239, 1240, 1241] := by rfl
theorem bound26 : entries26.map CheckedRow.row = rows26 := by rfl
theorem choices_and_26 : choices rows26 167837696#32 (-1) = [] := by rfl
theorem choices_orr_26 : choices rows26 704708608#32 (-1) = [] := by rfl
theorem choices_eor_26 : choices rows26 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_26 : choices rows26 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
