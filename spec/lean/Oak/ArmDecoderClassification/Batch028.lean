import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1250 : List String := ["function clause decode64 ((", "0b", "011111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1250", ") = {\n    SEE = ", "1250", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1250 : Clause := ⟨[.fixed "011111100", .any 1, .fixed "100001110010", .any 10], 1250, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode"⟩
theorem checked1250 : check raw1250 clause1250 = true := by rfl
def row1250 : Row := ⟨1250, 4290771968, 2116143104⟩
theorem derived1250 : clause1250.row = row1250 := by rfl
def entry1250 : CheckedRow := ⟨raw1250, clause1250, row1250, checked1250, derived1250⟩

def raw1251 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "011000", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1251", ") = {\n    SEE = ", "1251", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm19", " : bits(", "19", ") = ", "op_code[", "23", " .. ", "5", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_literal_general_decode", "(", "Rt", ", ", "imm19", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1251 : Clause := ⟨[.fixed "0", .any 1, .fixed "011000", .any 24], 1251, [⟨"Rt", 5, 4, 0, false⟩, ⟨"imm19", 19, 23, 5, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_literal_general_decode"⟩
theorem checked1251 : check raw1251 clause1251 = true := by rfl
def row1251 : Row := ⟨1251, 3204448256, 402653184⟩
theorem derived1251 : clause1251.row = row1251 := by rfl
def entry1251 : CheckedRow := ⟨raw1251, clause1251, row1251, checked1251, derived1251⟩

def raw1252 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101010000001110", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1252", ") = {\n    SEE = ", "1252", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1252 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101010000001110", .any 12], 1252, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1252 : check raw1252 clause1252 = true := by rfl
def row1252 : Row := ⟨1252, 3221221376, 222355456⟩
theorem derived1252 : clause1252.row = row1252 := by rfl
def entry1252 : CheckedRow := ⟨raw1252, clause1252, row1252, checked1252, derived1252⟩

def raw1253 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001000001", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1253", ") = {\n    SEE = ", "1253", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_exclusive_pair_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "sz", ")\n}\n"]
def clause1253 : Clause := ⟨[.fixed "1", .any 1, .fixed "001000001", .any 5, .fixed "0", .any 15], 1253, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"sz", 1, 30, 30, true⟩], "memory_exclusive_pair_decode"⟩
theorem checked1253 : check raw1253 clause1253 = true := by rfl
def row1253 : Row := ⟨1253, 3219161088, 2283798528⟩
theorem derived1253 : clause1253.row = row1253 := by rfl
def entry1253 : CheckedRow := ⟨raw1253, clause1253, row1253, checked1253, derived1253⟩

def raw1254 : List String := ["function clause decode64 ((", "0b", "011110001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1254", ") = {\n    SEE = ", "1254", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1254 : Clause := ⟨[.fixed "011110001", .any 1, .fixed "0", .any 9, .fixed "01", .any 10], 1254, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1254 : check raw1254 clause1254 = true := by rfl
def row1254 : Row := ⟨1254, 4288678912, 2021655552⟩
theorem derived1254 : clause1254.row = row1254 := by rfl
def entry1254 : CheckedRow := ⟨raw1254, clause1254, row1254, checked1254, derived1254⟩

def raw1255 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "010101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1255", ") = {\n    SEE = ", "1255", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_left_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1255 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "010101", .any 10], 1255, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_left_simd_decode"⟩
theorem checked1255 : check raw1255 clause1255 = true := by rfl
def row1255 : Row := ⟨1255, 3212901376, 251679744⟩
theorem derived1255 : clause1255.row = row1255 := by rfl
def entry1255 : CheckedRow := ⟨raw1255, clause1255, row1255, checked1255, derived1255⟩

def raw1256 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0110001", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1256", ") = {\n    SEE = ", "1256", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_immediate_decode", "(", "Rd", ", ", "Rn", ", ", "imm12", ", ", "shift", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1256 : Clause := ⟨[.any 1, .fixed "0110001", .any 24], 1256, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_immediate_decode"⟩
theorem checked1256 : check raw1256 clause1256 = true := by rfl
def row1256 : Row := ⟨1256, 2130706432, 822083584⟩
theorem derived1256 : clause1256.row = row1256 := by rfl
def entry1256 : CheckedRow := ⟨raw1256, clause1256, row1256, checked1256, derived1256⟩

def raw1257 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1257", ") = {\n    SEE = ", "1257", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1257 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "010001", .any 10], 1257, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_shift_sisd_decode"⟩
theorem checked1257 : check raw1257 clause1257 = true := by rfl
def row1257 : Row := ⟨1257, 4280351744, 1579172864⟩
theorem derived1257 : clause1257.row = row1257 := by rfl
def entry1257 : CheckedRow := ⟨raw1257, clause1257, row1257, checked1257, derived1257⟩

def entries28 : List CheckedRow := [entry1250, entry1251, entry1252, entry1253, entry1254, entry1255, entry1256, entry1257]
def rows28 : List Row := [row1250, row1251, row1252, row1253, row1254, row1255, row1256, row1257]
theorem indices28 : rows28.map Row.index = [1250, 1251, 1252, 1253, 1254, 1255, 1256, 1257] := by rfl
theorem bound28 : entries28.map CheckedRow.row = rows28 := by rfl
theorem choices_and_28 : choices rows28 167837696#32 (-1) = [] := by rfl
theorem choices_orr_28 : choices rows28 704708608#32 (-1) = [] := by rfl
theorem choices_eor_28 : choices rows28 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_28 : choices rows28 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
