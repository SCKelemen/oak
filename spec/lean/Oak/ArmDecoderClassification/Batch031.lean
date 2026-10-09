import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1274 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1274", ") = {\n    SEE = ", "1274", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_right_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1274 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "001101", .any 10], 1274, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_right_simd_decode"⟩
theorem checked1274 : check raw1274 clause1274 = true := by rfl
def row1274 : Row := ⟨1274, 3212901376, 251671552⟩
theorem derived1274 : clause1274.row = row1274 := by rfl
def entry1274 : CheckedRow := ⟨raw1274, clause1274, row1274, checked1274, derived1274⟩

def raw1275 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "010001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1275", ") = {\n    SEE = ", "1275", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_rightinsert_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1275 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "010001", .any 10], 1275, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_rightinsert_simd_decode"⟩
theorem checked1275 : check raw1275 clause1275 = true := by rfl
def row1275 : Row := ⟨1275, 3212901376, 788546560⟩
theorem derived1275 : clause1275.row = row1275 := by rfl
def entry1275 : CheckedRow := ⟨raw1275, clause1275, row1275, checked1275, derived1275⟩

def raw1276 : List String := ["function clause decode64 ((", "0b", "110110101100000100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1276", ") = {\n    SEE = ", "1276", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_autda_dp_1src_decode", "(", "Rd", ", ", "Rn", ", ", "Z", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1276 : Clause := ⟨[.fixed "110110101100000100", .any 1, .fixed "110", .any 10], 1276, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Z", 1, 13, 13, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_autda_dp_1src_decode"⟩
theorem checked1276 : check raw1276 clause1276 = true := by rfl
def row1276 : Row := ⟨1276, 4294958080, 3670087680⟩
theorem derived1276 : clause1276.row = row1276 := by rfl
def entry1276 : CheckedRow := ⟨raw1276, clause1276, row1276, checked1276, derived1276⟩

def raw1277 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "11100100", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1277", ") = {\n    SEE = ", "1277", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1277 : Clause := ⟨[.fixed "1", .any 1, .fixed "11100100", .any 22], 1277, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1277 : check raw1277 clause1277 = true := by rfl
def row1277 : Row := ⟨1277, 3217031168, 3103784960⟩
theorem derived1277 : clause1277.row = row1277 := by rfl
def entry1277 : CheckedRow := ⟨raw1277, clause1277, row1277, checked1277, derived1277⟩

def raw1278 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1278", ") = {\n    SEE = ", "1278", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1278 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "100001101010", .any 10], 1278, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_simd_decode"⟩
theorem checked1278 : check raw1278 clause1278 = true := by rfl
def row1278 : Row := ⟨1278, 3217030144, 245475328⟩
theorem derived1278 : clause1278.row = row1278 := by rfl
def entry1278 : CheckedRow := ⟨raw1278, clause1278, row1278, checked1278, derived1278⟩

def raw1279 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101101", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1279", ") = {\n    SEE = ", "1279", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1279 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101101", .any 7, .fixed "1", .any 13], 1279, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1279 : check raw1279 clause1279 = true := by rfl
def row1279 : Row := ⟨1279, 3219136512, 228597760⟩
theorem derived1279 : clause1279.row = row1279 := by rfl
def entry1279 : CheckedRow := ⟨raw1279, clause1279, row1279, checked1279, derived1279⟩

def raw1280 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1280", ") = {\n    SEE = ", "1280", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_right_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1280 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "000101", .any 10], 1280, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_right_simd_decode"⟩
theorem checked1280 : check raw1280 clause1280 = true := by rfl
def row1280 : Row := ⟨1280, 3212901376, 788534272⟩
theorem derived1280 : clause1280.row = row1280 := by rfl
def entry1280 : CheckedRow := ⟨raw1280, clause1280, row1280, checked1280, derived1280⟩

def raw1281 : List String := ["function clause decode64 ((", "0b", "010111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1281", ") = {\n    SEE = ", "1281", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_right_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1281 : Clause := ⟨[.fixed "010111110", .any 7, .fixed "001001", .any 10], 1281, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_right_sisd_decode"⟩
theorem checked1281 : check raw1281 clause1281 = true := by rfl
def row1281 : Row := ⟨1281, 4286643200, 1593844736⟩
theorem derived1281 : clause1281.row = row1281 := by rfl
def entry1281 : CheckedRow := ⟨raw1281, clause1281, row1281, checked1281, derived1281⟩

def entries31 : List CheckedRow := [entry1274, entry1275, entry1276, entry1277, entry1278, entry1279, entry1280, entry1281]
def rows31 : List Row := [row1274, row1275, row1276, row1277, row1278, row1279, row1280, row1281]
theorem indices31 : rows31.map Row.index = [1274, 1275, 1276, 1277, 1278, 1279, 1280, 1281] := by rfl
theorem bound31 : entries31.map CheckedRow.row = rows31 := by rfl
theorem choices_and_31 : choices rows31 167837696#32 (-1) = [] := by rfl
theorem choices_orr_31 : choices rows31 704708608#32 (-1) = [] := by rfl
theorem choices_eor_31 : choices rows31 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_31 : choices rows31 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
