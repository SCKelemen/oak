import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1122 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1122", ") = {\n    SEE = ", "1122", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1122 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "100100", .any 10], 1122, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_disparate_mul_dmacc_sisd_decode"⟩
theorem checked1122 : check raw1122 clause1122 = true := by rfl
def row1122 : Row := ⟨1122, 4280351744, 1579192320⟩
theorem derived1122 : clause1122.row = row1122 := by rfl
def entry1122 : CheckedRow := ⟨raw1122, clause1122, row1122, checked1122, derived1122⟩

def raw1123 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1123", ") = {\n    SEE = ", "1123", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_fpmax_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1123 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "110000111110", .any 10], 1123, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_fpmax_simd_decode"⟩
theorem checked1123 : check raw1123 clause1123 = true := by rfl
def row1123 : Row := ⟨1123, 3217030144, 783349760⟩
theorem derived1123 : clause1123.row = row1123 := by rfl
def entry1123 : CheckedRow := ⟨raw1123, clause1123, row1123, checked1123, derived1123⟩

def raw1124 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1124", ") = {\n    SEE = ", "1124", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1124 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110110", .any 5, .fixed "000101", .any 10], 1124, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_sub_fp16_simd_decode"⟩
theorem checked1124 : check raw1124 clause1124 = true := by rfl
def row1124 : Row := ⟨1124, 3219192832, 784339968⟩
theorem derived1124 : clause1124.row = row1124 := by rfl
def entry1124 : CheckedRow := ⟨raw1124, clause1124, row1124, checked1124, derived1124⟩

def raw1125 : List String := ["function clause decode64 ((", "0b", "000010001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "11111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1125", ") = {\n    SEE = ", "1125", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_cas_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1125 : Clause := ⟨[.fixed "000010001", .any 1, .fixed "1", .any 6, .fixed "11111", .any 10], 1125, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_cas_single_decode"⟩
theorem checked1125 : check raw1125 clause1125 = true := by rfl
def row1125 : Row := ⟨1125, 4288707584, 144735232⟩
theorem derived1125 : clause1125.row = row1125 := by rfl
def entry1125 : CheckedRow := ⟨raw1125, clause1125, row1125, checked1125, derived1125⟩

def raw1126 : List String := ["function clause decode64 ((", "0b", "11010101000000110011", " @ ", "_ : bits(", "4", ")", " @ ", "0b", "01011111", " as op_code) if SEE < ", "1126", ") = {\n    SEE = ", "1126", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_monitors_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1126 : Clause := ⟨[.fixed "11010101000000110011", .any 4, .fixed "01011111"], 1126, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_monitors_decode"⟩
theorem checked1126 : check raw1126 clause1126 = true := by rfl
def row1126 : Row := ⟨1126, 4294963455, 3573755999⟩
theorem derived1126 : clause1126.row = row1126 := by rfl
def entry1126 : CheckedRow := ⟨raw1126, clause1126, row1126, checked1126, derived1126⟩

def raw1127 : List String := ["function clause decode64 ((", "0b", "010111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1127", ") = {\n    SEE = ", "1127", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_conv_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1127 : Clause := ⟨[.fixed "010111110", .any 7, .fixed "111001", .any 10], 1127, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_conv_int_sisd_decode"⟩
theorem checked1127 : check raw1127 clause1127 = true := by rfl
def row1127 : Row := ⟨1127, 4286643200, 1593893888⟩
theorem derived1127 : clause1127.row = row1127 := by rfl
def entry1127 : CheckedRow := ⟨raw1127, clause1127, row1127, checked1127, derived1127⟩

def raw1128 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "4", ")", " as op_code) if SEE < ", "1128", ") = {\n    SEE = ", "1128", ";\n", "    ", "nzcv", " : bits(", "4", ") = ", "op_code[", "3", " .. ", "0", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "4", "]]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_compare_cond_decode", "(", "nzcv", ", ", "op", ", ", "Rn", ", ", "cond", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1128 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 9, .fixed "01", .any 5, .fixed "0", .any 4], 1128, [⟨"nzcv", 4, 3, 0, false⟩, ⟨"op", 1, 4, 4, true⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_compare_cond_decode"⟩
theorem checked1128 : check raw1128 clause1128 = true := by rfl
def row1128 : Row := ⟨1128, 4280290320, 505414656⟩
theorem derived1128 : clause1128.row = row1128 := by rfl
def entry1128 : CheckedRow := ⟨raw1128, clause1128, row1128, checked1128, derived1128⟩

def raw1129 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1101011", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1129", ") = {\n    SEE = ", "1129", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "shift", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1129 : Clause := ⟨[.any 1, .fixed "1101011", .any 2, .fixed "0", .any 21], 1129, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_shiftedreg_decode"⟩
theorem checked1129 : check raw1129 clause1129 = true := by rfl
def row1129 : Row := ⟨1129, 2132803584, 1795162112⟩
theorem derived1129 : clause1129.row = row1129 := by rfl
def entry1129 : CheckedRow := ⟨raw1129, clause1129, row1129, checked1129, derived1129⟩

def entries12 : List CheckedRow := [entry1122, entry1123, entry1124, entry1125, entry1126, entry1127, entry1128, entry1129]
def rows12 : List Row := [row1122, row1123, row1124, row1125, row1126, row1127, row1128, row1129]
theorem indices12 : rows12.map Row.index = [1122, 1123, 1124, 1125, 1126, 1127, 1128, 1129] := by rfl
theorem bound12 : entries12.map CheckedRow.row = rows12 := by rfl
theorem choices_and_12 : choices rows12 167837696#32 (-1) = [] := by rfl
theorem choices_orr_12 : choices rows12 704708608#32 (-1) = [] := by rfl
theorem choices_eor_12 : choices rows12 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_12 : choices rows12 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
