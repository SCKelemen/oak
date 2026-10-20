import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1138 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1011010000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1138", ") = {\n    SEE = ", "1138", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode2", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_carry_decode", "(", "Rd", ", ", "Rn", ", ", "opcode2", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1138 : Clause := ⟨[.any 1, .fixed "1011010000", .any 5, .fixed "000000", .any 10], 1138, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode2", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_carry_decode"⟩
theorem checked1138 : check raw1138 clause1138 = true := by rfl
def row1138 : Row := ⟨1138, 2145451008, 1509949440⟩
theorem derived1138 : clause1138.row = row1138 := by rfl
def entry1138 : CheckedRow := ⟨raw1138, clause1138, row1138, checked1138, derived1138⟩

def raw1139 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1139", ") = {\n    SEE = ", "1139", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1139 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "1", .any 5, .fixed "111001", .any 10], 1139, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_simd_decode"⟩
theorem checked1139 : check raw1139 clause1139 = true := by rfl
def row1139 : Row := ⟨1139, 3214998528, 237036544⟩
theorem derived1139 : clause1139.row = row1139 := by rfl
def entry1139 : CheckedRow := ⟨raw1139, clause1139, row1139, checked1139, derived1139⟩

def raw1140 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1140", ") = {\n    SEE = ", "1140", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_simdfp_immediate_signed_offset_normal_memory_single_simdfp_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1140 : Clause := ⟨[.any 2, .fixed "111100", .any 1, .fixed "10", .any 9, .fixed "00", .any 10], 1140, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_simdfp_immediate_signed_offset_normal_memory_single_simdfp_immediate_signed_offset_normal__decode"⟩
theorem checked1140 : check raw1140 clause1140 = true := by rfl
def row1140 : Row := ⟨1140, 1063259136, 1010827264⟩
theorem derived1140 : clause1140.row = row1140 := by rfl
def entry1140 : CheckedRow := ⟨raw1140, clause1140, row1140, checked1140, derived1140⟩

def raw1141 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001010010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1141", ") = {\n    SEE = ", "1141", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_extract_sat_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1141 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100001010010", .any 10], 1141, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_extract_sat_simd_decode"⟩
theorem checked1141 : check raw1141 clause1141 = true := by rfl
def row1141 : Row := ⟨1141, 3208641536, 773933056⟩
theorem derived1141 : clause1141.row = row1141 := by rfl
def entry1141 : CheckedRow := ⟨raw1141, clause1141, row1141, checked1141, derived1141⟩

def raw1142 : List String := ["function clause decode64 ((", "0b", "11010101000000110011", " @ ", "_ : bits(", "4", ")", " @ ", "0b", "10111111", " as op_code) if SEE < ", "1142", ") = {\n    SEE = ", "1142", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "6", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_barriers_decode", "(", "Rt", ", ", "opc", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1142 : Clause := ⟨[.fixed "11010101000000110011", .any 4, .fixed "10111111"], 1142, [⟨"Rt", 5, 4, 0, false⟩, ⟨"opc", 2, 6, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_barriers_decode"⟩
theorem checked1142 : check raw1142 clause1142 = true := by rfl
def row1142 : Row := ⟨1142, 4294963455, 3573756095⟩
theorem derived1142 : clause1142.row = row1142 := by rfl
def entry1142 : CheckedRow := ⟨raw1142, clause1142, row1142, checked1142, derived1142⟩

def raw1143 : List String := ["function clause decode64 ((", "0b", "0100111000101000011010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1143", ") = {\n    SEE = ", "1143", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "D", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_aes_mix_decode", "(", "Rd", ", ", "Rn", ", ", "D", ", ", "size", ")\n}\n"]
def clause1143 : Clause := ⟨[.fixed "0100111000101000011010", .any 10], 1143, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"D", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_aes_mix_decode"⟩
theorem checked1143 : check raw1143 clause1143 = true := by rfl
def row1143 : Row := ⟨1143, 4294966272, 1311270912⟩
theorem derived1143 : clause1143.row = row1143 := by rfl
def entry1143 : CheckedRow := ⟨raw1143, clause1143, row1143, checked1143, derived1143⟩

def raw1144 : List String := ["function clause decode64 ((", "0b", "110110101100000100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1144", ") = {\n    SEE = ", "1144", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_autdb_dp_1src_decode", "(", "Rd", ", ", "Rn", ", ", "Z", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1144 : Clause := ⟨[.fixed "110110101100000100", .any 1, .fixed "111", .any 10], 1144, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Z", 1, 13, 13, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_autdb_dp_1src_decode"⟩
theorem checked1144 : check raw1144 clause1144 = true := by rfl
def row1144 : Row := ⟨1144, 4294958080, 3670088704⟩
theorem derived1144 : clause1144.row = row1144 := by rfl
def entry1144 : CheckedRow := ⟨raw1144, clause1144, row1144, checked1144, derived1144⟩

def raw1145 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1145", ") = {\n    SEE = ", "1145", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1145 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100000101110", .any 10], 1145, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_diffneg_int_simd_decode"⟩
theorem checked1145 : check raw1145 clause1145 = true := by rfl
def row1145 : Row := ⟨1145, 3208641536, 773896192⟩
theorem derived1145 : clause1145.row = row1145 := by rfl
def entry1145 : CheckedRow := ⟨raw1145, clause1145, row1145, checked1145, derived1145⟩

def entries14 : List CheckedRow := [entry1138, entry1139, entry1140, entry1141, entry1142, entry1143, entry1144, entry1145]
def rows14 : List Row := [row1138, row1139, row1140, row1141, row1142, row1143, row1144, row1145]
theorem indices14 : rows14.map Row.index = [1138, 1139, 1140, 1141, 1142, 1143, 1144, 1145] := by rfl
theorem bound14 : entries14.map CheckedRow.row = rows14 := by rfl
theorem choices_and_14 : choices rows14 167837696#32 (-1) = [] := by rfl
theorem choices_orr_14 : choices rows14 704708608#32 (-1) = [] := by rfl
theorem choices_eor_14 : choices rows14 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_14 : choices rows14 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
