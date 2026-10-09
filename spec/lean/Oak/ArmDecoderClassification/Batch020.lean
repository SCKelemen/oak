import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1186 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111011111000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1186", ") = {\n    SEE = ", "1186", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_fp16_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1186 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111011111000111110", .any 10], 1186, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_diffneg_fp16_decode"⟩
theorem checked1186 : check raw1186 clause1186 = true := by rfl
def row1186 : Row := ⟨1186, 3221224448, 251197440⟩
theorem derived1186 : clause1186.row = row1186 := by rfl
def entry1186 : CheckedRow := ⟨raw1186, clause1186, row1186, checked1186, derived1186⟩

def raw1187 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1110001", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1187", ") = {\n    SEE = ", "1187", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_immediate_decode", "(", "Rd", ", ", "Rn", ", ", "imm12", ", ", "shift", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1187 : Clause := ⟨[.any 1, .fixed "1110001", .any 24], 1187, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_immediate_decode"⟩
theorem checked1187 : check raw1187 clause1187 = true := by rfl
def row1187 : Row := ⟨1187, 2130706432, 1895825408⟩
theorem derived1187 : clause1187.row = row1187 := by rfl
def entry1187 : CheckedRow := ⟨raw1187, clause1187, row1187, checked1187, derived1187⟩

def raw1188 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1188", ") = {\n    SEE = ", "1188", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "eq", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "eq", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1188 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "1", .any 5, .fixed "001101", .any 10], 1188, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"eq", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_int_sisd_decode"⟩
theorem checked1188 : check raw1188 clause1188 = true := by rfl
def row1188 : Row := ⟨1188, 4280351744, 2116039680⟩
theorem derived1188 : clause1188.row = row1188 := by rfl
def entry1188 : CheckedRow := ⟨raw1188, clause1188, row1188, checked1188, derived1188⟩

def raw1189 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "010100010", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1189", ") = {\n    SEE = ", "1189", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_general_postidx_memory_pair_general_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1189 : Clause := ⟨[.any 1, .fixed "010100010", .any 22], 1189, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_general_postidx_memory_pair_general_postidx__decode"⟩
theorem checked1189 : check raw1189 clause1189 = true := by rfl
def row1189 : Row := ⟨1189, 2143289344, 679477248⟩
theorem derived1189 : clause1189.row = row1189 := by rfl
def entry1189 : CheckedRow := ⟨raw1189, clause1189, row1189, checked1189, derived1189⟩

def raw1190 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1190", ") = {\n    SEE = ", "1190", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_bitwise_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1190 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "100011", .any 10], 1190, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_bitwise_sisd_decode"⟩
theorem checked1190 : check raw1190 clause1190 = true := by rfl
def row1190 : Row := ⟨1190, 4280351744, 1579191296⟩
theorem derived1190 : clause1190.row = row1190 := by rfl
def entry1190 : CheckedRow := ⟨raw1190, clause1190, row1190, checked1190, derived1190⟩

def raw1191 : List String := ["function clause decode64 ((", "0b", "001110001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1191", ") = {\n    SEE = ", "1191", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1191 : Clause := ⟨[.fixed "001110001", .any 1, .fixed "0", .any 9, .fixed "11", .any 10], 1191, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1191 : check raw1191 clause1191 = true := by rfl
def row1191 : Row := ⟨1191, 4288678912, 947915776⟩
theorem derived1191 : clause1191.row = row1191 := by rfl
def entry1191 : CheckedRow := ⟨raw1191, clause1191, row1191, checked1191, derived1191⟩

def raw1192 : List String := ["function clause decode64 ((", "0b", "0100111000101000010010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1192", ") = {\n    SEE = ", "1192", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "D", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_aes_round_decode", "(", "Rd", ", ", "Rn", ", ", "D", ", ", "size", ")\n}\n"]
def clause1192 : Clause := ⟨[.fixed "0100111000101000010010", .any 10], 1192, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"D", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_aes_round_decode"⟩
theorem checked1192 : check raw1192 clause1192 = true := by rfl
def row1192 : Row := ⟨1192, 4294966272, 1311262720⟩
theorem derived1192 : clause1192.row = row1192 := by rfl
def entry1192 : CheckedRow := ⟨raw1192, clause1192, row1192, checked1192, derived1192⟩

def raw1193 : List String := ["function clause decode64 ((", "0b", "0101111011111000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1193", ") = {\n    SEE = ", "1193", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "a", ", ", "U", ")\n}\n"]
def clause1193 : Clause := ⟨[.fixed "0101111011111000110010", .any 10], 1193, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode"⟩
theorem checked1193 : check raw1193 clause1193 = true := by rfl
def row1193 : Row := ⟨1193, 4294966272, 1593362432⟩
theorem derived1193 : clause1193.row = row1193 := by rfl
def entry1193 : CheckedRow := ⟨raw1193, clause1193, row1193, checked1193, derived1193⟩

def entries20 : List CheckedRow := [entry1186, entry1187, entry1188, entry1189, entry1190, entry1191, entry1192, entry1193]
def rows20 : List Row := [row1186, row1187, row1188, row1189, row1190, row1191, row1192, row1193]
theorem indices20 : rows20.map Row.index = [1186, 1187, 1188, 1189, 1190, 1191, 1192, 1193] := by rfl
theorem bound20 : entries20.map CheckedRow.row = rows20 := by rfl
theorem choices_and_20 : choices rows20 167837696#32 (-1) = [] := by rfl
theorem choices_orr_20 : choices rows20 704708608#32 (-1) = [] := by rfl
theorem choices_eor_20 : choices rows20 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_20 : choices rows20 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
