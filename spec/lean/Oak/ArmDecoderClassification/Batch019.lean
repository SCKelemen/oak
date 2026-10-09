import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1178 : List String := ["function clause decode64 ((", "0b", "10111000101", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1178", ") = {\n    SEE = ", "1178", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_register_memory_single_general_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1178 : Clause := ⟨[.fixed "10111000101", .any 9, .fixed "10", .any 10], 1178, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_register_memory_single_general_register__decode"⟩
theorem checked1178 : check raw1178 clause1178 = true := by rfl
def row1178 : Row := ⟨1178, 4292873216, 3097495552⟩
theorem derived1178 : clause1178.row = row1178 := by rfl
def entry1178 : CheckedRow := ⟨raw1178, clause1178, row1178, checked1178, derived1178⟩

def raw1179 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000011", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1179", ") = {\n    SEE = ", "1179", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_register_memory_single_general_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1179 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000011", .any 9, .fixed "10", .any 10], 1179, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_register_memory_single_general_register__decode"⟩
theorem checked1179 : check raw1179 clause1179 = true := by rfl
def row1179 : Row := ⟨1179, 3219131392, 3093301248⟩
theorem derived1179 : clause1179.row = row1179 := by rfl
def entry1179 : CheckedRow := ⟨raw1179, clause1179, row1179, checked1179, derived1179⟩

def raw1180 : List String := ["function clause decode64 ((", "0b", "01011110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1180", ") = {\n    SEE = ", "1180", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ")\n}\n"]
def clause1180 : Clause := ⟨[.fixed "01011110010", .any 5, .fixed "000111", .any 10], 1180, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_mul_fp16_extended_sisd_decode"⟩
theorem checked1180 : check raw1180 clause1180 = true := by rfl
def row1180 : Row := ⟨1180, 4292934656, 1581259776⟩
theorem derived1180 : clause1180.row = row1180 := by rfl
def entry1180 : CheckedRow := ⟨raw1180, clause1180, row1180, checked1180, derived1180⟩

def raw1181 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1181", ") = {\n    SEE = ", "1181", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_simdfp_register_memory_single_simdfp_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1181 : Clause := ⟨[.any 2, .fixed "111100", .any 1, .fixed "01", .any 9, .fixed "10", .any 10], 1181, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_simdfp_register_memory_single_simdfp_register__decode"⟩
theorem checked1181 : check raw1181 clause1181 = true := by rfl
def row1181 : Row := ⟨1181, 1063259136, 1008732160⟩
theorem derived1181 : clause1181.row = row1181 := by rfl
def entry1181 : CheckedRow := ⟨raw1181, clause1181, row1181, checked1181, derived1181⟩

def raw1182 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1182", ") = {\n    SEE = ", "1182", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1182 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000010", .any 9, .fixed "00", .any 10], 1182, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1182 : check raw1182 clause1182 = true := by rfl
def row1182 : Row := ⟨1182, 3219131392, 3091202048⟩
theorem derived1182 : clause1182.row = row1182 := by rfl
def entry1182 : CheckedRow := ⟨raw1182, clause1182, row1182, checked1182, derived1182⟩

def raw1183 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00110101000000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1183", ") = {\n    SEE = ", "1183", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1183 : Clause := ⟨[.fixed "0", .any 1, .fixed "00110101000000", .any 2, .fixed "0", .any 13], 1183, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1183 : check raw1183 clause1183 = true := by rfl
def row1183 : Row := ⟨1183, 3221168128, 222298112⟩
theorem derived1183 : clause1183.row = row1183 := by rfl
def entry1183 : CheckedRow := ⟨raw1183, clause1183, row1183, checked1183, derived1183⟩

def raw1184 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000001110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1184", ") = {\n    SEE = ", "1184", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_add_saturating_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1184 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "100000001110", .any 10], 1184, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_add_saturating_sisd_decode"⟩
theorem checked1184 : check raw1184 clause1184 = true := by rfl
def row1184 : Row := ⟨1184, 4282383360, 1579169792⟩
theorem derived1184 : clause1184.row = row1184 := by rfl
def entry1184 : CheckedRow := ⟨raw1184, clause1184, row1184, checked1184, derived1184⟩

def raw1185 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110111", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1185", ") = {\n    SEE = ", "1185", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc2", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_logical_bsleor_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "opc2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1185 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110111", .any 5, .fixed "000111", .any 10], 1185, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc2", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_logical_bsleor_decode"⟩
theorem checked1185 : check raw1185 clause1185 = true := by rfl
def row1185 : Row := ⟨1185, 3219192832, 786439168⟩
theorem derived1185 : clause1185.row = row1185 := by rfl
def entry1185 : CheckedRow := ⟨raw1185, clause1185, row1185, checked1185, derived1185⟩

def entries19 : List CheckedRow := [entry1178, entry1179, entry1180, entry1181, entry1182, entry1183, entry1184, entry1185]
def rows19 : List Row := [row1178, row1179, row1180, row1181, row1182, row1183, row1184, row1185]
theorem indices19 : rows19.map Row.index = [1178, 1179, 1180, 1181, 1182, 1183, 1184, 1185] := by rfl
theorem bound19 : entries19.map CheckedRow.row = rows19 := by rfl
theorem choices_and_19 : choices rows19 167837696#32 (-1) = [] := by rfl
theorem choices_orr_19 : choices rows19 704708608#32 (-1) = [] := by rfl
theorem choices_eor_19 : choices rows19 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_19 : choices rows19 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
