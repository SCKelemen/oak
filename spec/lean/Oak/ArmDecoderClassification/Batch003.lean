import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1050 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1110", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1050", ") = {\n    SEE = ", "1050", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1050 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101110", .any 5, .fixed "1110", .any 12], 1050, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1050 : check raw1050 clause1050 = true := by rfl
def row1050 : Row := ⟨1050, 3219189760, 230744064⟩
theorem derived1050 : clause1050.row = row1050 := by rfl
def entry1050 : CheckedRow := ⟨raw1050, clause1050, row1050, checked1050, derived1050⟩

def raw1051 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "011000", " @ ", "_ : bits(", "16", ")", " as op_code) if SEE < ", "1051", ") = {\n    SEE = ", "1051", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "scale", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_fix_decode", "(", "Rd", ", ", "Rn", ", ", "scale", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1051 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "011000", .any 16], 1051, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"scale", 6, 15, 10, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_fix_decode"⟩
theorem checked1051 : check raw1051 clause1051 = true := by rfl
def row1051 : Row := ⟨1051, 2134835200, 504889344⟩
theorem derived1051 : clause1051.row = row1051 := by rfl
def entry1051 : CheckedRow := ⟨raw1051, clause1051, row1051, checked1051, derived1051⟩

def raw1052 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1052", ") = {\n    SEE = ", "1052", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_saturating_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1052 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "1", .any 5, .fixed "000011", .any 10], 1052, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_add_saturating_sisd_decode"⟩
theorem checked1052 : check raw1052 clause1052 = true := by rfl
def row1052 : Row := ⟨1052, 4280351744, 2116029440⟩
theorem derived1052 : clause1052.row = row1052 := by rfl
def entry1052 : CheckedRow := ⟨raw1052, clause1052, row1052, checked1052, derived1052⟩

def raw1053 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111001111001100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1053", ") = {\n    SEE = ", "1053", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1053 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111001111001100010", .any 10], 1053, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_round_decode"⟩
theorem checked1053 : check raw1053 clause1053 = true := by rfl
def row1053 : Row := ⟨1053, 3221224448, 779716608⟩
theorem derived1053 : clause1053.row = row1053 := by rfl
def entry1053 : CheckedRow := ⟨raw1053, clause1053, row1053, checked1053, derived1053⟩

def raw1054 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1054", ") = {\n    SEE = ", "1054", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_addsub_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1054 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "001110", .any 10], 1054, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_addsub_decode"⟩
theorem checked1054 : check raw1054 clause1054 = true := by rfl
def row1054 : Row := ⟨1054, 4280351744, 505427968⟩
theorem derived1054 : clause1054.row = row1054 := by rfl
def entry1054 : CheckedRow := ⟨raw1054, clause1054, row1054, checked1054, derived1054⟩

def raw1055 : List String := ["function clause decode64 ((", "0b", "00111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1055", ") = {\n    SEE = ", "1055", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1055 : Clause := ⟨[.fixed "00111000", .any 2, .fixed "1", .any 5, .fixed "010100", .any 10], 1055, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1055 : check raw1055 clause1055 = true := by rfl
def row1055 : Row := ⟨1055, 4280351744, 941641728⟩
theorem derived1055 : clause1055.row = row1055 := by rfl
def entry1055 : CheckedRow := ⟨raw1055, clause1055, row1055, checked1055, derived1055⟩

def raw1056 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0111010000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1056", ") = {\n    SEE = ", "1056", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode2", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_carry_decode", "(", "Rd", ", ", "Rn", ", ", "opcode2", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1056 : Clause := ⟨[.any 1, .fixed "0111010000", .any 5, .fixed "000000", .any 10], 1056, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode2", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_carry_decode"⟩
theorem checked1056 : check raw1056 clause1056 = true := by rfl
def row1056 : Row := ⟨1056, 2145451008, 973078528⟩
theorem derived1056 : clause1056.row = row1056 := by rfl
def entry1056 : CheckedRow := ⟨raw1056, clause1056, row1056, checked1056, derived1056⟩

def raw1057 : List String := ["function clause decode64 ((", "0b", "10111000100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1057", ") = {\n    SEE = ", "1057", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1057 : Clause := ⟨[.fixed "10111000100", .any 9, .fixed "11", .any 10], 1057, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1057 : check raw1057 clause1057 = true := by rfl
def row1057 : Row := ⟨1057, 4292873216, 3095399424⟩
theorem derived1057 : clause1057.row = row1057 := by rfl
def entry1057 : CheckedRow := ⟨raw1057, clause1057, row1057, checked1057, derived1057⟩

def entries3 : List CheckedRow := [entry1050, entry1051, entry1052, entry1053, entry1054, entry1055, entry1056, entry1057]
def rows3 : List Row := [row1050, row1051, row1052, row1053, row1054, row1055, row1056, row1057]
theorem indices3 : rows3.map Row.index = [1050, 1051, 1052, 1053, 1054, 1055, 1056, 1057] := by rfl
theorem bound3 : entries3.map CheckedRow.row = rows3 := by rfl
theorem choices_and_3 : choices rows3 167837696#32 (-1) = [] := by rfl
theorem choices_orr_3 : choices rows3 704708608#32 (-1) = [] := by rfl
theorem choices_eor_3 : choices rows3 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_3 : choices rows3 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
