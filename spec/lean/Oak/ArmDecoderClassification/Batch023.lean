import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1210 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "10110101", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1210", ") = {\n    SEE = ", "1210", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_simdfp_offset_memory_pair_simdfp_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1210 : Clause := ⟨[.any 2, .fixed "10110101", .any 22], 1210, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_simdfp_offset_memory_pair_simdfp_postidx__decode"⟩
theorem checked1210 : check raw1210 clause1210 = true := by rfl
def row1210 : Row := ⟨1210, 1069547520, 759169024⟩
theorem derived1210 : clause1210.row = row1210 := by rfl
def entry1210 : CheckedRow := ⟨raw1210, clause1210, row1210, checked1210, derived1210⟩

def raw1211 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "011001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1211", ") = {\n    SEE = ", "1211", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_leftsat_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1211 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "011001", .any 10], 1211, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_leftsat_sisd_decode"⟩
theorem checked1211 : check raw1211 clause1211 = true := by rfl
def row1211 : Row := ⟨1211, 4286643200, 2130732032⟩
theorem derived1211 : clause1211.row = row1211 := by rfl
def entry1211 : CheckedRow := ⟨raw1211, clause1211, row1211, checked1211, derived1211⟩

def raw1212 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "000010", " @ ", "_ : bits(", "16", ")", " as op_code) if SEE < ", "1212", ") = {\n    SEE = ", "1212", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "scale", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_fix_decode", "(", "Rd", ", ", "Rn", ", ", "scale", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1212 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "000010", .any 16], 1212, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"scale", 6, 15, 10, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_fix_decode"⟩
theorem checked1212 : check raw1212 clause1212 = true := by rfl
def row1212 : Row := ⟨1212, 2134835200, 503447552⟩
theorem derived1212 : clause1212.row = row1212 := by rfl
def entry1212 : CheckedRow := ⟨raw1212, clause1212, row1212, checked1212, derived1212⟩

def raw1213 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00110100100000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1213", ") = {\n    SEE = ", "1213", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1213 : Clause := ⟨[.fixed "0", .any 1, .fixed "00110100100000", .any 2, .fixed "0", .any 13], 1213, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1213 : check raw1213 clause1213 = true := by rfl
def row1213 : Row := ⟨1213, 3221168128, 220200960⟩
theorem derived1213 : clause1213.row = row1213 := by rfl
def entry1213 : CheckedRow := ⟨raw1213, clause1213, row1213, checked1213, derived1213⟩

def raw1214 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1214", ") = {\n    SEE = ", "1214", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm4", " : bits(", "4", ") = ", "op_code[", "14", " .. ", "11", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_cpydup_simd_decode", "(", "Rd", ", ", "Rn", ", ", "imm4", ", ", "imm5", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1214 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110000", .any 5, .fixed "000001", .any 10], 1214, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm4", 4, 14, 11, false⟩, ⟨"imm5", 5, 20, 16, false⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_cpydup_simd_decode"⟩
theorem checked1214 : check raw1214 clause1214 = true := by rfl
def row1214 : Row := ⟨1214, 3219192832, 234882048⟩
theorem derived1214 : clause1214.row = row1214 := by rfl
def entry1214 : CheckedRow := ⟨raw1214, clause1214, row1214, checked1214, derived1214⟩

def raw1215 : List String := ["function clause decode64 ((", "0b", "000101", " @ ", "_ : bits(", "26", ")", " as op_code) if SEE < ", "1215", ") = {\n    SEE = ", "1215", ";\n", "    ", "imm26", " : bits(", "26", ") = ", "op_code[", "25", " .. ", "0", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "branch_unconditional_immediate_decode", "(", "imm26", ", ", "op", ")\n}\n"]
def clause1215 : Clause := ⟨[.fixed "000101", .any 26], 1215, [⟨"imm26", 26, 25, 0, false⟩, ⟨"op", 1, 31, 31, true⟩], "branch_unconditional_immediate_decode"⟩
theorem checked1215 : check raw1215 clause1215 = true := by rfl
def row1215 : Row := ⟨1215, 4227858432, 335544320⟩
theorem derived1215 : clause1215.row = row1215 := by rfl
def entry1215 : CheckedRow := ⟨raw1215, clause1215, row1215, checked1215, derived1215⟩

def raw1216 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1216", ") = {\n    SEE = ", "1216", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp_2008_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1216 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "1", .any 5, .fixed "110001", .any 10], 1216, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp_2008_decode"⟩
theorem checked1216 : check raw1216 clause1216 = true := by rfl
def row1216 : Row := ⟨1216, 3214998528, 237028352⟩
theorem derived1216 : clause1216.row = row1216 := by rfl
def entry1216 : CheckedRow := ⟨raw1216, clause1216, row1216, checked1216, derived1216⟩

def raw1217 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "011001", " @ ", "_ : bits(", "16", ")", " as op_code) if SEE < ", "1217", ") = {\n    SEE = ", "1217", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "scale", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_fix_decode", "(", "Rd", ", ", "Rn", ", ", "scale", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1217 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "011001", .any 16], 1217, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"scale", 6, 15, 10, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_fix_decode"⟩
theorem checked1217 : check raw1217 clause1217 = true := by rfl
def row1217 : Row := ⟨1217, 2134835200, 504954880⟩
theorem derived1217 : clause1217.row = row1217 := by rfl
def entry1217 : CheckedRow := ⟨raw1217, clause1217, row1217, checked1217, derived1217⟩

def entries23 : List CheckedRow := [entry1210, entry1211, entry1212, entry1213, entry1214, entry1215, entry1216, entry1217]
def rows23 : List Row := [row1210, row1211, row1212, row1213, row1214, row1215, row1216, row1217]
theorem indices23 : rows23.map Row.index = [1210, 1211, 1212, 1213, 1214, 1215, 1216, 1217] := by rfl
theorem bound23 : entries23.map CheckedRow.row = rows23 := by rfl
theorem choices_and_23 : choices rows23 167837696#32 (-1) = [] := by rfl
theorem choices_orr_23 : choices rows23 704708608#32 (-1) = [] := by rfl
theorem choices_eor_23 : choices rows23 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_23 : choices rows23 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
