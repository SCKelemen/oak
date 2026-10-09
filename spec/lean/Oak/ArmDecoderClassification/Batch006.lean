import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1074 : List String := ["function clause decode64 ((", "0b", "01001000000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1074", ") = {\n    SEE = ", "1074", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1074 : Clause := ⟨[.fixed "01001000000", .any 5, .fixed "1", .any 15], 1074, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1074 : check raw1074 clause1074 = true := by rfl
def row1074 : Row := ⟨1074, 4292902912, 1207992320⟩
theorem derived1074 : clause1074.row = row1074 := by rfl
def entry1074 : CheckedRow := ⟨raw1074, clause1074, row1074, checked1074, derived1074⟩

def raw1075 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1075", ") = {\n    SEE = ", "1075", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1075 : Clause := ⟨[.fixed "1", .any 1, .fixed "1110000", .any 1, .fixed "1", .any 5, .fixed "010100", .any 5, .fixed "11111"], 1075, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1075 : check raw1075 clause1075 = true := by rfl
def row1075 : Row := ⟨1075, 3214998559, 3089125407⟩
theorem derived1075 : clause1075.row = row1075 := by rfl
def entry1075 : CheckedRow := ⟨raw1075, clause1075, row1075, checked1075, derived1075⟩

def raw1076 : List String := ["function clause decode64 ((", "0b", "01111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1076", ") = {\n    SEE = ", "1076", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1076 : Clause := ⟨[.fixed "01111000", .any 2, .fixed "1", .any 5, .fixed "000000", .any 10], 1076, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1076 : check raw1076 clause1076 = true := by rfl
def row1076 : Row := ⟨1076, 4280351744, 2015363072⟩
theorem derived1076 : clause1076.row = row1076 := by rfl
def entry1076 : CheckedRow := ⟨raw1076, clause1076, row1076, checked1076, derived1076⟩

def raw1077 : List String := ["function clause decode64 ((", "0b", "00011111", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1077", ") = {\n    SEE = ", "1077", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_mul_addsub_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "o1", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1077 : Clause := ⟨[.fixed "00011111", .any 2, .fixed "1", .any 5, .fixed "0", .any 15], 1077, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_mul_addsub_decode"⟩
theorem checked1077 : check raw1077 clause1077 = true := by rfl
def row1077 : Row := ⟨1077, 4280320000, 522190848⟩
theorem derived1077 : clause1077.row = row1077 := by rfl
def entry1077 : CheckedRow := ⟨raw1077, clause1077, row1077, checked1077, derived1077⟩

def raw1078 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1078", ") = {\n    SEE = ", "1078", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_int_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1078 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000101110", .any 10], 1078, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_diffneg_int_simd_decode"⟩
theorem checked1078 : check raw1078 clause1078 = true := by rfl
def row1078 : Row := ⟨1078, 3208641536, 237025280⟩
theorem derived1078 : clause1078.row = row1078 := by rfl
def entry1078 : CheckedRow := ⟨raw1078, clause1078, row1078, checked1078, derived1078⟩

def raw1079 : List String := ["function clause decode64 ((", "0b", "1001000110", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1079", ") = {\n    SEE = ", "1079", ";\n", "    ", "Xd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "uimm4", " : bits(", "4", ") = ", "op_code[", "13", " .. ", "10", "]", ";\n", "    ", "op3", " : bits(", "2", ") = ", "op_code[", "15", " .. ", "14", "]", ";\n", "    ", "uimm6", " : bits(", "6", ") = ", "op_code[", "21", " .. ", "16", "]", ";\n", "    ", "integer_tags_mcaddtag_decode", "(", "Xd", ", ", "Xn", ", ", "uimm4", ", ", "op3", ", ", "uimm6", ")\n}\n"]
def clause1079 : Clause := ⟨[.fixed "1001000110", .any 22], 1079, [⟨"Xd", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"uimm4", 4, 13, 10, false⟩, ⟨"op3", 2, 15, 14, false⟩, ⟨"uimm6", 6, 21, 16, false⟩], "integer_tags_mcaddtag_decode"⟩
theorem checked1079 : check raw1079 clause1079 = true := by rfl
def row1079 : Row := ⟨1079, 4290772992, 2441084928⟩
theorem derived1079 : clause1079.row = row1079 := by rfl
def entry1079 : CheckedRow := ⟨raw1079, clause1079, row1079, checked1079, derived1079⟩

def raw1080 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1001011001", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1080", ") = {\n    SEE = ", "1080", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm3", " : bits(", "3", ") = ", "op_code[", "12", " .. ", "10", "]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opt", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_extendedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm3", ", ", "option_name", ", ", "Rm", ", ", "opt", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1080 : Clause := ⟨[.any 1, .fixed "1001011001", .any 21], 1080, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm3", 3, 12, 10, false⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opt", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_extendedreg_decode"⟩
theorem checked1080 : check raw1080 clause1080 = true := by rfl
def row1080 : Row := ⟨1080, 2145386496, 1260388352⟩
theorem derived1080 : clause1080.row = row1080 := by rfl
def entry1080 : CheckedRow := ⟨raw1080, clause1080, row1080, checked1080, derived1080⟩

def raw1081 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1081", ") = {\n    SEE = ", "1081", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "eq", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "eq", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1081 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "001111", .any 10], 1081, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"eq", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_int_sisd_decode"⟩
theorem checked1081 : check raw1081 clause1081 = true := by rfl
def row1081 : Row := ⟨1081, 4280351744, 1579170816⟩
theorem derived1081 : clause1081.row = row1081 := by rfl
def entry1081 : CheckedRow := ⟨raw1081, clause1081, row1081, checked1081, derived1081⟩

def entries6 : List CheckedRow := [entry1074, entry1075, entry1076, entry1077, entry1078, entry1079, entry1080, entry1081]
def rows6 : List Row := [row1074, row1075, row1076, row1077, row1078, row1079, row1080, row1081]
theorem indices6 : rows6.map Row.index = [1074, 1075, 1076, 1077, 1078, 1079, 1080, 1081] := by rfl
theorem bound6 : entries6.map CheckedRow.row = rows6 := by rfl
theorem choices_and_6 : choices rows6 167837696#32 (-1) = [] := by rfl
theorem choices_orr_6 : choices rows6 704708608#32 (-1) = [] := by rfl
theorem choices_eor_6 : choices rows6 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_6 : choices rows6 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
