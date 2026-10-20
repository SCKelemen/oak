import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1066 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0010001", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1066", ") = {\n    SEE = ", "1066", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_immediate_decode", "(", "Rd", ", ", "Rn", ", ", "imm12", ", ", "shift", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1066 : Clause := ⟨[.any 1, .fixed "0010001", .any 24], 1066, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_immediate_decode"⟩
theorem checked1066 : check raw1066 clause1066 = true := by rfl
def row1066 : Row := ⟨1066, 2130706432, 285212672⟩
theorem derived1066 : clause1066.row = row1066 := by rfl
def entry1066 : CheckedRow := ⟨raw1066, clause1066, row1066, checked1066, derived1066⟩

def raw1067 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1067", ") = {\n    SEE = ", "1067", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_diff_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1067 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "010100", .any 10], 1067, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_diff_decode"⟩
theorem checked1067 : check raw1067 clause1067 = true := by rfl
def row1067 : Row := ⟨1067, 3206609920, 236998656⟩
theorem derived1067 : clause1067.row = row1067 := by rfl
def entry1067 : CheckedRow := ⟨raw1067, clause1067, row1067, checked1067, derived1067⟩

def raw1068 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1068", ") = {\n    SEE = ", "1068", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_float_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1068 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "100000111110", .any 10], 1068, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_diffneg_float_decode"⟩
theorem checked1068 : check raw1068 clause1068 = true := by rfl
def row1068 : Row := ⟨1068, 3217030144, 782301184⟩
theorem derived1068 : clause1068.row = row1068 := by rfl
def entry1068 : CheckedRow := ⟨raw1068, clause1068, row1068, checked1068, derived1068⟩

def raw1069 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101011000001110", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1069", ") = {\n    SEE = ", "1069", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1069 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101011000001110", .any 12], 1069, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1069 : check raw1069 clause1069 = true := by rfl
def row1069 : Row := ⟨1069, 3221221376, 224452608⟩
theorem derived1069 : clause1069.row = row1069 := by rfl
def entry1069 : CheckedRow := ⟨raw1069, clause1069, row1069, checked1069, derived1069⟩

def raw1070 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1070", ") = {\n    SEE = ", "1070", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1070 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "100001101010", .any 10], 1070, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode"⟩
theorem checked1070 : check raw1070 clause1070 = true := by rfl
def row1070 : Row := ⟨1070, 4290771968, 2124523520⟩
theorem derived1070 : clause1070.row = row1070 := by rfl
def entry1070 : CheckedRow := ⟨raw1070, clause1070, row1070, checked1070, derived1070⟩

def raw1071 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "10110100", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1071", ") = {\n    SEE = ", "1071", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_simdfp_offset_memory_pair_simdfp_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1071 : Clause := ⟨[.any 2, .fixed "10110100", .any 22], 1071, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_simdfp_offset_memory_pair_simdfp_postidx__decode"⟩
theorem checked1071 : check raw1071 clause1071 = true := by rfl
def row1071 : Row := ⟨1071, 1069547520, 754974720⟩
theorem derived1071 : clause1071.row = row1071 := by rfl
def entry1071 : CheckedRow := ⟨raw1071, clause1071, row1071, checked1071, derived1071⟩

def raw1072 : List String := ["function clause decode64 ((", "0b", "010111111", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "1001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1072", ") = {\n    SEE = ", "1072", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_fp_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "opcode", ", ", "Rm", ", ", "M", ", ", "L", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1072 : Clause := ⟨[.fixed "010111111", .any 7, .fixed "1001", .any 1, .fixed "0", .any 10], 1072, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mul_fp_sisd_decode"⟩
theorem checked1072 : check raw1072 clause1072 = true := by rfl
def row1072 : Row := ⟨1072, 4286641152, 1602260992⟩
theorem derived1072 : clause1072.row = row1072 := by rfl
def entry1072 : CheckedRow := ⟨raw1072, clause1072, row1072, checked1072, derived1072⟩

def raw1073 : List String := ["function clause decode64 ((", "0b", "00111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1073", ") = {\n    SEE = ", "1073", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1073 : Clause := ⟨[.fixed "00111000000", .any 9, .fixed "01", .any 10], 1073, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_postidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1073 : check raw1073 clause1073 = true := by rfl
def row1073 : Row := ⟨1073, 4292873216, 939525120⟩
theorem derived1073 : clause1073.row = row1073 := by rfl
def entry1073 : CheckedRow := ⟨raw1073, clause1073, row1073, checked1073, derived1073⟩

def entries5 : List CheckedRow := [entry1066, entry1067, entry1068, entry1069, entry1070, entry1071, entry1072, entry1073]
def rows5 : List Row := [row1066, row1067, row1068, row1069, row1070, row1071, row1072, row1073]
theorem indices5 : rows5.map Row.index = [1066, 1067, 1068, 1069, 1070, 1071, 1072, 1073] := by rfl
theorem bound5 : entries5.map CheckedRow.row = rows5 := by rfl
theorem choices_and_5 : choices rows5 167837696#32 (-1) = [] := by rfl
theorem choices_orr_5 : choices rows5 704708608#32 (-1) = [] := by rfl
theorem choices_eor_5 : choices rows5 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_5 : choices rows5 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
