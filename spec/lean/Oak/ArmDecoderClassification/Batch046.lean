import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1394 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "10000", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1394", ") = {\n    SEE = ", "1394", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "immhi", " : bits(", "19", ") = ", "op_code[", "23", " .. ", "5", "]", ";\n", "    ", "immlo", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_address_pcrel_decode", "(", "Rd", ", ", "immhi", ", ", "immlo", ", ", "op", ")\n}\n"]
def clause1394 : Clause := ⟨[.fixed "1", .any 2, .fixed "10000", .any 24], 1394, [⟨"Rd", 5, 4, 0, false⟩, ⟨"immhi", 19, 23, 5, false⟩, ⟨"immlo", 2, 30, 29, false⟩, ⟨"op", 1, 31, 31, true⟩], "integer_arithmetic_address_pcrel_decode"⟩
theorem checked1394 : check raw1394 clause1394 = true := by rfl
def row1394 : Row := ⟨1394, 2667577344, 2415919104⟩
theorem derived1394 : clause1394.row = row1394 := by rfl
def entry1394 : CheckedRow := ⟨raw1394, clause1394, row1394, checked1394, derived1394⟩

def raw1395 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100100110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1395", ") = {\n    SEE = ", "1395", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "rmode", " : bits(", "3", ") = ", "op_code[", "17", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_round_frint_decode", "(", "Rd", ", ", "Rn", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1395 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100100110000", .any 10], 1395, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"rmode", 3, 17, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_round_frint_decode"⟩
theorem checked1395 : check raw1395 clause1395 = true := by rfl
def row1395 : Row := ⟨1395, 4282383360, 505724928⟩
theorem derived1395 : clause1395.row = row1395 := by rfl
def entry1395 : CheckedRow := ⟨raw1395, clause1395, row1395, checked1395, derived1395⟩

def raw1396 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101011000001100", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1396", ") = {\n    SEE = ", "1396", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1396 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101011000001100", .any 12], 1396, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1396 : check raw1396 clause1396 = true := by rfl
def row1396 : Row := ⟨1396, 3221221376, 224444416⟩
theorem derived1396 : clause1396.row = row1396 := by rfl
def entry1396 : CheckedRow := ⟨raw1396, clause1396, row1396, checked1396, derived1396⟩

def raw1397 : List String := ["function clause decode64 ((", "0b", "10011001010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1397", ") = {\n    SEE = ", "1397", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1397 : Clause := ⟨[.fixed "10011001010", .any 9, .fixed "00", .any 10], 1397, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1397 : check raw1397 clause1397 = true := by rfl
def row1397 : Row := ⟨1397, 4292873216, 2571108352⟩
theorem derived1397 : clause1397.row = row1397 := by rfl
def entry1397 : CheckedRow := ⟨raw1397, clause1397, row1397, checked1397, derived1397⟩

def raw1398 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111001111001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1398", ") = {\n    SEE = ", "1398", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1398 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111001111001110010", .any 10], 1398, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_conv_float_tieaway_simd_decode"⟩
theorem checked1398 : check raw1398 clause1398 = true := by rfl
def row1398 : Row := ⟨1398, 3221224448, 242862080⟩
theorem derived1398 : clause1398.row = row1398 := by rfl
def entry1398 : CheckedRow := ⟨raw1398, clause1398, row1398, checked1398, derived1398⟩

def raw1399 : List String := ["function clause decode64 ((", "0b", "00001000000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1399", ") = {\n    SEE = ", "1399", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1399 : Clause := ⟨[.fixed "00001000000", .any 5, .fixed "1", .any 15], 1399, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1399 : check raw1399 clause1399 = true := by rfl
def row1399 : Row := ⟨1399, 4292902912, 134250496⟩
theorem derived1399 : clause1399.row = row1399 := by rfl
def entry1399 : CheckedRow := ⟨raw1399, clause1399, row1399, checked1399, derived1399⟩

def raw1400 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100000000000000", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1400", ") = {\n    SEE = ", "1400", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1400 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100000000000000", .any 12], 1400, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode"⟩
theorem checked1400 : check raw1400 clause1400 = true := by rfl
def row1400 : Row := ⟨1400, 3221221376, 201326592⟩
theorem derived1400 : clause1400.row = row1400 := by rfl
def entry1400 : CheckedRow := ⟨raw1400, clause1400, row1400, checked1400, derived1400⟩

def raw1401 : List String := ["function clause decode64 ((", "0b", "010111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1401", ") = {\n    SEE = ", "1401", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_recps_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1401 : Clause := ⟨[.fixed "010111100", .any 1, .fixed "1", .any 5, .fixed "111111", .any 10], 1401, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_recps_sisd_decode"⟩
theorem checked1401 : check raw1401 clause1401 = true := by rfl
def row1401 : Row := ⟨1401, 4288740352, 1579219968⟩
theorem derived1401 : clause1401.row = row1401 := by rfl
def entry1401 : CheckedRow := ⟨raw1401, clause1401, row1401, checked1401, derived1401⟩

def entries46 : List CheckedRow := [entry1394, entry1395, entry1396, entry1397, entry1398, entry1399, entry1400, entry1401]
def rows46 : List Row := [row1394, row1395, row1396, row1397, row1398, row1399, row1400, row1401]
theorem indices46 : rows46.map Row.index = [1394, 1395, 1396, 1397, 1398, 1399, 1400, 1401] := by rfl
theorem bound46 : entries46.map CheckedRow.row = rows46 := by rfl
theorem choices_and_46 : choices rows46 167837696#32 (-1) = [] := by rfl
theorem choices_orr_46 : choices rows46 704708608#32 (-1) = [] := by rfl
theorem choices_eor_46 : choices rows46 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_46 : choices rows46 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
