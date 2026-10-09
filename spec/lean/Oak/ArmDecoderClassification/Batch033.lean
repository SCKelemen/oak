import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1290 : List String := ["function clause decode64 ((", "0b", "00001000010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1290", ") = {\n    SEE = ", "1290", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1290 : Clause := ⟨[.fixed "00001000010", .any 5, .fixed "1", .any 15], 1290, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1290 : check raw1290 clause1290 = true := by rfl
def row1290 : Row := ⟨1290, 4292902912, 138444800⟩
theorem derived1290 : clause1290.row = row1290 := by rfl
def entry1290 : CheckedRow := ⟨raw1290, clause1290, row1290, checked1290, derived1290⟩

def raw1291 : List String := ["function clause decode64 ((", "0b", "01111000010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1291", ") = {\n    SEE = ", "1291", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1291 : Clause := ⟨[.fixed "01111000010", .any 9, .fixed "00", .any 10], 1291, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1291 : check raw1291 clause1291 = true := by rfl
def row1291 : Row := ⟨1291, 4292873216, 2017460224⟩
theorem derived1291 : clause1291.row = row1291 := by rfl
def entry1291 : CheckedRow := ⟨raw1291, clause1291, row1291, checked1291, derived1291⟩

def raw1292 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100011000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1292", ") = {\n    SEE = ", "1292", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1292 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "100011000000", .any 10], 1292, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1292 : check raw1292 clause1292 = true := by rfl
def row1292 : Row := ⟨1292, 2134899712, 505610240⟩
theorem derived1292 : clause1292.row = row1292 := by rfl
def entry1292 : CheckedRow := ⟨raw1292, clause1292, row1292, checked1292, derived1292⟩

def raw1293 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001010010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1293", ") = {\n    SEE = ", "1293", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_extract_sat_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1293 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "100001010010", .any 10], 1293, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_extract_sat_sisd_decode"⟩
theorem checked1293 : check raw1293 clause1293 = true := by rfl
def row1293 : Row := ⟨1293, 4282383360, 1579239424⟩
theorem derived1293 : clause1293.row = row1293 := by rfl
def entry1293 : CheckedRow := ⟨raw1293, clause1293, row1293, checked1293, derived1293⟩

def raw1294 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1294", ") = {\n    SEE = ", "1294", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1294 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "100000110110", .any 10], 1294, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_float_bulk_sisd_decode"⟩
theorem checked1294 : check raw1294 clause1294 = true := by rfl
def row1294 : Row := ⟨1294, 4290771968, 2124470272⟩
theorem derived1294 : clause1294.row = row1294 := by rfl
def entry1294 : CheckedRow := ⟨raw1294, clause1294, row1294, checked1294, derived1294⟩

def raw1295 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1295", ") = {\n    SEE = ", "1295", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_diff_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1295 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "011101", .any 10], 1295, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_diff_decode"⟩
theorem checked1295 : check raw1295 clause1295 = true := by rfl
def row1295 : Row := ⟨1295, 3206609920, 773878784⟩
theorem derived1295 : clause1295.row = row1295 := by rfl
def entry1295 : CheckedRow := ⟨raw1295, clause1295, row1295, checked1295, derived1295⟩

def raw1296 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1296", ") = {\n    SEE = ", "1296", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_diff_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1296 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "011100", .any 10], 1296, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_diff_decode"⟩
theorem checked1296 : check raw1296 clause1296 = true := by rfl
def row1296 : Row := ⟨1296, 3206609920, 237006848⟩
theorem derived1296 : clause1296.row = row1296 := by rfl
def entry1296 : CheckedRow := ⟨raw1296, clause1296, row1296, checked1296, derived1296⟩

def raw1297 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1297", ") = {\n    SEE = ", "1297", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1297 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "1", .any 5, .fixed "111011", .any 10], 1297, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_simd_decode"⟩
theorem checked1297 : check raw1297 clause1297 = true := by rfl
def row1297 : Row := ⟨1297, 3214998528, 773909504⟩
theorem derived1297 : clause1297.row = row1297 := by rfl
def entry1297 : CheckedRow := ⟨raw1297, clause1297, row1297, checked1297, derived1297⟩

def entries33 : List CheckedRow := [entry1290, entry1291, entry1292, entry1293, entry1294, entry1295, entry1296, entry1297]
def rows33 : List Row := [row1290, row1291, row1292, row1293, row1294, row1295, row1296, row1297]
theorem indices33 : rows33.map Row.index = [1290, 1291, 1292, 1293, 1294, 1295, 1296, 1297] := by rfl
theorem bound33 : entries33.map CheckedRow.row = rows33 := by rfl
theorem choices_and_33 : choices rows33 167837696#32 (-1) = [] := by rfl
theorem choices_orr_33 : choices rows33 704708608#32 (-1) = [] := by rfl
theorem choices_eor_33 : choices rows33 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_33 : choices rows33 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
