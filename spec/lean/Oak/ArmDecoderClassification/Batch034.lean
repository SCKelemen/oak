import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1298 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1298", ") = {\n    SEE = ", "1298", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_divfp16_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1298 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110010", .any 5, .fixed "001111", .any 10], 1298, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_divfp16_decode"⟩
theorem checked1298 : check raw1298 clause1298 = true := by rfl
def row1298 : Row := ⟨1298, 3219192832, 775961600⟩
theorem derived1298 : clause1298.row = row1298 := by rfl
def entry1298 : CheckedRow := ⟨raw1298, clause1298, row1298, checked1298, derived1298⟩

def raw1299 : List String := ["function clause decode64 ((", "0b", "00011001100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1299", ") = {\n    SEE = ", "1299", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagandzerodatapre_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1299 : Clause := ⟨[.fixed "00011001100", .any 9, .fixed "11", .any 10], 1299, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagandzerodatapre_decode"⟩
theorem checked1299 : check raw1299 clause1299 = true := by rfl
def row1299 : Row := ⟨1299, 4292873216, 427822080⟩
theorem derived1299 : clause1299.row = row1299 := by rfl
def entry1299 : CheckedRow := ⟨raw1299, clause1299, row1299, checked1299, derived1299⟩

def raw1300 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1300", ") = {\n    SEE = ", "1300", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_rightnarrow_nonuniform_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1300 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "100001", .any 10], 1300, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_rightnarrow_nonuniform_sisd_decode"⟩
theorem checked1300 : check raw1300 clause1300 = true := by rfl
def row1300 : Row := ⟨1300, 4286643200, 2130740224⟩
theorem derived1300 : clause1300.row = row1300 := by rfl
def entry1300 : CheckedRow := ⟨raw1300, clause1300, row1300, checked1300, derived1300⟩

def raw1301 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1301", ") = {\n    SEE = ", "1301", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_right_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1301 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "000001", .any 10], 1301, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_right_sisd_decode"⟩
theorem checked1301 : check raw1301 clause1301 = true := by rfl
def row1301 : Row := ⟨1301, 4286643200, 2130707456⟩
theorem derived1301 : clause1301.row = row1301 := by rfl
def entry1301 : CheckedRow := ⟨raw1301, clause1301, row1301, checked1301, derived1301⟩

def raw1302 : List String := ["function clause decode64 ((", "0b", "00011111", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1302", ") = {\n    SEE = ", "1302", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_mul_addsub_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "o1", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1302 : Clause := ⟨[.fixed "00011111", .any 2, .fixed "0", .any 5, .fixed "1", .any 15], 1302, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_mul_addsub_decode"⟩
theorem checked1302 : check raw1302 clause1302 = true := by rfl
def row1302 : Row := ⟨1302, 4280320000, 520126464⟩
theorem derived1302 : clause1302.row = row1302 := by rfl
def entry1302 : CheckedRow := ⟨raw1302, clause1302, row1302, checked1302, derived1302⟩

def raw1303 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111000100000010110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1303", ") = {\n    SEE = ", "1303", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_not_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1303 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111000100000010110", .any 10], 1303, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_not_decode"⟩
theorem checked1303 : check raw1303 clause1303 = true := by rfl
def row1303 : Row := ⟨1303, 3221224448, 773871616⟩
theorem derived1303 : clause1303.row = row1303 := by rfl
def entry1303 : CheckedRow := ⟨raw1303, clause1303, row1303, checked1303, derived1303⟩

def raw1304 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1304", ") = {\n    SEE = ", "1304", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_tieaway_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1304 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "100001110010", .any 10], 1304, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_float_tieaway_simd_decode"⟩
theorem checked1304 : check raw1304 clause1304 = true := by rfl
def row1304 : Row := ⟨1304, 3217030144, 237094912⟩
theorem derived1304 : clause1304.row = row1304 := by rfl
def entry1304 : CheckedRow := ⟨raw1304, clause1304, row1304, checked1304, derived1304⟩

def raw1305 : List String := ["function clause decode64 ((", "0b", "11010110101111110000001111100000", " as op_code) if SEE < ", "1305", ") = {\n    SEE = ", "1305", ";\n", "    ", "op4", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op3", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "op2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "4", ") = ", "op_code[", "24", " .. ", "21", "]", ";\n", "    ", "branch_unconditional_dret_decode", "(", "op4", ", ", "Rt", ", ", "op3", ", ", "op2", ", ", "opc", ")\n}\n"]
def clause1305 : Clause := ⟨[.fixed "11010110101111110000001111100000"], 1305, [⟨"op4", 5, 4, 0, false⟩, ⟨"Rt", 5, 9, 5, false⟩, ⟨"op3", 6, 15, 10, false⟩, ⟨"op2", 5, 20, 16, false⟩, ⟨"opc", 4, 24, 21, false⟩], "branch_unconditional_dret_decode"⟩
theorem checked1305 : check raw1305 clause1305 = true := by rfl
def row1305 : Row := ⟨1305, 4294967295, 3602842592⟩
theorem derived1305 : clause1305.row = row1305 := by rfl
def entry1305 : CheckedRow := ⟨raw1305, clause1305, row1305, checked1305, derived1305⟩

def entries34 : List CheckedRow := [entry1298, entry1299, entry1300, entry1301, entry1302, entry1303, entry1304, entry1305]
def rows34 : List Row := [row1298, row1299, row1300, row1301, row1302, row1303, row1304, row1305]
theorem indices34 : rows34.map Row.index = [1298, 1299, 1300, 1301, 1302, 1303, 1304, 1305] := by rfl
theorem bound34 : entries34.map CheckedRow.row = rows34 := by rfl
theorem choices_and_34 : choices rows34 167837696#32 (-1) = [] := by rfl
theorem choices_orr_34 : choices rows34 704708608#32 (-1) = [] := by rfl
theorem choices_eor_34 : choices rows34 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_34 : choices rows34 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
