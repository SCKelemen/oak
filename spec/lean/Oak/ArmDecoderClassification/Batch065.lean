import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1546 : List String := ["function clause decode64 ((", "0b", "011111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1546", ") = {\n    SEE = ", "1546", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_right_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1546 : Clause := ⟨[.fixed "011111110", .any 7, .fixed "001101", .any 10], 1546, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_right_sisd_decode"⟩
theorem checked1546 : check raw1546 clause1546 = true := by rfl
def row1546 : Row := ⟨1546, 4286643200, 2130719744⟩
theorem derived1546 : clause1546.row = row1546 := by rfl
def entry1546 : CheckedRow := ⟨raw1546, clause1546, row1546, checked1546, derived1546⟩

def raw1547 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1547", ") = {\n    SEE = ", "1547", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_right_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1547 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "001001", .any 10], 1547, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_right_simd_decode"⟩
theorem checked1547 : check raw1547 clause1547 = true := by rfl
def row1547 : Row := ⟨1547, 3212901376, 251667456⟩
theorem derived1547 : clause1547.row = row1547 := by rfl
def entry1547 : CheckedRow := ⟨raw1547, clause1547, row1547, checked1547, derived1547⟩

def raw1548 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001001010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1548", ") = {\n    SEE = ", "1548", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_extract_sqxtun_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1548 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100001001010", .any 10], 1548, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_extract_sqxtun_simd_decode"⟩
theorem checked1548 : check raw1548 clause1548 = true := by rfl
def row1548 : Row := ⟨1548, 3208641536, 773924864⟩
theorem derived1548 : clause1548.row = row1548 := by rfl
def entry1548 : CheckedRow := ⟨raw1548, clause1548, row1548, checked1548, derived1548⟩

def raw1549 : List String := ["function clause decode64 ((", "0b", "00111000101", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1549", ") = {\n    SEE = ", "1549", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_orderedrcpc_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1549 : Clause := ⟨[.fixed "00111000101", .any 5, .fixed "110000", .any 10], 1549, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_orderedrcpc_decode"⟩
theorem checked1549 : check raw1549 clause1549 = true := by rfl
def row1549 : Row := ⟨1549, 4292934656, 950059008⟩
theorem derived1549 : clause1549.row = row1549 := by rfl
def entry1549 : CheckedRow := ⟨raw1549, clause1549, row1549, checked1549, derived1549⟩

def raw1550 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1550", ") = {\n    SEE = ", "1550", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_rightnarrow_nonuniform_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1550 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "100001", .any 10], 1550, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_rightnarrow_nonuniform_simd_decode"⟩
theorem checked1550 : check raw1550 clause1550 = true := by rfl
def row1550 : Row := ⟨1550, 3212901376, 788562944⟩
theorem derived1550 : clause1550.row = row1550 := by rfl
def entry1550 : CheckedRow := ⟨raw1550, clause1550, row1550, checked1550, derived1550⟩

def raw1551 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1551", ") = {\n    SEE = ", "1551", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ")\n}\n"]
def clause1551 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "1", .any 5, .fixed "111011", .any 10], 1551, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode"⟩
theorem checked1551 : check raw1551 clause1551 = true := by rfl
def row1551 : Row := ⟨1551, 4288740352, 2124475392⟩
theorem derived1551 : clause1551.row = row1551 := by rfl
def entry1551 : CheckedRow := ⟨raw1551, clause1551, row1551, checked1551, derived1551⟩

def raw1552 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111001100000010110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1552", ") = {\n    SEE = ", "1552", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_rbit_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1552 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111001100000010110", .any 10], 1552, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_rbit_decode"⟩
theorem checked1552 : check raw1552 clause1552 = true := by rfl
def row1552 : Row := ⟨1552, 3221224448, 778065920⟩
theorem derived1552 : clause1552.row = row1552 := by rfl
def entry1552 : CheckedRow := ⟨raw1552, clause1552, row1552, checked1552, derived1552⟩

def raw1553 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1553", ") = {\n    SEE = ", "1553", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1553 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "100000110110", .any 10], 1553, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_float_bulk_simd_decode"⟩
theorem checked1553 : check raw1553 clause1553 = true := by rfl
def row1553 : Row := ⟨1553, 3217030144, 782292992⟩
theorem derived1553 : clause1553.row = row1553 := by rfl
def entry1553 : CheckedRow := ⟨raw1553, clause1553, row1553, checked1553, derived1553⟩

def entries65 : List CheckedRow := [entry1546, entry1547, entry1548, entry1549, entry1550, entry1551, entry1552, entry1553]
def rows65 : List Row := [row1546, row1547, row1548, row1549, row1550, row1551, row1552, row1553]
theorem indices65 : rows65.map Row.index = [1546, 1547, 1548, 1549, 1550, 1551, 1552, 1553] := by rfl
theorem bound65 : entries65.map CheckedRow.row = rows65 := by rfl
theorem choices_and_65 : choices rows65 167837696#32 (-1) = [] := by rfl
theorem choices_orr_65 : choices rows65 704708608#32 (-1) = [] := by rfl
theorem choices_eor_65 : choices rows65 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_65 : choices rows65 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
