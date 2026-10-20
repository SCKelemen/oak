import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1610 : List String := ["function clause decode64 ((", "0b", "11010101000000000100", " @ ", "_ : bits(", "4", ")", " @ ", "0b", "01011111", " as op_code) if SEE < ", "1610", ") = {\n    SEE = ", "1610", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "integer_flags_axflag_decode", "(", "CRm", ")\n}\n"]
def clause1610 : Clause := ⟨[.fixed "11010101000000000100", .any 4, .fixed "01011111"], 1610, [⟨"CRm", 4, 11, 8, false⟩], "integer_flags_axflag_decode"⟩
theorem checked1610 : check raw1610 clause1610 = true := by rfl
def row1610 : Row := ⟨1610, 4294963455, 3573563487⟩
theorem derived1610 : clause1610.row = row1610 := by rfl
def entry1610 : CheckedRow := ⟨raw1610, clause1610, row1610, checked1610, derived1610⟩

def raw1611 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1611", ") = {\n    SEE = ", "1611", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_single_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1611 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "011001", .any 10], 1611, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_single_decode"⟩
theorem checked1611 : check raw1611 clause1611 = true := by rfl
def row1611 : Row := ⟨1611, 3206609920, 773874688⟩
theorem derived1611 : clause1611.row = row1611 := by rfl
def entry1611 : CheckedRow := ⟨raw1611, clause1611, row1611, checked1611, derived1611⟩

def raw1612 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1612", ") = {\n    SEE = ", "1612", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_int_accum_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1612 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "100101", .any 10], 1612, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_mul_int_accum_decode"⟩
theorem checked1612 : check raw1612 clause1612 = true := by rfl
def row1612 : Row := ⟨1612, 3206609920, 237016064⟩
theorem derived1612 : clause1612.row = row1612 := by rfl
def entry1612 : CheckedRow := ⟨raw1612, clause1612, row1612, checked1612, derived1612⟩

def raw1613 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100010000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1613", ") = {\n    SEE = ", "1613", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1613 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "100010000000", .any 10], 1613, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1613 : check raw1613 clause1613 = true := by rfl
def row1613 : Row := ⟨1613, 2134899712, 505544704⟩
theorem derived1613 : clause1613.row = row1613 := by rfl
def entry1613 : CheckedRow := ⟨raw1613, clause1613, row1613, checked1613, derived1613⟩

def raw1614 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "00100100", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1614", ") = {\n    SEE = ", "1614", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imms", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "immr", " : bits(", "6", ") = ", "op_code[", "21", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_immediate_decode", "(", "Rd", ", ", "Rn", ", ", "imms", ", ", "immr", ", ", "N", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1614 : Clause := ⟨[.any 1, .fixed "00100100", .any 23], 1614, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imms", 6, 15, 10, false⟩, ⟨"immr", 6, 21, 16, false⟩, ⟨"N", 1, 22, 22, true⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_immediate_decode"⟩
theorem checked1614 : check raw1614 clause1614 = true := by rfl
def row1614 : Row := ⟨1614, 2139095040, 301989888⟩
theorem derived1614 : clause1614.row = row1614 := by rfl
def entry1614 : CheckedRow := ⟨raw1614, clause1614, row1614, checked1614, derived1614⟩

def raw1615 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1615", ") = {\n    SEE = ", "1615", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp_1985_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1615 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "1", .any 5, .fixed "111101", .any 10], 1615, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp_1985_decode"⟩
theorem checked1615 : check raw1615 clause1615 = true := by rfl
def row1615 : Row := ⟨1615, 3214998528, 237040640⟩
theorem derived1615 : clause1615.row = row1615 := by rfl
def entry1615 : CheckedRow := ⟨raw1615, clause1615, row1615, checked1615, derived1615⟩

def raw1616 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1111010010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "4", ")", " as op_code) if SEE < ", "1616", ") = {\n    SEE = ", "1616", ";\n", "    ", "nzcv", " : bits(", "4", ") = ", "op_code[", "3", " .. ", "0", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "4", "]]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_conditional_compare_immediate_decode", "(", "nzcv", ", ", "o3", ", ", "Rn", ", ", "o2", ", ", "cond", ", ", "imm5", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1616 : Clause := ⟨[.any 1, .fixed "1111010010", .any 9, .fixed "10", .any 5, .fixed "0", .any 4], 1616, [⟨"nzcv", 4, 3, 0, false⟩, ⟨"o3", 1, 4, 4, true⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o2", 1, 10, 10, true⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"imm5", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_conditional_compare_immediate_decode"⟩
theorem checked1616 : check raw1616 clause1616 = true := by rfl
def row1616 : Row := ⟨1616, 2145389584, 2051016704⟩
theorem derived1616 : clause1616.row = row1616 := by rfl
def entry1616 : CheckedRow := ⟨raw1616, clause1616, row1616, checked1616, derived1616⟩

def raw1617 : List String := ["function clause decode64 ((", "0b", "010111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100000111010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1617", ") = {\n    SEE = ", "1617", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_float_lessthan_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1617 : Clause := ⟨[.fixed "010111101", .any 1, .fixed "100000111010", .any 10], 1617, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_float_lessthan_sisd_decode"⟩
theorem checked1617 : check raw1617 clause1617 = true := by rfl
def row1617 : Row := ⟨1617, 4290771968, 1587603456⟩
theorem derived1617 : clause1617.row = row1617 := by rfl
def entry1617 : CheckedRow := ⟨raw1617, clause1617, row1617, checked1617, derived1617⟩

def entries73 : List CheckedRow := [entry1610, entry1611, entry1612, entry1613, entry1614, entry1615, entry1616, entry1617]
def rows73 : List Row := [row1610, row1611, row1612, row1613, row1614, row1615, row1616, row1617]
theorem indices73 : rows73.map Row.index = [1610, 1611, 1612, 1613, 1614, 1615, 1616, 1617] := by rfl
theorem bound73 : entries73.map CheckedRow.row = rows73 := by rfl
theorem choices_and_73 : choices rows73 167837696#32 (-1) = [] := by rfl
theorem choices_orr_73 : choices rows73 704708608#32 (-1) = [] := by rfl
theorem choices_eor_73 : choices rows73 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_73 : choices rows73 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
