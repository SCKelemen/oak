import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1522 : List String := ["function clause decode64 ((", "0b", "1101011001011111000000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "00000", " as op_code) if SEE < ", "1522", ") = {\n    SEE = ", "1522", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "22", " .. ", "21", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "branch_unconditional_register_decode", "(", "Rm", ", ", "Rn", ", ", "M", ", ", "A", ", ", "op2", ", ", "op", ", ", "Z", ")\n}\n"]
def clause1522 : Clause := ⟨[.fixed "1101011001011111000000", .any 5, .fixed "00000"], 1522, [⟨"Rm", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"M", 1, 10, 10, true⟩, ⟨"A", 1, 11, 11, true⟩, ⟨"op2", 5, 20, 16, false⟩, ⟨"op", 2, 22, 21, false⟩, ⟨"Z", 1, 24, 24, true⟩], "branch_unconditional_register_decode"⟩
theorem checked1522 : check raw1522 clause1522 = true := by rfl
def row1522 : Row := ⟨1522, 4294966303, 3596550144⟩
theorem derived1522 : clause1522.row = row1522 := by rfl
def entry1522 : CheckedRow := ⟨raw1522, clause1522, row1522, checked1522, derived1522⟩

def raw1523 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "10001", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "10000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1523", ") = {\n    SEE = ", "1523", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "16", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_fp_decode", "(", "Rd", ", ", "Rn", ", ", "opc", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1523 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "10001", .any 2, .fixed "10000", .any 10], 1523, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 2, 16, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_convert_fp_decode"⟩
theorem checked1523 : check raw1523 clause1523 = true := by rfl
def row1523 : Row := ⟨1523, 4282285056, 505561088⟩
theorem derived1523 : clause1523.row = row1523 := by rfl
def entry1523 : CheckedRow := ⟨raw1523, clause1523, row1523, checked1523, derived1523⟩

def raw1524 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001000010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1524", ") = {\n    SEE = ", "1524", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1524 : Clause := ⟨[.fixed "1", .any 1, .fixed "001000010", .any 5, .fixed "1", .any 15], 1524, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1524 : check raw1524 clause1524 = true := by rfl
def row1524 : Row := ⟨1524, 3219161088, 2285928448⟩
theorem derived1524 : clause1524.row = row1524 := by rfl
def entry1524 : CheckedRow := ⟨raw1524, clause1524, row1524, checked1524, derived1524⟩

def raw1525 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000010010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1525", ") = {\n    SEE = ", "1525", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_clsz_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1525 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100000010010", .any 10], 1525, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_clsz_decode"⟩
theorem checked1525 : check raw1525 clause1525 = true := by rfl
def row1525 : Row := ⟨1525, 3208641536, 773867520⟩
theorem derived1525 : clause1525.row = row1525 := by rfl
def entry1525 : CheckedRow := ⟨raw1525, clause1525, row1525, checked1525, derived1525⟩

def raw1526 : List String := ["function clause decode64 ((", "0b", "00011001001", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1526", ") = {\n    SEE = ", "1526", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagpairpost_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1526 : Clause := ⟨[.fixed "00011001001", .any 9, .fixed "01", .any 10], 1526, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagpairpost_decode"⟩
theorem checked1526 : check raw1526 clause1526 = true := by rfl
def row1526 : Row := ⟨1526, 4292873216, 421528576⟩
theorem derived1526 : clause1526.row = row1526 := by rfl
def entry1526 : CheckedRow := ⟨raw1526, clause1526, row1526, checked1526, derived1526⟩

def raw1527 : List String := ["function clause decode64 ((", "0b", "00111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1527", ") = {\n    SEE = ", "1527", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1527 : Clause := ⟨[.fixed "00111000000", .any 9, .fixed "11", .any 10], 1527, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_preidx_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1527 : check raw1527 clause1527 = true := by rfl
def row1527 : Row := ⟨1527, 4292873216, 939527168⟩
theorem derived1527 : clause1527.row = row1527 := by rfl
def entry1527 : CheckedRow := ⟨raw1527, clause1527, row1527, checked1527, derived1527⟩

def raw1528 : List String := ["function clause decode64 ((", "0b", "110110101100000100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1528", ") = {\n    SEE = ", "1528", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_pacib_dp_1src_decode", "(", "Rd", ", ", "Rn", ", ", "Z", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1528 : Clause := ⟨[.fixed "110110101100000100", .any 1, .fixed "001", .any 10], 1528, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Z", 1, 13, 13, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_pacib_dp_1src_decode"⟩
theorem checked1528 : check raw1528 clause1528 = true := by rfl
def row1528 : Row := ⟨1528, 4294958080, 3670082560⟩
theorem derived1528 : clause1528.row = row1528 := by rfl
def entry1528 : CheckedRow := ⟨raw1528, clause1528, row1528, checked1528, derived1528⟩

def raw1529 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1529", ") = {\n    SEE = ", "1529", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1529 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "10", .any 1, .fixed "11", .any 1, .fixed "000000", .any 10], 1529, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1529 : check raw1529 clause1529 = true := by rfl
def row1529 : Row := ⟨1529, 2134309888, 505806848⟩
theorem derived1529 : clause1529.row = row1529 := by rfl
def entry1529 : CheckedRow := ⟨raw1529, clause1529, row1529, checked1529, derived1529⟩

def entries62 : List CheckedRow := [entry1522, entry1523, entry1524, entry1525, entry1526, entry1527, entry1528, entry1529]
def rows62 : List Row := [row1522, row1523, row1524, row1525, row1526, row1527, row1528, row1529]
theorem indices62 : rows62.map Row.index = [1522, 1523, 1524, 1525, 1526, 1527, 1528, 1529] := by rfl
theorem bound62 : entries62.map CheckedRow.row = rows62 := by rfl
theorem choices_and_62 : choices rows62 167837696#32 (-1) = [] := by rfl
theorem choices_orr_62 : choices rows62 704708608#32 (-1) = [] := by rfl
theorem choices_eor_62 : choices rows62 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_62 : choices rows62 3596551104#32 (-1) = [1522] := by rfl

end Oak.ArmDecoderClassification.Data
