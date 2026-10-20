import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1730 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100111110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1730", ") = {\n    SEE = ", "1730", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "rmode", " : bits(", "3", ") = ", "op_code[", "17", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_round_frint_decode", "(", "Rd", ", ", "Rn", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1730 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100111110000", .any 10], 1730, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"rmode", 3, 17, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_round_frint_decode"⟩
theorem checked1730 : check raw1730 clause1730 = true := by rfl
def row1730 : Row := ⟨1730, 4282383360, 505921536⟩
theorem derived1730 : clause1730.row = row1730 := by rfl
def entry1730 : CheckedRow := ⟨raw1730, clause1730, row1730, checked1730, derived1730⟩

def raw1731 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110000101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1731", ") = {\n    SEE = ", "1731", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "16", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_intmax_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1731 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "110000101010", .any 10], 1731, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 16, 16, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_intmax_decode"⟩
theorem checked1731 : check raw1731 clause1731 = true := by rfl
def row1731 : Row := ⟨1731, 3208641536, 774940672⟩
theorem derived1731 : clause1731.row = row1731 := by rfl
def entry1731 : CheckedRow := ⟨raw1731, clause1731, row1731, checked1731, derived1731⟩

def raw1732 : List String := ["function clause decode64 ((", "0b", "10011011101", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1732", ") = {\n    SEE = ", "1732", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "op54", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_mul_widening_3264_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "U", ", ", "op54", ", ", "sf", ")\n}\n"]
def clause1732 : Clause := ⟨[.fixed "10011011101", .any 5, .fixed "1", .any 15], 1732, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"U", 1, 23, 23, true⟩, ⟨"op54", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_mul_widening_3264_decode"⟩
theorem checked1732 : check raw1732 clause1732 = true := by rfl
def row1732 : Row := ⟨1732, 4292902912, 2610987008⟩
theorem derived1732 : clause1732.row = row1732 := by rfl
def entry1732 : CheckedRow := ⟨raw1732, clause1732, row1732, checked1732, derived1732⟩

def raw1733 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00110100000000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1733", ") = {\n    SEE = ", "1733", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1733 : Clause := ⟨[.fixed "0", .any 1, .fixed "00110100000000", .any 2, .fixed "0", .any 13], 1733, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1733 : check raw1733 clause1733 = true := by rfl
def row1733 : Row := ⟨1733, 3221168128, 218103808⟩
theorem derived1733 : clause1733.row = row1733 := by rfl
def entry1733 : CheckedRow := ⟨raw1733, clause1733, row1733, checked1733, derived1733⟩

def raw1734 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100101000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1734", ") = {\n    SEE = ", "1734", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1734 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "100101000000", .any 10], 1734, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1734 : check raw1734 clause1734 = true := by rfl
def row1734 : Row := ⟨1734, 2134899712, 505741312⟩
theorem derived1734 : clause1734.row = row1734 := by rfl
def entry1734 : CheckedRow := ⟨raw1734, clause1734, row1734, checked1734, derived1734⟩

def raw1735 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1735", ") = {\n    SEE = ", "1735", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_fpmaxnm_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1735 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "110000110010", .any 10], 1735, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_fpmaxnm_simd_decode"⟩
theorem checked1735 : check raw1735 clause1735 = true := by rfl
def row1735 : Row := ⟨1735, 3217030144, 774948864⟩
theorem derived1735 : clause1735.row = row1735 := by rfl
def entry1735 : CheckedRow := ⟨raw1735, clause1735, row1735, checked1735, derived1735⟩

def raw1736 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1736", ") = {\n    SEE = ", "1736", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_simdfp_immediate_signed_postidx_memory_single_simdfp_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1736 : Clause := ⟨[.any 2, .fixed "111100", .any 1, .fixed "10", .any 9, .fixed "01", .any 10], 1736, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_simdfp_immediate_signed_postidx_memory_single_simdfp_immediate_signed_postidx__decode"⟩
theorem checked1736 : check raw1736 clause1736 = true := by rfl
def row1736 : Row := ⟨1736, 1063259136, 1010828288⟩
theorem derived1736 : clause1736.row = row1736 := by rfl
def entry1736 : CheckedRow := ⟨raw1736, clause1736, row1736, checked1736, derived1736⟩

def raw1737 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "0111", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1737", ") = {\n    SEE = ", "1737", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_double_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1737 : Clause := ⟨[.fixed "0", .any 1, .fixed "001111", .any 8, .fixed "0111", .any 1, .fixed "0", .any 10], 1737, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_double_simd_decode"⟩
theorem checked1737 : check raw1737 clause1737 = true := by rfl
def row1737 : Row := ⟨1737, 3204510720, 251686912⟩
theorem derived1737 : clause1737.row = row1737 := by rfl
def entry1737 : CheckedRow := ⟨raw1737, clause1737, row1737, checked1737, derived1737⟩

def entries88 : List CheckedRow := [entry1730, entry1731, entry1732, entry1733, entry1734, entry1735, entry1736, entry1737]
def rows88 : List Row := [row1730, row1731, row1732, row1733, row1734, row1735, row1736, row1737]
theorem indices88 : rows88.map Row.index = [1730, 1731, 1732, 1733, 1734, 1735, 1736, 1737] := by rfl
theorem bound88 : entries88.map CheckedRow.row = rows88 := by rfl
theorem choices_and_88 : choices rows88 167837696#32 (-1) = [] := by rfl
theorem choices_orr_88 : choices rows88 704708608#32 (-1) = [] := by rfl
theorem choices_eor_88 : choices rows88 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_88 : choices rows88 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
