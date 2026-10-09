import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1690 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111010110000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1690", ") = {\n    SEE = ", "1690", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_fp16maxnm_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1690 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111010110000110010", .any 10], 1690, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_fp16maxnm_simd_decode"⟩
theorem checked1690 : check raw1690 clause1690 = true := by rfl
def row1690 : Row := ⟨1690, 3221224448, 246466560⟩
theorem derived1690 : clause1690.row = row1690 := by rfl
def entry1690 : CheckedRow := ⟨raw1690, clause1690, row1690, checked1690, derived1690⟩

def raw1691 : List String := ["function clause decode64 ((", "0b", "10011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1691", ") = {\n    SEE = ", "1691", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode2", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_pacga_dp_2src_decode", "(", "Rd", ", ", "Rn", ", ", "opcode2", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1691 : Clause := ⟨[.fixed "10011010110", .any 5, .fixed "001100", .any 10], 1691, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode2", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_pacga_dp_2src_decode"⟩
theorem checked1691 : check raw1691 clause1691 = true := by rfl
def row1691 : Row := ⟨1691, 4292934656, 2596286464⟩
theorem derived1691 : clause1691.row = row1691 := by rfl
def entry1691 : CheckedRow := ⟨raw1691, clause1691, row1691, checked1691, derived1691⟩

def raw1692 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0111100000", " @ ", "_ : bits(", "3", ")", " @ ", "0b", "111101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1692", ") = {\n    SEE = ", "1692", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "h", " : bits(", "1", ") = ", "[op_code[", "5", "]]", ";\n", "    ", "g", " : bits(", "1", ") = ", "[op_code[", "6", "]]", ";\n", "    ", "f", " : bits(", "1", ") = ", "[op_code[", "7", "]]", ";\n", "    ", "e", " : bits(", "1", ") = ", "[op_code[", "8", "]]", ";\n", "    ", "d", " : bits(", "1", ") = ", "[op_code[", "9", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "cmode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "c", " : bits(", "1", ") = ", "[op_code[", "16", "]]", ";\n", "    ", "b", " : bits(", "1", ") = ", "[op_code[", "17", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "18", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_logical_decode", "(", "Rd", ", ", "h", ", ", "g", ", ", "f", ", ", "e", ", ", "d", ", ", "o2", ", ", "cmode", ", ", "c", ", ", "b", ", ", "a", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1692 : Clause := ⟨[.fixed "0", .any 2, .fixed "0111100000", .any 3, .fixed "111101", .any 10], 1692, [⟨"Rd", 5, 4, 0, false⟩, ⟨"h", 1, 5, 5, true⟩, ⟨"g", 1, 6, 6, true⟩, ⟨"f", 1, 7, 7, true⟩, ⟨"e", 1, 8, 8, true⟩, ⟨"d", 1, 9, 9, true⟩, ⟨"o2", 1, 11, 11, true⟩, ⟨"cmode", 4, 15, 12, false⟩, ⟨"c", 1, 16, 16, true⟩, ⟨"b", 1, 17, 17, true⟩, ⟨"a", 1, 18, 18, true⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_logical_decode"⟩
theorem checked1692 : check raw1692 clause1692 = true := by rfl
def row1692 : Row := ⟨1692, 2683894784, 251720704⟩
theorem derived1692 : clause1692.row = row1692 := by rfl
def entry1692 : CheckedRow := ⟨raw1692, clause1692, row1692, checked1692, derived1692⟩

def raw1693 : List String := ["function clause decode64 ((", "0b", "00011001001", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1693", ") = {\n    SEE = ", "1693", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagpair_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1693 : Clause := ⟨[.fixed "00011001001", .any 9, .fixed "10", .any 10], 1693, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagpair_decode"⟩
theorem checked1693 : check raw1693 clause1693 = true := by rfl
def row1693 : Row := ⟨1693, 4292873216, 421529600⟩
theorem derived1693 : clause1693.row = row1693 := by rfl
def entry1693 : CheckedRow := ⟨raw1693, clause1693, row1693, checked1693, derived1693⟩

def raw1694 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "01100110", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1694", ") = {\n    SEE = ", "1694", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imms", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "immr", " : bits(", "6", ") = ", "op_code[", "21", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_bitfield_decode", "(", "Rd", ", ", "Rn", ", ", "imms", ", ", "immr", ", ", "N", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1694 : Clause := ⟨[.any 1, .fixed "01100110", .any 23], 1694, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imms", 6, 15, 10, false⟩, ⟨"immr", 6, 21, 16, false⟩, ⟨"N", 1, 22, 22, true⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_bitfield_decode"⟩
theorem checked1694 : check raw1694 clause1694 = true := by rfl
def row1694 : Row := ⟨1694, 2139095040, 855638016⟩
theorem derived1694 : clause1694.row = row1694 := by rfl
def entry1694 : CheckedRow := ⟨raw1694, clause1694, row1694, checked1694, derived1694⟩

def raw1695 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0101", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1695", ") = {\n    SEE = ", "1695", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "sz", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "C", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode2_5_3_", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_crc_decode", "(", "Rd", ", ", "Rn", ", ", "sz", ", ", "C", ", ", "opcode2_5_3_", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1695 : Clause := ⟨[.any 1, .fixed "0011010110", .any 5, .fixed "0101", .any 12], 1695, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"sz", 2, 11, 10, false⟩, ⟨"C", 1, 12, 12, true⟩, ⟨"opcode2_5_3_", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_crc_decode"⟩
theorem checked1695 : check raw1695 clause1695 = true := by rfl
def row1695 : Row := ⟨1695, 2145447936, 448811008⟩
theorem derived1695 : clause1695.row = row1695 := by rfl
def entry1695 : CheckedRow := ⟨raw1695, clause1695, row1695, checked1695, derived1695⟩

def raw1696 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111100000", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1696", ") = {\n    SEE = ", "1696", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "h", " : bits(", "1", ") = ", "[op_code[", "5", "]]", ";\n", "    ", "g", " : bits(", "1", ") = ", "[op_code[", "6", "]]", ";\n", "    ", "f", " : bits(", "1", ") = ", "[op_code[", "7", "]]", ";\n", "    ", "e", " : bits(", "1", ") = ", "[op_code[", "8", "]]", ";\n", "    ", "d", " : bits(", "1", ") = ", "[op_code[", "9", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "cmode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "c", " : bits(", "1", ") = ", "[op_code[", "16", "]]", ";\n", "    ", "b", " : bits(", "1", ") = ", "[op_code[", "17", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "18", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_logical_decode", "(", "Rd", ", ", "h", ", ", "g", ", ", "f", ", ", "e", ", ", "d", ", ", "o2", ", ", "cmode", ", ", "c", ", ", "b", ", ", "a", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1696 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111100000", .any 7, .fixed "01", .any 10], 1696, [⟨"Rd", 5, 4, 0, false⟩, ⟨"h", 1, 5, 5, true⟩, ⟨"g", 1, 6, 6, true⟩, ⟨"f", 1, 7, 7, true⟩, ⟨"e", 1, 8, 8, true⟩, ⟨"d", 1, 9, 9, true⟩, ⟨"o2", 1, 11, 11, true⟩, ⟨"cmode", 4, 15, 12, false⟩, ⟨"c", 1, 16, 16, true⟩, ⟨"b", 1, 17, 17, true⟩, ⟨"a", 1, 18, 18, true⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_logical_decode"⟩
theorem checked1696 : check raw1696 clause1696 = true := by rfl
def row1696 : Row := ⟨1696, 3220704256, 788530176⟩
theorem derived1696 : clause1696.row = row1696 := by rfl
def entry1696 : CheckedRow := ⟨raw1696, clause1696, row1696, checked1696, derived1696⟩

def raw1697 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111001111001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1697", ") = {\n    SEE = ", "1697", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1697 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111001111001101110", .any 10], 1697, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_simd_decode"⟩
theorem checked1697 : check raw1697 clause1697 = true := by rfl
def row1697 : Row := ⟨1697, 3221224448, 779728896⟩
theorem derived1697 : clause1697.row = row1697 := by rfl
def entry1697 : CheckedRow := ⟨raw1697, clause1697, row1697, checked1697, derived1697⟩

def entries83 : List CheckedRow := [entry1690, entry1691, entry1692, entry1693, entry1694, entry1695, entry1696, entry1697]
def rows83 : List Row := [row1690, row1691, row1692, row1693, row1694, row1695, row1696, row1697]
theorem indices83 : rows83.map Row.index = [1690, 1691, 1692, 1693, 1694, 1695, 1696, 1697] := by rfl
theorem bound83 : entries83.map CheckedRow.row = rows83 := by rfl
theorem choices_and_83 : choices rows83 167837696#32 (-1) = [] := by rfl
theorem choices_orr_83 : choices rows83 704708608#32 (-1) = [] := by rfl
theorem choices_eor_83 : choices rows83 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_83 : choices rows83 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
