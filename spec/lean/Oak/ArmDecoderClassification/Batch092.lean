import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1762 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1762", ") = {\n    SEE = ", "1762", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_single_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1762 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "011011", .any 10], 1762, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_single_decode"⟩
theorem checked1762 : check raw1762 clause1762 = true := by rfl
def row1762 : Row := ⟨1762, 3206609920, 773876736⟩
theorem derived1762 : clause1762.row = row1762 := by rfl
def entry1762 : CheckedRow := ⟨raw1762, clause1762, row1762, checked1762, derived1762⟩

def raw1763 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1763", ") = {\n    SEE = ", "1763", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1763 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000100010", .any 10], 1763, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_int_bulk_simd_decode"⟩
theorem checked1763 : check raw1763 clause1763 = true := by rfl
def row1763 : Row := ⟨1763, 3208641536, 237012992⟩
theorem derived1763 : clause1763.row = row1763 := by rfl
def entry1763 : CheckedRow := ⟨raw1763, clause1763, row1763, checked1763, derived1763⟩

def raw1764 : List String := ["function clause decode64 ((", "0b", "00011001000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "01", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1764", ") = {\n    SEE = ", "1764", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagpost_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1764 : Clause := ⟨[.fixed "00011001000", .any 9, .fixed "01", .any 10], 1764, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagpost_decode"⟩
theorem checked1764 : check raw1764 clause1764 = true := by rfl
def row1764 : Row := ⟨1764, 4292873216, 419431424⟩
theorem derived1764 : clause1764.row = row1764 := by rfl
def entry1764 : CheckedRow := ⟨raw1764, clause1764, row1764, checked1764, derived1764⟩

def raw1765 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "10110101100000000001", " @ ", "_ : bits(", "11", ")", " as op_code) if SEE < ", "1765", ") = {\n    SEE = ", "1765", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_rev_decode", "(", "Rd", ", ", "Rn", ", ", "opc", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1765 : Clause := ⟨[.any 1, .fixed "10110101100000000001", .any 11], 1765, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 2, 11, 10, false⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_rev_decode"⟩
theorem checked1765 : check raw1765 clause1765 = true := by rfl
def row1765 : Row := ⟨1765, 2147481600, 1522534400⟩
theorem derived1765 : clause1765.row = row1765 := by rfl
def entry1765 : CheckedRow := ⟨raw1765, clause1765, row1765, checked1765, derived1765⟩

def raw1766 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000100110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1766", ") = {\n    SEE = ", "1766", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1766 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100000100110", .any 10], 1766, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_int_bulk_simd_decode"⟩
theorem checked1766 : check raw1766 clause1766 = true := by rfl
def row1766 : Row := ⟨1766, 3208641536, 773888000⟩
theorem derived1766 : clause1766.row = row1766 := by rfl
def entry1766 : CheckedRow := ⟨raw1766, clause1766, row1766, checked1766, derived1766⟩

def raw1767 : List String := ["function clause decode64 ((", "0b", "001110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1767", ") = {\n    SEE = ", "1767", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1767 : Clause := ⟨[.fixed "001110000", .any 1, .fixed "1", .any 5, .fixed "001100", .any 5, .fixed "11111"], 1767, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1767 : check raw1767 clause1767 = true := by rfl
def row1767 : Row := ⟨1767, 4288740383, 941633567⟩
theorem derived1767 : clause1767.row = row1767 := by rfl
def entry1767 : CheckedRow := ⟨raw1767, clause1767, row1767, checked1767, derived1767⟩

def raw1768 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111011111001100110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1768", ") = {\n    SEE = ", "1768", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1768 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111011111001100110", .any 10], 1768, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_round_decode"⟩
theorem checked1768 : check raw1768 clause1768 = true := by rfl
def row1768 : Row := ⟨1768, 3221224448, 251238400⟩
theorem derived1768 : clause1768.row = row1768 := by rfl
def entry1768 : CheckedRow := ⟨raw1768, clause1768, row1768, checked1768, derived1768⟩

def raw1769 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "10100110", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1769", ") = {\n    SEE = ", "1769", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imms", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "immr", " : bits(", "6", ") = ", "op_code[", "21", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_bitfield_decode", "(", "Rd", ", ", "Rn", ", ", "imms", ", ", "immr", ", ", "N", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1769 : Clause := ⟨[.any 1, .fixed "10100110", .any 23], 1769, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imms", 6, 15, 10, false⟩, ⟨"immr", 6, 21, 16, false⟩, ⟨"N", 1, 22, 22, true⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_bitfield_decode"⟩
theorem checked1769 : check raw1769 clause1769 = true := by rfl
def row1769 : Row := ⟨1769, 2139095040, 1392508928⟩
theorem derived1769 : clause1769.row = row1769 := by rfl
def entry1769 : CheckedRow := ⟨raw1769, clause1769, row1769, checked1769, derived1769⟩

def entries92 : List CheckedRow := [entry1762, entry1763, entry1764, entry1765, entry1766, entry1767, entry1768, entry1769]
def rows92 : List Row := [row1762, row1763, row1764, row1765, row1766, row1767, row1768, row1769]
theorem indices92 : rows92.map Row.index = [1762, 1763, 1764, 1765, 1766, 1767, 1768, 1769] := by rfl
theorem bound92 : entries92.map CheckedRow.row = rows92 := by rfl
theorem choices_and_92 : choices rows92 167837696#32 (-1) = [] := by rfl
theorem choices_orr_92 : choices rows92 704708608#32 (-1) = [] := by rfl
theorem choices_eor_92 : choices rows92 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_92 : choices rows92 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
