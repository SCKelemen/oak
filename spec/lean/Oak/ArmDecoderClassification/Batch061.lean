import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1514 : List String := ["function clause decode64 ((", "0b", "10111000100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1514", ") = {\n    SEE = ", "1514", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1514 : Clause := ⟨[.fixed "10111000100", .any 9, .fixed "00", .any 10], 1514, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1514 : check raw1514 clause1514 = true := by rfl
def row1514 : Row := ⟨1514, 4292873216, 3095396352⟩
theorem derived1514 : clause1514.row = row1514 := by rfl
def entry1514 : CheckedRow := ⟨raw1514, clause1514, row1514, checked1514, derived1514⟩

def raw1515 : List String := ["function clause decode64 ((", "0b", "01111000000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1515", ") = {\n    SEE = ", "1515", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1515 : Clause := ⟨[.fixed "01111000000", .any 9, .fixed "00", .any 10], 1515, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_normal_memory_single_general_immediate_signed_offset_normal__decode"⟩
theorem checked1515 : check raw1515 clause1515 = true := by rfl
def row1515 : Row := ⟨1515, 4292873216, 2013265920⟩
theorem derived1515 : clause1515.row = row1515 := by rfl
def entry1515 : CheckedRow := ⟨raw1515, clause1515, row1515, checked1515, derived1515⟩

def raw1516 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1516", ") = {\n    SEE = ", "1516", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_mul_product_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1516 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "000010", .any 10], 1516, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_mul_product_decode"⟩
theorem checked1516 : check raw1516 clause1516 = true := by rfl
def row1516 : Row := ⟨1516, 4280351744, 505415680⟩
theorem derived1516 : clause1516.row = row1516 := by rfl
def entry1516 : CheckedRow := ⟨raw1516, clause1516, row1516, checked1516, derived1516⟩

def raw1517 : List String := ["function clause decode64 ((", "0b", "1101010100000011001000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1517", ") = {\n    SEE = ", "1517", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "integer_pac_pacia_hint_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1517 : Clause := ⟨[.fixed "1101010100000011001000", .any 1, .fixed "100", .any 1, .fixed "11111"], 1517, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "integer_pac_pacia_hint_decode"⟩
theorem checked1517 : check raw1517 clause1517 = true := by rfl
def row1517 : Row := ⟨1517, 4294966751, 3573752095⟩
theorem derived1517 : clause1517.row = row1517 := by rfl
def entry1517 : CheckedRow := ⟨raw1517, clause1517, row1517, checked1517, derived1517⟩

def raw1518 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110000000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1518", ") = {\n    SEE = ", "1518", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1518 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "110000000000", .any 10], 1518, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1518 : check raw1518 clause1518 = true := by rfl
def row1518 : Row := ⟨1518, 2134899712, 506462208⟩
theorem derived1518 : clause1518.row = row1518 := by rfl
def entry1518 : CheckedRow := ⟨raw1518, clause1518, row1518, checked1518, derived1518⟩

def raw1519 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1519", ") = {\n    SEE = ", "1519", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_saturating_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1519 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "000011", .any 10], 1519, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_saturating_simd_decode"⟩
theorem checked1519 : check raw1519 clause1519 = true := by rfl
def row1519 : Row := ⟨1519, 3206609920, 236981248⟩
theorem derived1519 : clause1519.row = row1519 := by rfl
def entry1519 : CheckedRow := ⟨raw1519, clause1519, row1519, checked1519, derived1519⟩

def raw1520 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "000", " as op_code) if SEE < ", "1520", ") = {\n    SEE = ", "1520", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "4", " .. ", "3", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "2", ") = ", "op_code[", "15", " .. ", "14", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_compare_uncond_decode", "(", "opc", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1520 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 5, .fixed "001000", .any 5, .fixed "1", .any 1, .fixed "000"], 1520, [⟨"opc", 2, 4, 3, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 2, 15, 14, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_compare_uncond_decode"⟩
theorem checked1520 : check raw1520 clause1520 = true := by rfl
def row1520 : Row := ⟨1520, 4280351767, 505421840⟩
theorem derived1520 : clause1520.row = row1520 := by rfl
def entry1520 : CheckedRow := ⟨raw1520, clause1520, row1520, checked1520, derived1520⟩

def raw1521 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1521", ") = {\n    SEE = ", "1521", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_addsub_narrow_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1521 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "010000", .any 10], 1521, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_addsub_narrow_decode"⟩
theorem checked1521 : check raw1521 clause1521 = true := by rfl
def row1521 : Row := ⟨1521, 3206609920, 236994560⟩
theorem derived1521 : clause1521.row = row1521 := by rfl
def entry1521 : CheckedRow := ⟨raw1521, clause1521, row1521, checked1521, derived1521⟩

def entries61 : List CheckedRow := [entry1514, entry1515, entry1516, entry1517, entry1518, entry1519, entry1520, entry1521]
def rows61 : List Row := [row1514, row1515, row1516, row1517, row1518, row1519, row1520, row1521]
theorem indices61 : rows61.map Row.index = [1514, 1515, 1516, 1517, 1518, 1519, 1520, 1521] := by rfl
theorem bound61 : entries61.map CheckedRow.row = rows61 := by rfl
theorem choices_and_61 : choices rows61 167837696#32 (-1) = [] := by rfl
theorem choices_orr_61 : choices rows61 704708608#32 (-1) = [] := by rfl
theorem choices_eor_61 : choices rows61 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_61 : choices rows61 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
