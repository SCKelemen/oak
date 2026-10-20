import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1698 : List String := ["function clause decode64 ((", "0b", "1101010100000011001000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1698", ") = {\n    SEE = ", "1698", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "integer_pac_autia_hint_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1698 : Clause := ⟨[.fixed "1101010100000011001000", .any 1, .fixed "110", .any 1, .fixed "11111"], 1698, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "integer_pac_autia_hint_decode"⟩
theorem checked1698 : check raw1698 clause1698 = true := by rfl
def row1698 : Row := ⟨1698, 4294966751, 3573752223⟩
theorem derived1698 : clause1698.row = row1698 := by rfl
def entry1698 : CheckedRow := ⟨raw1698, clause1698, row1698, checked1698, derived1698⟩

def raw1699 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1699", ") = {\n    SEE = ", "1699", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1699 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "001001", .any 10], 1699, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_sub_int_decode"⟩
theorem checked1699 : check raw1699 clause1699 = true := by rfl
def row1699 : Row := ⟨1699, 3206609920, 236987392⟩
theorem derived1699 : clause1699.row = row1699 := by rfl
def entry1699 : CheckedRow := ⟨raw1699, clause1699, row1699, checked1699, derived1699⟩

def raw1700 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1700", ") = {\n    SEE = ", "1700", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_tieaway_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1700 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "100001110010", .any 10], 1700, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_float_tieaway_simd_decode"⟩
theorem checked1700 : check raw1700 clause1700 = true := by rfl
def row1700 : Row := ⟨1700, 3217030144, 773965824⟩
theorem derived1700 : clause1700.row = row1700 := by rfl
def entry1700 : CheckedRow := ⟨raw1700, clause1700, row1700, checked1700, derived1700⟩

def raw1701 : List String := ["function clause decode64 ((", "0b", "0111111011111000110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1701", ") = {\n    SEE = ", "1701", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "a", ", ", "U", ")\n}\n"]
def clause1701 : Clause := ⟨[.fixed "0111111011111000110110", .any 10], 1701, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode"⟩
theorem checked1701 : check raw1701 clause1701 = true := by rfl
def row1701 : Row := ⟨1701, 4294966272, 2130237440⟩
theorem derived1701 : clause1701.row = row1701 := by rfl
def entry1701 : CheckedRow := ⟨raw1701, clause1701, row1701, checked1701, derived1701⟩

def raw1702 : List String := ["function clause decode64 ((", "0b", "0111111011111000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1702", ") = {\n    SEE = ", "1702", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "a", ", ", "U", ")\n}\n"]
def clause1702 : Clause := ⟨[.fixed "0111111011111000110010", .any 10], 1702, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_fp16_bulk_sisd_decode"⟩
theorem checked1702 : check raw1702 clause1702 = true := by rfl
def row1702 : Row := ⟨1702, 4294966272, 2130233344⟩
theorem derived1702 : clause1702.row = row1702 := by rfl
def entry1702 : CheckedRow := ⟨raw1702, clause1702, row1702, checked1702, derived1702⟩

def raw1703 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0111010000", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "00001", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "4", ")", " as op_code) if SEE < ", "1703", ") = {\n    SEE = ", "1703", ";\n", "    ", "mask", " : bits(", "4", ") = ", "op_code[", "3", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "20", " .. ", "15", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_flags_rmif_decode", "(", "mask", ", ", "Rn", ", ", "imm6", ", ", "sf", ")\n}\n"]
def clause1703 : Clause := ⟨[.any 1, .fixed "0111010000", .any 6, .fixed "00001", .any 5, .fixed "0", .any 4], 1703, [⟨"mask", 4, 3, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 20, 15, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_flags_rmif_decode"⟩
theorem checked1703 : check raw1703 clause1703 = true := by rfl
def row1703 : Row := ⟨1703, 2145418256, 973079552⟩
theorem derived1703 : clause1703.row = row1703 := by rfl
def entry1703 : CheckedRow := ⟨raw1703, clause1703, row1703, checked1703, derived1703⟩

def raw1704 : List String := ["function clause decode64 ((", "0b", "11010100000", " @ ", "_ : bits(", "16", ")", " @ ", "0b", "00001", " as op_code) if SEE < ", "1704", ") = {\n    SEE = ", "1704", ";\n", "    ", "LL", " : bits(", "2", ") = ", "op_code[", "1", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "4", " .. ", "2", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "23", " .. ", "21", "]", ";\n", "    ", "system_exceptions_runtime_svc_decode", "(", "LL", ", ", "op2", ", ", "imm16", ", ", "opc", ")\n}\n"]
def clause1704 : Clause := ⟨[.fixed "11010100000", .any 16, .fixed "00001"], 1704, [⟨"LL", 2, 1, 0, false⟩, ⟨"op2", 3, 4, 2, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"opc", 3, 23, 21, false⟩], "system_exceptions_runtime_svc_decode"⟩
theorem checked1704 : check raw1704 clause1704 = true := by rfl
def row1704 : Row := ⟨1704, 4292870175, 3556769793⟩
theorem derived1704 : clause1704.row = row1704 := by rfl
def entry1704 : CheckedRow := ⟨raw1704, clause1704, row1704, checked1704, derived1704⟩

def raw1705 : List String := ["function clause decode64 ((", "0b", "00111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1705", ") = {\n    SEE = ", "1705", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1705 : Clause := ⟨[.fixed "00111000", .any 2, .fixed "1", .any 5, .fixed "011000", .any 10], 1705, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1705 : check raw1705 clause1705 = true := by rfl
def row1705 : Row := ⟨1705, 4280351744, 941645824⟩
theorem derived1705 : clause1705.row = row1705 := by rfl
def entry1705 : CheckedRow := ⟨raw1705, clause1705, row1705, checked1705, derived1705⟩

def entries84 : List CheckedRow := [entry1698, entry1699, entry1700, entry1701, entry1702, entry1703, entry1704, entry1705]
def rows84 : List Row := [row1698, row1699, row1700, row1701, row1702, row1703, row1704, row1705]
theorem indices84 : rows84.map Row.index = [1698, 1699, 1700, 1701, 1702, 1703, 1704, 1705] := by rfl
theorem bound84 : entries84.map CheckedRow.row = rows84 := by rfl
theorem choices_and_84 : choices rows84 167837696#32 (-1) = [] := by rfl
theorem choices_orr_84 : choices rows84 704708608#32 (-1) = [] := by rfl
theorem choices_eor_84 : choices rows84 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_84 : choices rows84 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
