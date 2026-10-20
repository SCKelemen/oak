import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1706 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000001110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1706", ") = {\n    SEE = ", "1706", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_add_saturating_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1706 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "100000001110", .any 10], 1706, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_add_saturating_sisd_decode"⟩
theorem checked1706 : check raw1706 clause1706 = true := by rfl
def row1706 : Row := ⟨1706, 4282383360, 2116040704⟩
theorem derived1706 : clause1706.row = row1706 := by rfl
def entry1706 : CheckedRow := ⟨raw1706, clause1706, row1706, checked1706, derived1706⟩

def raw1707 : List String := ["function clause decode64 ((", "0b", "11001110100", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1707", ") = {\n    SEE = ", "1707", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "vector_crypto_sha3_xar_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ")\n}\n"]
def clause1707 : Clause := ⟨[.fixed "11001110100", .any 21], 1707, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩], "vector_crypto_sha3_xar_decode"⟩
theorem checked1707 : check raw1707 clause1707 = true := by rfl
def row1707 : Row := ⟨1707, 4292870144, 3464495104⟩
theorem derived1707 : clause1707.row = row1707 := by rfl
def entry1707 : CheckedRow := ⟨raw1707, clause1707, row1707, checked1707, derived1707⟩

def raw1708 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "10000", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1708", ") = {\n    SEE = ", "1708", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "immhi", " : bits(", "19", ") = ", "op_code[", "23", " .. ", "5", "]", ";\n", "    ", "immlo", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_address_pcrel_decode", "(", "Rd", ", ", "immhi", ", ", "immlo", ", ", "op", ")\n}\n"]
def clause1708 : Clause := ⟨[.fixed "0", .any 2, .fixed "10000", .any 24], 1708, [⟨"Rd", 5, 4, 0, false⟩, ⟨"immhi", 19, 23, 5, false⟩, ⟨"immlo", 2, 30, 29, false⟩, ⟨"op", 1, 31, 31, true⟩], "integer_arithmetic_address_pcrel_decode"⟩
theorem checked1708 : check raw1708 clause1708 = true := by rfl
def row1708 : Row := ⟨1708, 2667577344, 268435456⟩
theorem derived1708 : clause1708.row = row1708 := by rfl
def entry1708 : CheckedRow := ⟨raw1708, clause1708, row1708, checked1708, derived1708⟩

def raw1709 : List String := ["function clause decode64 ((", "0b", "110101101001111100001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1111111111", " as op_code) if SEE < ", "1709", ") = {\n    SEE = ", "1709", ";\n", "    ", "op4", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "branch_unconditional_eret_decode", "(", "op4", ", ", "Rn", ", ", "M", ", ", "A", ", ", "op2", ")\n}\n"]
def clause1709 : Clause := ⟨[.fixed "110101101001111100001", .any 1, .fixed "1111111111"], 1709, [⟨"op4", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"M", 1, 10, 10, true⟩, ⟨"A", 1, 11, 11, true⟩, ⟨"op2", 5, 20, 16, false⟩], "branch_unconditional_eret_decode"⟩
theorem checked1709 : check raw1709 clause1709 = true := by rfl
def row1709 : Row := ⟨1709, 4294966271, 3600747519⟩
theorem derived1709 : clause1709.row = row1709 := by rfl
def entry1709 : CheckedRow := ⟨raw1709, clause1709, row1709, checked1709, derived1709⟩

def raw1710 : List String := ["function clause decode64 ((", "0b", "01001000000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1710", ") = {\n    SEE = ", "1710", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1710 : Clause := ⟨[.fixed "01001000000", .any 5, .fixed "0", .any 15], 1710, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1710 : check raw1710 clause1710 = true := by rfl
def row1710 : Row := ⟨1710, 4292902912, 1207959552⟩
theorem derived1710 : clause1710.row = row1710 := by rfl
def entry1710 : CheckedRow := ⟨raw1710, clause1710, row1710, checked1710, derived1710⟩

def raw1711 : List String := ["function clause decode64 ((", "0b", "01111000101", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1711", ") = {\n    SEE = ", "1711", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_orderedrcpc_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1711 : Clause := ⟨[.fixed "01111000101", .any 5, .fixed "110000", .any 10], 1711, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_orderedrcpc_decode"⟩
theorem checked1711 : check raw1711 clause1711 = true := by rfl
def row1711 : Row := ⟨1711, 4292934656, 2023800832⟩
theorem derived1711 : clause1711.row = row1711 := by rfl
def entry1711 : CheckedRow := ⟨raw1711, clause1711, row1711, checked1711, derived1711⟩

def raw1712 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "010100001", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1712", ") = {\n    SEE = ", "1712", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_general_noalloc_memory_pair_general_noalloc__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1712 : Clause := ⟨[.any 1, .fixed "010100001", .any 22], 1712, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_general_noalloc_memory_pair_general_noalloc__decode"⟩
theorem checked1712 : check raw1712 clause1712 = true := by rfl
def row1712 : Row := ⟨1712, 2143289344, 675282944⟩
theorem derived1712 : clause1712.row = row1712 := by rfl
def entry1712 : CheckedRow := ⟨raw1712, clause1712, row1712, checked1712, derived1712⟩

def raw1713 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100101110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1713", ") = {\n    SEE = ", "1713", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "rmode", " : bits(", "3", ") = ", "op_code[", "17", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_round_frint_decode", "(", "Rd", ", ", "Rn", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1713 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100101110000", .any 10], 1713, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"rmode", 3, 17, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_round_frint_decode"⟩
theorem checked1713 : check raw1713 clause1713 = true := by rfl
def row1713 : Row := ⟨1713, 4282383360, 505790464⟩
theorem derived1713 : clause1713.row = row1713 := by rfl
def entry1713 : CheckedRow := ⟨raw1713, clause1713, row1713, checked1713, derived1713⟩

def entries85 : List CheckedRow := [entry1706, entry1707, entry1708, entry1709, entry1710, entry1711, entry1712, entry1713]
def rows85 : List Row := [row1706, row1707, row1708, row1709, row1710, row1711, row1712, row1713]
theorem indices85 : rows85.map Row.index = [1706, 1707, 1708, 1709, 1710, 1711, 1712, 1713] := by rfl
theorem bound85 : entries85.map CheckedRow.row = rows85 := by rfl
theorem choices_and_85 : choices rows85 167837696#32 (-1) = [] := by rfl
theorem choices_orr_85 : choices rows85 704708608#32 (-1) = [] := by rfl
theorem choices_eor_85 : choices rows85 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_85 : choices rows85 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
