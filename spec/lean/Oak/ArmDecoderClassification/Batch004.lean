import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1058 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "101111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1058", ") = {\n    SEE = ", "1058", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_wrapping_pair_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1058 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "101111", .any 10], 1058, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_wrapping_pair_decode"⟩
theorem checked1058 : check raw1058 clause1058 = true := by rfl
def row1058 : Row := ⟨1058, 3206609920, 237026304⟩
theorem derived1058 : clause1058.row = row1058 := by rfl
def entry1058 : CheckedRow := ⟨raw1058, clause1058, row1058, checked1058, derived1058⟩

def raw1059 : List String := ["function clause decode64 ((", "0b", "10011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1059", ") = {\n    SEE = ", "1059", ";\n", "    ", "Xd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Xm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "integer_tags_mcinserttagmask_decode", "(", "Xd", ", ", "Xn", ", ", "Xm", ")\n}\n"]
def clause1059 : Clause := ⟨[.fixed "10011010110", .any 5, .fixed "000101", .any 10], 1059, [⟨"Xd", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"Xm", 5, 20, 16, false⟩], "integer_tags_mcinserttagmask_decode"⟩
theorem checked1059 : check raw1059 clause1059 = true := by rfl
def row1059 : Row := ⟨1059, 4292934656, 2596279296⟩
theorem derived1059 : clause1059.row = row1059 := by rfl
def entry1059 : CheckedRow := ⟨raw1059, clause1059, row1059, checked1059, derived1059⟩

def raw1060 : List String := ["function clause decode64 ((", "0b", "11010101000000110010000001011111", " as op_code) if SEE < ", "1060", ") = {\n    SEE = ", "1060", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_hints_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1060 : Clause := ⟨[.fixed "11010101000000110010000001011111"], 1060, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_hints_decode"⟩
theorem checked1060 : check raw1060 clause1060 = true := by rfl
def row1060 : Row := ⟨1060, 4294967295, 3573751903⟩
theorem derived1060 : clause1060.row = row1060 := by rfl
def entry1060 : CheckedRow := ⟨raw1060, clause1060, row1060, checked1060, derived1060⟩

def raw1061 : List String := ["function clause decode64 ((", "0b", "0110100101", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1061", ") = {\n    SEE = ", "1061", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_general_offset_memory_pair_general_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1061 : Clause := ⟨[.fixed "0110100101", .any 22], 1061, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_general_offset_memory_pair_general_postidx__decode"⟩
theorem checked1061 : check raw1061 clause1061 = true := by rfl
def row1061 : Row := ⟨1061, 4290772992, 1765801984⟩
theorem derived1061 : clause1061.row = row1061 := by rfl
def entry1061 : CheckedRow := ⟨raw1061, clause1061, row1061, checked1061, derived1061⟩

def raw1062 : List String := ["function clause decode64 ((", "0b", "00001000110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1062", ") = {\n    SEE = ", "1062", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_ordered_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1062 : Clause := ⟨[.fixed "00001000110", .any 5, .fixed "1", .any 15], 1062, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_ordered_decode"⟩
theorem checked1062 : check raw1062 clause1062 = true := by rfl
def row1062 : Row := ⟨1062, 4292902912, 146833408⟩
theorem derived1062 : clause1062.row = row1062 := by rfl
def entry1062 : CheckedRow := ⟨raw1062, clause1062, row1062, checked1062, derived1062⟩

def raw1063 : List String := ["function clause decode64 ((", "0b", "0101111010110000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1063", ") = {\n    SEE = ", "1063", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fp16maxnm_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ")\n}\n"]
def clause1063 : Clause := ⟨[.fixed "0101111010110000110010", .any 10], 1063, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fp16maxnm_sisd_decode"⟩
theorem checked1063 : check raw1063 clause1063 = true := by rfl
def row1063 : Row := ⟨1063, 4294966272, 1588643840⟩
theorem derived1063 : clause1063.row = row1063 := by rfl
def entry1063 : CheckedRow := ⟨raw1063, clause1063, row1063, checked1063, derived1063⟩

def raw1064 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1064", ") = {\n    SEE = ", "1064", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm4", " : bits(", "4", ") = ", "op_code[", "14", " .. ", "11", "]", ";\n", "    ", "imm5", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_integer_dup_decode", "(", "Rd", ", ", "Rn", ", ", "imm4", ", ", "imm5", ", ", "op", ", ", "Q", ")\n}\n"]
def clause1064 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110000", .any 5, .fixed "000011", .any 10], 1064, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm4", 4, 14, 11, false⟩, ⟨"imm5", 5, 20, 16, false⟩, ⟨"op", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_integer_dup_decode"⟩
theorem checked1064 : check raw1064 clause1064 = true := by rfl
def row1064 : Row := ⟨1064, 3219192832, 234884096⟩
theorem derived1064 : clause1064.row = row1064 := by rfl
def entry1064 : CheckedRow := ⟨raw1064, clause1064, row1064, checked1064, derived1064⟩

def raw1065 : List String := ["function clause decode64 ((", "0b", "001110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1065", ") = {\n    SEE = ", "1065", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1065 : Clause := ⟨[.fixed "001110000", .any 1, .fixed "1", .any 5, .fixed "011000", .any 5, .fixed "11111"], 1065, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1065 : check raw1065 clause1065 = true := by rfl
def row1065 : Row := ⟨1065, 4288740383, 941645855⟩
theorem derived1065 : clause1065.row = row1065 := by rfl
def entry1065 : CheckedRow := ⟨raw1065, clause1065, row1065, checked1065, derived1065⟩

def entries4 : List CheckedRow := [entry1058, entry1059, entry1060, entry1061, entry1062, entry1063, entry1064, entry1065]
def rows4 : List Row := [row1058, row1059, row1060, row1061, row1062, row1063, row1064, row1065]
theorem indices4 : rows4.map Row.index = [1058, 1059, 1060, 1061, 1062, 1063, 1064, 1065] := by rfl
theorem bound4 : entries4.map CheckedRow.row = rows4 := by rfl
theorem choices_and_4 : choices rows4 167837696#32 (-1) = [] := by rfl
theorem choices_orr_4 : choices rows4 704708608#32 (-1) = [] := by rfl
theorem choices_eor_4 : choices rows4 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_4 : choices rows4 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
