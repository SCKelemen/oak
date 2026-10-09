import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1330 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "011100", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1330", ") = {\n    SEE = ", "1330", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm19", " : bits(", "19", ") = ", "op_code[", "23", " .. ", "5", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_literal_simdfp_decode", "(", "Rt", ", ", "imm19", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1330 : Clause := ⟨[.any 2, .fixed "011100", .any 24], 1330, [⟨"Rt", 5, 4, 0, false⟩, ⟨"imm19", 19, 23, 5, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_literal_simdfp_decode"⟩
theorem checked1330 : check raw1330 clause1330 = true := by rfl
def row1330 : Row := ⟨1330, 1056964608, 469762048⟩
theorem derived1330 : clause1330.row = row1330 := by rfl
def entry1330 : CheckedRow := ⟨raw1330, clause1330, row1330, checked1330, derived1330⟩

def raw1331 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "10111011111000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1331", ") = {\n    SEE = ", "1331", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_fp16_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1331 : Clause := ⟨[.fixed "0", .any 1, .fixed "10111011111000111110", .any 10], 1331, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_diffneg_fp16_decode"⟩
theorem checked1331 : check raw1331 clause1331 = true := by rfl
def row1331 : Row := ⟨1331, 3221224448, 788068352⟩
theorem derived1331 : clause1331.row = row1331 := by rfl
def entry1331 : CheckedRow := ⟨raw1331, clause1331, row1331, checked1331, derived1331⟩

def raw1332 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1332", ") = {\n    SEE = ", "1332", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1332 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100000100010", .any 10], 1332, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_cmp_int_bulk_simd_decode"⟩
theorem checked1332 : check raw1332 clause1332 = true := by rfl
def row1332 : Row := ⟨1332, 3208641536, 773883904⟩
theorem derived1332 : clause1332.row = row1332 := by rfl
def entry1332 : CheckedRow := ⟨raw1332, clause1332, row1332, checked1332, derived1332⟩

def raw1333 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1333", ") = {\n    SEE = ", "1333", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_double_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1333 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "110100", .any 10], 1333, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_disparate_mul_double_sisd_decode"⟩
theorem checked1333 : check raw1333 clause1333 = true := by rfl
def row1333 : Row := ⟨1333, 4280351744, 1579208704⟩
theorem derived1333 : clause1333.row = row1333 := by rfl
def entry1333 : CheckedRow := ⟨raw1333, clause1333, row1333, checked1333, derived1333⟩

def raw1334 : List String := ["function clause decode64 ((", "0b", "001110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1334", ") = {\n    SEE = ", "1334", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1334 : Clause := ⟨[.fixed "001110000", .any 1, .fixed "1", .any 5, .fixed "010100", .any 5, .fixed "11111"], 1334, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1334 : check raw1334 clause1334 = true := by rfl
def row1334 : Row := ⟨1334, 4288740383, 941641759⟩
theorem derived1334 : clause1334.row = row1334 := by rfl
def entry1334 : CheckedRow := ⟨raw1334, clause1334, row1334, checked1334, derived1334⟩

def raw1335 : List String := ["function clause decode64 ((", "0b", "011111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110000111110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1335", ") = {\n    SEE = ", "1335", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fpmax_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ")\n}\n"]
def clause1335 : Clause := ⟨[.fixed "011111100", .any 1, .fixed "110000111110", .any 10], 1335, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fpmax_sisd_decode"⟩
theorem checked1335 : check raw1335 clause1335 = true := by rfl
def row1335 : Row := ⟨1335, 4290771968, 2117138432⟩
theorem derived1335 : clause1335.row = row1335 := by rfl
def entry1335 : CheckedRow := ⟨raw1335, clause1335, row1335, checked1335, derived1335⟩

def raw1336 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1336", ") = {\n    SEE = ", "1336", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_fp16_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1336 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110010", .any 5, .fixed "000101", .any 10], 1336, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_fp16_decode"⟩
theorem checked1336 : check raw1336 clause1336 = true := by rfl
def row1336 : Row := ⟨1336, 3219192832, 775951360⟩
theorem derived1336 : clause1336.row = row1336 := by rfl
def entry1336 : CheckedRow := ⟨raw1336, clause1336, row1336, checked1336, derived1336⟩

def raw1337 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100100010000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1337", ") = {\n    SEE = ", "1337", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "rmode", " : bits(", "3", ") = ", "op_code[", "17", " .. ", "15", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_arithmetic_round_frint_decode", "(", "Rd", ", ", "Rn", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1337 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "100100010000", .any 10], 1337, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"rmode", 3, 17, 15, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_arithmetic_round_frint_decode"⟩
theorem checked1337 : check raw1337 clause1337 = true := by rfl
def row1337 : Row := ⟨1337, 4282383360, 505692160⟩
theorem derived1337 : clause1337.row = row1337 := by rfl
def entry1337 : CheckedRow := ⟨raw1337, clause1337, row1337, checked1337, derived1337⟩

def entries38 : List CheckedRow := [entry1330, entry1331, entry1332, entry1333, entry1334, entry1335, entry1336, entry1337]
def rows38 : List Row := [row1330, row1331, row1332, row1333, row1334, row1335, row1336, row1337]
theorem indices38 : rows38.map Row.index = [1330, 1331, 1332, 1333, 1334, 1335, 1336, 1337] := by rfl
theorem bound38 : entries38.map CheckedRow.row = rows38 := by rfl
theorem choices_and_38 : choices rows38 167837696#32 (-1) = [] := by rfl
theorem choices_orr_38 : choices rows38 704708608#32 (-1) = [] := by rfl
theorem choices_eor_38 : choices rows38 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_38 : choices rows38 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
