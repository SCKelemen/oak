import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1042 : List String := ["function clause decode64 ((", "0b", "01001000110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1042", ") = {\n    SEE = ", "1042", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_ordered_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1042 : Clause := ⟨[.fixed "01001000110", .any 5, .fixed "0", .any 15], 1042, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_ordered_decode"⟩
theorem checked1042 : check raw1042 clause1042 = true := by rfl
def row1042 : Row := ⟨1042, 4292902912, 1220542464⟩
theorem derived1042 : clause1042.row = row1042 := by rfl
def entry1042 : CheckedRow := ⟨raw1042, clause1042, row1042, checked1042, derived1042⟩

def raw1043 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1043", ") = {\n    SEE = ", "1043", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ")\n}\n"]
def clause1043 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "100000100010", .any 10], 1043, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_int_bulk_sisd_decode"⟩
theorem checked1043 : check raw1043 clause1043 = true := by rfl
def row1043 : Row := ⟨1043, 4282383360, 2116061184⟩
theorem derived1043 : clause1043.row = row1043 := by rfl
def entry1043 : CheckedRow := ⟨raw1043, clause1043, row1043, checked1043, derived1043⟩

def raw1044 : List String := ["function clause decode64 ((", "0b", "11010101000000110010001000011111", " as op_code) if SEE < ", "1044", ") = {\n    SEE = ", "1044", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_hints_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1044 : Clause := ⟨[.fixed "11010101000000110010001000011111"], 1044, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_hints_decode"⟩
theorem checked1044 : check raw1044 clause1044 = true := by rfl
def row1044 : Row := ⟨1044, 4294967295, 3573752351⟩
theorem derived1044 : clause1044.row = row1044 := by rfl
def entry1044 : CheckedRow := ⟨raw1044, clause1044, row1044, checked1044, derived1044⟩

def raw1045 : List String := ["function clause decode64 ((", "0b", "01111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1045", ") = {\n    SEE = ", "1045", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1045 : Clause := ⟨[.fixed "01111000", .any 2, .fixed "1", .any 5, .fixed "010000", .any 10], 1045, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1045 : check raw1045 clause1045 = true := by rfl
def row1045 : Row := ⟨1045, 4280351744, 2015379456⟩
theorem derived1045 : clause1045.row = row1045 := by rfl
def entry1045 : CheckedRow := ⟨raw1045, clause1045, row1045, checked1045, derived1045⟩

def raw1046 : List String := ["function clause decode64 ((", "0b", "11010101000000110011", " @ ", "_ : bits(", "4", ")", " @ ", "0b", "11011111", " as op_code) if SEE < ", "1046", ") = {\n    SEE = ", "1046", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "6", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_barriers_decode", "(", "Rt", ", ", "opc", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1046 : Clause := ⟨[.fixed "11010101000000110011", .any 4, .fixed "11011111"], 1046, [⟨"Rt", 5, 4, 0, false⟩, ⟨"opc", 2, 6, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_barriers_decode"⟩
theorem checked1046 : check raw1046 clause1046 = true := by rfl
def row1046 : Row := ⟨1046, 4294963455, 3573756127⟩
theorem derived1046 : clause1046.row = row1046 := by rfl
def entry1046 : CheckedRow := ⟨raw1046, clause1046, row1046, checked1046, derived1046⟩

def raw1047 : List String := ["function clause decode64 ((", "0b", "01111110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1047", ") = {\n    SEE = ", "1047", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "E", ", ", "U", ")\n}\n"]
def clause1047 : Clause := ⟨[.fixed "01111110110", .any 5, .fixed "001011", .any 10], 1047, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode"⟩
theorem checked1047 : check raw1047 clause1047 = true := by rfl
def row1047 : Row := ⟨1047, 4292934656, 2126523392⟩
theorem derived1047 : clause1047.row = row1047 := by rfl
def entry1047 : CheckedRow := ⟨raw1047, clause1047, row1047, checked1047, derived1047⟩

def raw1048 : List String := ["function clause decode64 ((", "0b", "00111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1048", ") = {\n    SEE = ", "1048", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1048 : Clause := ⟨[.fixed "00111000", .any 2, .fixed "1", .any 5, .fixed "011100", .any 10], 1048, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1048 : check raw1048 clause1048 = true := by rfl
def row1048 : Row := ⟨1048, 4280351744, 941649920⟩
theorem derived1048 : clause1048.row = row1048 := by rfl
def entry1048 : CheckedRow := ⟨raw1048, clause1048, row1048, checked1048, derived1048⟩

def raw1049 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1049", ") = {\n    SEE = ", "1049", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_saturating_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1049 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "000011", .any 10], 1049, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_add_saturating_sisd_decode"⟩
theorem checked1049 : check raw1049 clause1049 = true := by rfl
def row1049 : Row := ⟨1049, 4280351744, 1579158528⟩
theorem derived1049 : clause1049.row = row1049 := by rfl
def entry1049 : CheckedRow := ⟨raw1049, clause1049, row1049, checked1049, derived1049⟩

def entries2 : List CheckedRow := [entry1042, entry1043, entry1044, entry1045, entry1046, entry1047, entry1048, entry1049]
def rows2 : List Row := [row1042, row1043, row1044, row1045, row1046, row1047, row1048, row1049]
theorem indices2 : rows2.map Row.index = [1042, 1043, 1044, 1045, 1046, 1047, 1048, 1049] := by rfl
theorem bound2 : entries2.map CheckedRow.row = rows2 := by rfl
theorem choices_and_2 : choices rows2 167837696#32 (-1) = [] := by rfl
theorem choices_orr_2 : choices rows2 704708608#32 (-1) = [] := by rfl
theorem choices_eor_2 : choices rows2 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_2 : choices rows2 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
