import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1938 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1938", ") = {\n    SEE = ", "1938", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op2", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode2_5_2_", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_shift_variable_decode", "(", "Rd", ", ", "Rn", ", ", "op2", ", ", "opcode2_5_2_", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1938 : Clause := ⟨[.any 1, .fixed "0011010110", .any 5, .fixed "001001", .any 10], 1938, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op2", 2, 11, 10, false⟩, ⟨"opcode2_5_2_", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_shift_variable_decode"⟩
theorem checked1938 : check raw1938 clause1938 = true := by rfl
def row1938 : Row := ⟨1938, 2145451008, 448799744⟩
theorem derived1938 : clause1938.row = row1938 := by rfl
def entry1938 : CheckedRow := ⟨raw1938, clause1938, row1938, checked1938, derived1938⟩

def raw1939 : List String := ["function clause decode64 ((", "0b", "01011111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1939", ") = {\n    SEE = ", "1939", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_high_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "op", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1939 : Clause := ⟨[.fixed "01011111", .any 8, .fixed "1101", .any 1, .fixed "0", .any 10], 1939, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mul_high_sisd_decode"⟩
theorem checked1939 : check raw1939 clause1939 = true := by rfl
def row1939 : Row := ⟨1939, 4278252544, 1593888768⟩
theorem derived1939 : clause1939.row = row1939 := by rfl
def entry1939 : CheckedRow := ⟨raw1939, clause1939, row1939, checked1939, derived1939⟩

def raw1940 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100100000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1940", ") = {\n    SEE = ", "1940", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1940 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "100100000000", .any 10], 1940, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1940 : check raw1940 clause1940 = true := by rfl
def row1940 : Row := ⟨1940, 2134899712, 505675776⟩
theorem derived1940 : clause1940.row = row1940 := by rfl
def entry1940 : CheckedRow := ⟨raw1940, clause1940, row1940, checked1940, derived1940⟩

def raw1941 : List String := ["function clause decode64 ((", "0b", "110110101100000100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1941", ") = {\n    SEE = ", "1941", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Z", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_pac_autia_dp_1src_decode", "(", "Rd", ", ", "Rn", ", ", "Z", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1941 : Clause := ⟨[.fixed "110110101100000100", .any 1, .fixed "100", .any 10], 1941, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Z", 1, 13, 13, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_pac_autia_dp_1src_decode"⟩
theorem checked1941 : check raw1941 clause1941 = true := by rfl
def row1941 : Row := ⟨1941, 4294958080, 3670085632⟩
theorem derived1941 : clause1941.row = row1941 := by rfl
def entry1941 : CheckedRow := ⟨raw1941, clause1941, row1941, checked1941, derived1941⟩

def raw1942 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1942", ") = {\n    SEE = ", "1942", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1942 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000", .any 2, .fixed "1", .any 5, .fixed "001000", .any 10], 1942, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1942 : check raw1942 clause1942 = true := by rfl
def row1942 : Row := ⟨1942, 3206609920, 3089113088⟩
theorem derived1942 : clause1942.row = row1942 := by rfl
def entry1942 : CheckedRow := ⟨raw1942, clause1942, row1942, checked1942, derived1942⟩

def entries114 : List CheckedRow := [entry1938, entry1939, entry1940, entry1941, entry1942]
def rows114 : List Row := [row1938, row1939, row1940, row1941, row1942]
theorem indices114 : rows114.map Row.index = [1938, 1939, 1940, 1941, 1942] := by rfl
theorem bound114 : entries114.map CheckedRow.row = rows114 := by rfl
theorem choices_and_114 : choices rows114 167837696#32 (-1) = [] := by rfl
theorem choices_orr_114 : choices rows114 704708608#32 (-1) = [] := by rfl
theorem choices_eor_114 : choices rows114 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_114 : choices rows114 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
