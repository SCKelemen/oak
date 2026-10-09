import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1322 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "101101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1322", ") = {\n    SEE = ", "1322", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1322 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "1", .any 5, .fixed "101101", .any 10], 1322, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode"⟩
theorem checked1322 : check raw1322 clause1322 = true := by rfl
def row1322 : Row := ⟨1322, 4280351744, 2116072448⟩
theorem derived1322 : clause1322.row = row1322 := by rfl
def entry1322 : CheckedRow := ⟨raw1322, clause1322, row1322, checked1322, derived1322⟩

def raw1323 : List String := ["function clause decode64 ((", "0b", "00001000100", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1323", ") = {\n    SEE = ", "1323", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_ordered_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1323 : Clause := ⟨[.fixed "00001000100", .any 5, .fixed "1", .any 15], 1323, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_ordered_decode"⟩
theorem checked1323 : check raw1323 clause1323 = true := by rfl
def row1323 : Row := ⟨1323, 4292902912, 142639104⟩
theorem derived1323 : clause1323.row = row1323 := by rfl
def entry1323 : CheckedRow := ⟨raw1323, clause1323, row1323, checked1323, derived1323⟩

def raw1324 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "101101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1324", ") = {\n    SEE = ", "1324", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1324 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "101101", .any 10], 1324, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_mul_int_doubling_sisd_decode"⟩
theorem checked1324 : check raw1324 clause1324 = true := by rfl
def row1324 : Row := ⟨1324, 4280351744, 1579201536⟩
theorem derived1324 : clause1324.row = row1324 := by rfl
def entry1324 : CheckedRow := ⟨raw1324, clause1324, row1324, checked1324, derived1324⟩

def raw1325 : List String := ["function clause decode64 ((", "0b", "010111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1325", ") = {\n    SEE = ", "1325", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1325 : Clause := ⟨[.fixed "010111101", .any 1, .fixed "100001101110", .any 10], 1325, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode"⟩
theorem checked1325 : check raw1325 clause1325 = true := by rfl
def row1325 : Row := ⟨1325, 4290771968, 1587656704⟩
theorem derived1325 : clause1325.row = row1325 := by rfl
def entry1325 : CheckedRow := ⟨raw1325, clause1325, row1325, checked1325, derived1325⟩

def raw1326 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1326", ") = {\n    SEE = ", "1326", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op2", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode2_5_2_", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_shift_variable_decode", "(", "Rd", ", ", "Rn", ", ", "op2", ", ", "opcode2_5_2_", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1326 : Clause := ⟨[.any 1, .fixed "0011010110", .any 5, .fixed "001000", .any 10], 1326, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op2", 2, 11, 10, false⟩, ⟨"opcode2_5_2_", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_shift_variable_decode"⟩
theorem checked1326 : check raw1326 clause1326 = true := by rfl
def row1326 : Row := ⟨1326, 2145451008, 448798720⟩
theorem derived1326 : clause1326.row = row1326 := by rfl
def entry1326 : CheckedRow := ⟨raw1326, clause1326, row1326, checked1326, derived1326⟩

def raw1327 : List String := ["function clause decode64 ((", "0b", "011110000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1327", ") = {\n    SEE = ", "1327", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_st_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1327 : Clause := ⟨[.fixed "011110000", .any 1, .fixed "1", .any 5, .fixed "010000", .any 5, .fixed "11111"], 1327, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_st_decode"⟩
theorem checked1327 : check raw1327 clause1327 = true := by rfl
def row1327 : Row := ⟨1327, 4288740383, 2015379487⟩
theorem derived1327 : clause1327.row = row1327 := by rfl
def entry1327 : CheckedRow := ⟨raw1327, clause1327, row1327, checked1327, derived1327⟩

def raw1328 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "101001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1328", ") = {\n    SEE = ", "1328", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_leftlong_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1328 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "101001", .any 10], 1328, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_leftlong_decode"⟩
theorem checked1328 : check raw1328 clause1328 = true := by rfl
def row1328 : Row := ⟨1328, 3212901376, 251700224⟩
theorem derived1328 : clause1328.row = row1328 := by rfl
def entry1328 : CheckedRow := ⟨raw1328, clause1328, row1328, checked1328, derived1328⟩

def raw1329 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001011110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1329", ") = {\n    SEE = ", "1329", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_widen_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1329 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011100", .any 1, .fixed "100001011110", .any 10], 1329, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_widen_decode"⟩
theorem checked1329 : check raw1329 clause1329 = true := by rfl
def row1329 : Row := ⟨1329, 3217030144, 237074432⟩
theorem derived1329 : clause1329.row = row1329 := by rfl
def entry1329 : CheckedRow := ⟨raw1329, clause1329, row1329, checked1329, derived1329⟩

def entries37 : List CheckedRow := [entry1322, entry1323, entry1324, entry1325, entry1326, entry1327, entry1328, entry1329]
def rows37 : List Row := [row1322, row1323, row1324, row1325, row1326, row1327, row1328, row1329]
theorem indices37 : rows37.map Row.index = [1322, 1323, 1324, 1325, 1326, 1327, 1328, 1329] := by rfl
theorem bound37 : entries37.map CheckedRow.row = rows37 := by rfl
theorem choices_and_37 : choices rows37 167837696#32 (-1) = [] := by rfl
theorem choices_orr_37 : choices rows37 704708608#32 (-1) = [] := by rfl
theorem choices_eor_37 : choices rows37 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_37 : choices rows37 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
