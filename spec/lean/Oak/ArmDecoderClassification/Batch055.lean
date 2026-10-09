import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1466 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00110100000000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1466", ") = {\n    SEE = ", "1466", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_nowb_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1466 : Clause := ⟨[.fixed "0", .any 1, .fixed "00110100000000", .any 2, .fixed "1", .any 13], 1466, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_nowb_memory_vector_single_nowb__decode"⟩
theorem checked1466 : check raw1466 clause1466 = true := by rfl
def row1466 : Row := ⟨1466, 3221168128, 218112000⟩
theorem derived1466 : clause1466.row = row1466 := by rfl
def entry1466 : CheckedRow := ⟨raw1466, clause1466, row1466, checked1466, derived1466⟩

def raw1467 : List String := ["function clause decode64 ((", "0b", "01011110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1467", ") = {\n    SEE = ", "1467", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha3op_sha1sched0_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ")\n}\n"]
def clause1467 : Clause := ⟨[.fixed "01011110000", .any 5, .fixed "001100", .any 10], 1467, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 14, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha3op_sha1sched0_decode"⟩
theorem checked1467 : check raw1467 clause1467 = true := by rfl
def row1467 : Row := ⟨1467, 4292934656, 1577070592⟩
theorem derived1467 : clause1467.row = row1467 := by rfl
def entry1467 : CheckedRow := ⟨raw1467, clause1467, row1467, checked1467, derived1467⟩

def raw1468 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1468", ") = {\n    SEE = ", "1468", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1468 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "100001101110", .any 10], 1468, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_sisd_decode"⟩
theorem checked1468 : check raw1468 clause1468 = true := by rfl
def row1468 : Row := ⟨1468, 4290771968, 2124527616⟩
theorem derived1468 : clause1468.row = row1468 := by rfl
def entry1468 : CheckedRow := ⟨raw1468, clause1468, row1468, checked1468, derived1468⟩

def raw1469 : List String := ["function clause decode64 ((", "0b", "0101111100", " @ ", "_ : bits(", "6", ")", " @ ", "0b", "0101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1469", ") = {\n    SEE = ", "1469", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1469 : Clause := ⟨[.fixed "0101111100", .any 6, .fixed "0101", .any 1, .fixed "0", .any 10], 1469, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mulacc_fp16_sisd_decode"⟩
theorem checked1469 : check raw1469 clause1469 = true := by rfl
def row1469 : Row := ⟨1469, 4290835456, 1593856000⟩
theorem derived1469 : clause1469.row = row1469 := by rfl
def entry1469 : CheckedRow := ⟨raw1469, clause1469, row1469, checked1469, derived1469⟩

def raw1470 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1470", ") = {\n    SEE = ", "1470", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_permute_unzip_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "size", ", ", "Q", ")\n}\n"]
def clause1470 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "0", .any 5, .fixed "010110", .any 10], 1470, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_permute_unzip_decode"⟩
theorem checked1470 : check raw1470 clause1470 = true := by rfl
def row1470 : Row := ⟨1470, 3206609920, 234903552⟩
theorem derived1470 : clause1470.row = row1470 := by rfl
def entry1470 : CheckedRow := ⟨raw1470, clause1470, row1470, checked1470, derived1470⟩

def raw1471 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111001111001100110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1471", ") = {\n    SEE = ", "1471", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1471 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111001111001100110", .any 10], 1471, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_fp16_round_decode"⟩
theorem checked1471 : check raw1471 clause1471 = true := by rfl
def row1471 : Row := ⟨1471, 3221224448, 242849792⟩
theorem derived1471 : clause1471.row = row1471 := by rfl
def entry1471 : CheckedRow := ⟨raw1471, clause1471, row1471, checked1471, derived1471⟩

def raw1472 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101111", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1110", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1472", ") = {\n    SEE = ", "1472", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1472 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101111", .any 5, .fixed "1110", .any 12], 1472, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1472 : check raw1472 clause1472 = true := by rfl
def row1472 : Row := ⟨1472, 3219189760, 232841216⟩
theorem derived1472 : clause1472.row = row1472 := by rfl
def entry1472 : CheckedRow := ⟨raw1472, clause1472, row1472, checked1472, derived1472⟩

def raw1473 : List String := ["function clause decode64 ((", "0b", "10011011110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1473", ") = {\n    SEE = ", "1473", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Ra", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "op54", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_mul_widening_64128hi_decode", "(", "Rd", ", ", "Rn", ", ", "Ra", ", ", "o0", ", ", "Rm", ", ", "U", ", ", "op54", ", ", "sf", ")\n}\n"]
def clause1473 : Clause := ⟨[.fixed "10011011110", .any 5, .fixed "0", .any 15], 1473, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Ra", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"U", 1, 23, 23, true⟩, ⟨"op54", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_mul_widening_64128hi_decode"⟩
theorem checked1473 : check raw1473 clause1473 = true := by rfl
def row1473 : Row := ⟨1473, 4292902912, 2613051392⟩
theorem derived1473 : clause1473.row = row1473 := by rfl
def entry1473 : CheckedRow := ⟨raw1473, clause1473, row1473, checked1473, derived1473⟩

def entries55 : List CheckedRow := [entry1466, entry1467, entry1468, entry1469, entry1470, entry1471, entry1472, entry1473]
def rows55 : List Row := [row1466, row1467, row1468, row1469, row1470, row1471, row1472, row1473]
theorem indices55 : rows55.map Row.index = [1466, 1467, 1468, 1469, 1470, 1471, 1472, 1473] := by rfl
theorem bound55 : entries55.map CheckedRow.row = rows55 := by rfl
theorem choices_and_55 : choices rows55 167837696#32 (-1) = [] := by rfl
theorem choices_orr_55 : choices rows55 704708608#32 (-1) = [] := by rfl
theorem choices_eor_55 : choices rows55 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_55 : choices rows55 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
