import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1602 : List String := ["function clause decode64 ((", "0b", "01011110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1602", ") = {\n    SEE = ", "1602", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha3op_sha1hash_parity_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ")\n}\n"]
def clause1602 : Clause := ⟨[.fixed "01011110000", .any 5, .fixed "000100", .any 10], 1602, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 14, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha3op_sha1hash_parity_decode"⟩
theorem checked1602 : check raw1602 clause1602 = true := by rfl
def row1602 : Row := ⟨1602, 4292934656, 1577062400⟩
theorem derived1602 : clause1602.row = row1602 := by rfl
def entry1602 : CheckedRow := ⟨raw1602, clause1602, row1602, checked1602, derived1602⟩

def raw1603 : List String := ["function clause decode64 ((", "0b", "0101111000101000001010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1603", ") = {\n    SEE = ", "1603", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "vector_crypto_sha2op_sha256sched0_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ")\n}\n"]
def clause1603 : Clause := ⟨[.fixed "0101111000101000001010", .any 10], 1603, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩], "vector_crypto_sha2op_sha256sched0_decode"⟩
theorem checked1603 : check raw1603 clause1603 = true := by rfl
def row1603 : Row := ⟨1603, 4294966272, 1579689984⟩
theorem derived1603 : clause1603.row = row1603 := by rfl
def entry1603 : CheckedRow := ⟨raw1603, clause1603, row1603, checked1603, derived1603⟩

def raw1604 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1111", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1604", ") = {\n    SEE = ", "1604", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_high_simd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "S", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1604 : Clause := ⟨[.fixed "0", .any 1, .fixed "101111", .any 8, .fixed "1111", .any 1, .fixed "0", .any 10], 1604, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"S", 1, 13, 13, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_element_mulacc_high_simd_decode"⟩
theorem checked1604 : check raw1604 clause1604 = true := by rfl
def row1604 : Row := ⟨1604, 3204510720, 788590592⟩
theorem derived1604 : clause1604.row = row1604 := by rfl
def entry1604 : CheckedRow := ⟨raw1604, clause1604, row1604, checked1604, derived1604⟩

def raw1605 : List String := ["function clause decode64 ((", "0b", "1101010100000010001000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1605", ") = {\n    SEE = ", "1605", ";\n", "    ", "Xt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "integer_tags_mcsettagarray_decode", "(", "Xt", ", ", "Xn", ")\n}\n"]
def clause1605 : Clause := ⟨[.fixed "1101010100000010001000", .any 10], 1605, [⟨"Xt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩], "integer_tags_mcsettagarray_decode"⟩
theorem checked1605 : check raw1605 clause1605 = true := by rfl
def row1605 : Row := ⟨1605, 4294966272, 3573686272⟩
theorem derived1605 : clause1605.row = row1605 := by rfl
def entry1605 : CheckedRow := ⟨raw1605, clause1605, row1605, checked1605, derived1605⟩

def raw1606 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1606", ") = {\n    SEE = ", "1606", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_lessthan_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1606 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "100000101010", .any 10], 1606, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_int_lessthan_sisd_decode"⟩
theorem checked1606 : check raw1606 clause1606 = true := by rfl
def row1606 : Row := ⟨1606, 4282383360, 1579198464⟩
theorem derived1606 : clause1606.row = row1606 := by rfl
def entry1606 : CheckedRow := ⟨raw1606, clause1606, row1606, checked1606, derived1606⟩

def raw1607 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "100001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1607", ") = {\n    SEE = ", "1607", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1607 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "100001", .any 10], 1607, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_add_wrapping_single_sisd_decode"⟩
theorem checked1607 : check raw1607 clause1607 = true := by rfl
def row1607 : Row := ⟨1607, 4280351744, 1579189248⟩
theorem derived1607 : clause1607.row = row1607 := by rfl
def entry1607 : CheckedRow := ⟨raw1607, clause1607, row1607, checked1607, derived1607⟩

def raw1608 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100010000000000", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1608", ") = {\n    SEE = ", "1608", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1608 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100010000000000", .any 12], 1608, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode"⟩
theorem checked1608 : check raw1608 clause1608 = true := by rfl
def row1608 : Row := ⟨1608, 3221221376, 205520896⟩
theorem derived1608 : clause1608.row = row1608 := by rfl
def entry1608 : CheckedRow := ⟨raw1608, clause1608, row1608, checked1608, derived1608⟩

def raw1609 : List String := ["function clause decode64 ((", "0b", "010111110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "111111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1609", ") = {\n    SEE = ", "1609", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_shift_conv_float_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "immb", ", ", "immh", ", ", "U", ")\n}\n"]
def clause1609 : Clause := ⟨[.fixed "010111110", .any 7, .fixed "111111", .any 10], 1609, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_shift_conv_float_sisd_decode"⟩
theorem checked1609 : check raw1609 clause1609 = true := by rfl
def row1609 : Row := ⟨1609, 4286643200, 1593900032⟩
theorem derived1609 : clause1609.row = row1609 := by rfl
def entry1609 : CheckedRow := ⟨raw1609, clause1609, row1609, checked1609, derived1609⟩

def entries72 : List CheckedRow := [entry1602, entry1603, entry1604, entry1605, entry1606, entry1607, entry1608, entry1609]
def rows72 : List Row := [row1602, row1603, row1604, row1605, row1606, row1607, row1608, row1609]
theorem indices72 : rows72.map Row.index = [1602, 1603, 1604, 1605, 1606, 1607, 1608, 1609] := by rfl
theorem bound72 : entries72.map CheckedRow.row = rows72 := by rfl
theorem choices_and_72 : choices rows72 167837696#32 (-1) = [] := by rfl
theorem choices_orr_72 : choices rows72 704708608#32 (-1) = [] := by rfl
theorem choices_eor_72 : choices rows72 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_72 : choices rows72 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
