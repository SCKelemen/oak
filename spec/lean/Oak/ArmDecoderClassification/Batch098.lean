import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1810 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1810", ") = {\n    SEE = ", "1810", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1810 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110010", .any 5, .fixed "001101", .any 10], 1810, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp16_1985_decode"⟩
theorem checked1810 : check raw1810 clause1810 = true := by rfl
def row1810 : Row := ⟨1810, 3219192832, 775959552⟩
theorem derived1810 : clause1810.row = row1810 := by rfl
def entry1810 : CheckedRow := ⟨raw1810, clause1810, row1810, checked1810, derived1810⟩

def raw1811 : List String := ["function clause decode64 ((", "0b", "0001111001111110000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1811", ") = {\n    SEE = ", "1811", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_int_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1811 : Clause := ⟨[.fixed "0001111001111110000000", .any 10], 1811, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_int_decode"⟩
theorem checked1811 : check raw1811 clause1811 = true := by rfl
def row1811 : Row := ⟨1811, 4294966272, 511574016⟩
theorem derived1811 : clause1811.row = row1811 := by rfl
def entry1811 : CheckedRow := ⟨raw1811, clause1811, row1811, checked1811, derived1811⟩

def raw1812 : List String := ["function clause decode64 ((", "0b", "11010100101", " @ ", "_ : bits(", "16", ")", " @ ", "0b", "00011", " as op_code) if SEE < ", "1812", ") = {\n    SEE = ", "1812", ";\n", "    ", "LL", " : bits(", "2", ") = ", "op_code[", "1", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "4", " .. ", "2", "]", ";\n", "    ", "imm16", " : bits(", "16", ") = ", "op_code[", "20", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "23", " .. ", "21", "]", ";\n", "    ", "system_exceptions_debug_exception_decode", "(", "LL", ", ", "op2", ", ", "imm16", ", ", "opc", ")\n}\n"]
def clause1812 : Clause := ⟨[.fixed "11010100101", .any 16, .fixed "00011"], 1812, [⟨"LL", 2, 1, 0, false⟩, ⟨"op2", 3, 4, 2, false⟩, ⟨"imm16", 16, 20, 5, false⟩, ⟨"opc", 3, 23, 21, false⟩], "system_exceptions_debug_exception_decode"⟩
theorem checked1812 : check raw1812 clause1812 = true := by rfl
def row1812 : Row := ⟨1812, 4292870175, 3567255555⟩
theorem derived1812 : clause1812.row = row1812 := by rfl
def entry1812 : CheckedRow := ⟨raw1812, clause1812, row1812, checked1812, derived1812⟩

def raw1813 : List String := ["function clause decode64 ((", "0b", "01011110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1813", ") = {\n    SEE = ", "1813", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_rsqrtsfp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "a", ", ", "U", ")\n}\n"]
def clause1813 : Clause := ⟨[.fixed "01011110110", .any 5, .fixed "001111", .any 10], 1813, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_rsqrtsfp16_sisd_decode"⟩
theorem checked1813 : check raw1813 clause1813 = true := by rfl
def row1813 : Row := ⟨1813, 4292934656, 1589656576⟩
theorem derived1813 : clause1813.row = row1813 := by rfl
def entry1813 : CheckedRow := ⟨raw1813, clause1813, row1813, checked1813, derived1813⟩

def raw1814 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "101101011000000000100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1814", ") = {\n    SEE = ", "1814", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "opcode2", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_cnt_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "opcode2", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1814 : Clause := ⟨[.any 1, .fixed "101101011000000000100", .any 10], 1814, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 10, 10, true⟩, ⟨"opcode2", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_cnt_decode"⟩
theorem checked1814 : check raw1814 clause1814 = true := by rfl
def row1814 : Row := ⟨1814, 2147482624, 1522536448⟩
theorem derived1814 : clause1814.row = row1814 := by rfl
def entry1814 : CheckedRow := ⟨raw1814, clause1814, row1814, checked1814, derived1814⟩

def raw1815 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1815", ") = {\n    SEE = ", "1815", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1815 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000", .any 2, .fixed "1", .any 5, .fixed "011000", .any 10], 1815, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1815 : check raw1815 clause1815 = true := by rfl
def row1815 : Row := ⟨1815, 3206609920, 3089129472⟩
theorem derived1815 : clause1815.row = row1815 := by rfl
def entry1815 : CheckedRow := ⟨raw1815, clause1815, row1815, checked1815, derived1815⟩

def raw1816 : List String := ["function clause decode64 ((", "0b", "1101010100000011001000", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "11111", " as op_code) if SEE < ", "1816", ") = {\n    SEE = ", "1816", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "integer_pac_autib_hint_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1816 : Clause := ⟨[.fixed "1101010100000011001000", .any 1, .fixed "111", .any 1, .fixed "11111"], 1816, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "integer_pac_autib_hint_decode"⟩
theorem checked1816 : check raw1816 clause1816 = true := by rfl
def row1816 : Row := ⟨1816, 4294966751, 3573752287⟩
theorem derived1816 : clause1816.row = row1816 := by rfl
def entry1816 : CheckedRow := ⟨raw1816, clause1816, row1816, checked1816, derived1816⟩

def raw1817 : List String := ["function clause decode64 ((", "0b", "0111111001111001101010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1817", ") = {\n    SEE = ", "1817", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1817 : Clause := ⟨[.fixed "0111111001111001101010", .any 10], 1817, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode"⟩
theorem checked1817 : check raw1817 clause1817 = true := by rfl
def row1817 : Row := ⟨1817, 4294966272, 2121902080⟩
theorem derived1817 : clause1817.row = row1817 := by rfl
def entry1817 : CheckedRow := ⟨raw1817, clause1817, row1817, checked1817, derived1817⟩

def entries98 : List CheckedRow := [entry1810, entry1811, entry1812, entry1813, entry1814, entry1815, entry1816, entry1817]
def rows98 : List Row := [row1810, row1811, row1812, row1813, row1814, row1815, row1816, row1817]
theorem indices98 : rows98.map Row.index = [1810, 1811, 1812, 1813, 1814, 1815, 1816, 1817] := by rfl
theorem bound98 : entries98.map CheckedRow.row = rows98 := by rfl
theorem choices_and_98 : choices rows98 167837696#32 (-1) = [] := by rfl
theorem choices_orr_98 : choices rows98 704708608#32 (-1) = [] := by rfl
theorem choices_eor_98 : choices rows98 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_98 : choices rows98 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
