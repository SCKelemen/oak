import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1786 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100000000001000", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1786", ") = {\n    SEE = ", "1786", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1786 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100000000001000", .any 12], 1786, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode"⟩
theorem checked1786 : check raw1786 clause1786 = true := by rfl
def row1786 : Row := ⟨1786, 3221221376, 201359360⟩
theorem derived1786 : clause1786.row = row1786 := by rfl
def entry1786 : CheckedRow := ⟨raw1786, clause1786, row1786, checked1786, derived1786⟩

def raw1787 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1787", ") = {\n    SEE = ", "1787", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_simd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1787 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "010011", .any 10], 1787, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_shift_simd_decode"⟩
theorem checked1787 : check raw1787 clause1787 = true := by rfl
def row1787 : Row := ⟨1787, 3206609920, 236997632⟩
theorem derived1787 : clause1787.row = row1787 := by rfl
def entry1787 : CheckedRow := ⟨raw1787, clause1787, row1787, checked1787, derived1787⟩

def raw1788 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1001010", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1788", ") = {\n    SEE = ", "1788", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "N", ", ", "shift", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1788 : Clause := ⟨[.any 1, .fixed "1001010", .any 2, .fixed "0", .any 21], 1788, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"N", 1, 21, 21, true⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_shiftedreg_decode"⟩
theorem checked1788 : check raw1788 clause1788 = true := by rfl
def row1788 : Row := ⟨1788, 2132803584, 1241513984⟩
theorem derived1788 : clause1788.row = row1788 := by rfl
def entry1788 : CheckedRow := ⟨raw1788, clause1788, row1788, checked1788, derived1788⟩

def raw1789 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1789", ") = {\n    SEE = ", "1789", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_bulk_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1789 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "100001101110", .any 10], 1789, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_conv_float_bulk_simd_decode"⟩
theorem checked1789 : check raw1789 clause1789 = true := by rfl
def row1789 : Row := ⟨1789, 3217030144, 245479424⟩
theorem derived1789 : clause1789.row = row1789 := by rfl
def entry1789 : CheckedRow := ⟨raw1789, clause1789, row1789, checked1789, derived1789⟩

def raw1790 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001000110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1790", ") = {\n    SEE = ", "1790", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_ordered_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1790 : Clause := ⟨[.fixed "1", .any 1, .fixed "001000110", .any 5, .fixed "1", .any 15], 1790, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_ordered_decode"⟩
theorem checked1790 : check raw1790 clause1790 = true := by rfl
def row1790 : Row := ⟨1790, 3219161088, 2294317056⟩
theorem derived1790 : clause1790.row = row1790 := by rfl
def entry1790 : CheckedRow := ⟨raw1790, clause1790, row1790, checked1790, derived1790⟩

def raw1791 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110000", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1791", ") = {\n    SEE = ", "1791", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "len", " : bits(", "2", ") = ", "op_code[", "14", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "op2", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_table_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "len", ", ", "Rm", ", ", "op2", ", ", "Q", ")\n}\n"]
def clause1791 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110000", .any 5, .fixed "0", .any 2, .fixed "100", .any 10], 1791, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"len", 2, 14, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"op2", 2, 23, 22, false⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_table_decode"⟩
theorem checked1791 : check raw1791 clause1791 = true := by rfl
def row1791 : Row := ⟨1791, 3219168256, 234885120⟩
theorem derived1791 : clause1791.row = row1791 := by rfl
def entry1791 : CheckedRow := ⟨raw1791, clause1791, row1791, checked1791, derived1791⟩

def raw1792 : List String := ["function clause decode64 ((", "0b", "10111010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1792", ") = {\n    SEE = ", "1792", ";\n", "    ", "Xd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Xm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags_decode", "(", "Xd", ", ", "Xn", ", ", "Xm", ")\n}\n"]
def clause1792 : Clause := ⟨[.fixed "10111010110", .any 5, .fixed "000000", .any 10], 1792, [⟨"Xd", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"Xm", 5, 20, 16, false⟩], "integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags_decode"⟩
theorem checked1792 : check raw1792 clause1792 = true := by rfl
def row1792 : Row := ⟨1792, 4292934656, 3133145088⟩
theorem derived1792 : clause1792.row = row1792 := by rfl
def entry1792 : CheckedRow := ⟨raw1792, clause1792, row1792, checked1792, derived1792⟩

def raw1793 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1793", ") = {\n    SEE = ", "1793", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_saturating_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1793 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "1", .any 5, .fixed "001011", .any 10], 1793, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_sub_saturating_sisd_decode"⟩
theorem checked1793 : check raw1793 clause1793 = true := by rfl
def row1793 : Row := ⟨1793, 4280351744, 1579166720⟩
theorem derived1793 : clause1793.row = row1793 := by rfl
def entry1793 : CheckedRow := ⟨raw1793, clause1793, row1793, checked1793, derived1793⟩

def entries95 : List CheckedRow := [entry1786, entry1787, entry1788, entry1789, entry1790, entry1791, entry1792, entry1793]
def rows95 : List Row := [row1786, row1787, row1788, row1789, row1790, row1791, row1792, row1793]
theorem indices95 : rows95.map Row.index = [1786, 1787, 1788, 1789, 1790, 1791, 1792, 1793] := by rfl
theorem bound95 : entries95.map CheckedRow.row = rows95 := by rfl
theorem choices_and_95 : choices rows95 167837696#32 (-1) = [] := by rfl
theorem choices_orr_95 : choices rows95 704708608#32 (-1) = [] := by rfl
theorem choices_eor_95 : choices rows95 1241579520#32 (-1) = [1788] := by rfl
theorem choices_ret_95 : choices rows95 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
