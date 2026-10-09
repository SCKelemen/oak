import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1578 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "00111011111001110110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1578", ") = {\n    SEE = ", "1578", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_special_recip_fp16_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1578 : Clause := ⟨[.fixed "0", .any 1, .fixed "00111011111001110110", .any 10], 1578, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_special_recip_fp16_simd_decode"⟩
theorem checked1578 : check raw1578 clause1578 = true := by rfl
def row1578 : Row := ⟨1578, 3221224448, 251254784⟩
theorem derived1578 : clause1578.row = row1578 := by rfl
def entry1578 : CheckedRow := ⟨raw1578, clause1578, row1578, checked1578, derived1578⟩

def raw1579 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "10100100", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1579", ") = {\n    SEE = ", "1579", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imms", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "immr", " : bits(", "6", ") = ", "op_code[", "21", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_immediate_decode", "(", "Rd", ", ", "Rn", ", ", "imms", ", ", "immr", ", ", "N", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1579 : Clause := ⟨[.any 1, .fixed "10100100", .any 23], 1579, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imms", 6, 15, 10, false⟩, ⟨"immr", 6, 21, 16, false⟩, ⟨"N", 1, 22, 22, true⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_immediate_decode"⟩
theorem checked1579 : check raw1579 clause1579 = true := by rfl
def row1579 : Row := ⟨1579, 2139095040, 1375731712⟩
theorem derived1579 : clause1579.row = row1579 := by rfl
def entry1579 : CheckedRow := ⟨raw1579, clause1579, row1579, checked1579, derived1579⟩

def raw1580 : List String := ["function clause decode64 ((", "0b", "011110001", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1580", ") = {\n    SEE = ", "1580", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1580 : Clause := ⟨[.fixed "011110001", .any 1, .fixed "0", .any 9, .fixed "10", .any 10], 1580, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_unpriv_memory_single_general_immediate_signed_offset_unpriv__decode"⟩
theorem checked1580 : check raw1580 clause1580 = true := by rfl
def row1580 : Row := ⟨1580, 4288678912, 2021656576⟩
theorem derived1580 : clause1580.row = row1580 := by rfl
def entry1580 : CheckedRow := ⟨raw1580, clause1580, row1580, checked1580, derived1580⟩

def raw1581 : List String := ["function clause decode64 ((", "0b", "01011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000100110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1581", ") = {\n    SEE = ", "1581", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_cmp_int_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "size", ", ", "U", ")\n}\n"]
def clause1581 : Clause := ⟨[.fixed "01011110", .any 2, .fixed "100000100110", .any 10], 1581, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_cmp_int_bulk_sisd_decode"⟩
theorem checked1581 : check raw1581 clause1581 = true := by rfl
def row1581 : Row := ⟨1581, 4282383360, 1579194368⟩
theorem derived1581 : clause1581.row = row1581 := by rfl
def entry1581 : CheckedRow := ⟨raw1581, clause1581, row1581, checked1581, derived1581⟩

def raw1582 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "10110011", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1582", ") = {\n    SEE = ", "1582", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_simdfp_postidx_memory_pair_simdfp_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1582 : Clause := ⟨[.any 2, .fixed "10110011", .any 22], 1582, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_simdfp_postidx_memory_pair_simdfp_postidx__decode"⟩
theorem checked1582 : check raw1582 clause1582 = true := by rfl
def row1582 : Row := ⟨1582, 1069547520, 750780416⟩
theorem derived1582 : clause1582.row = row1582 := by rfl
def entry1582 : CheckedRow := ⟨raw1582, clause1582, row1582, checked1582, derived1582⟩

def raw1583 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "011001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1583", ") = {\n    SEE = ", "1583", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_single_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1583 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "011001", .any 10], 1583, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_single_decode"⟩
theorem checked1583 : check raw1583 clause1583 = true := by rfl
def row1583 : Row := ⟨1583, 3206609920, 237003776⟩
theorem derived1583 : clause1583.row = row1583 := by rfl
def entry1583 : CheckedRow := ⟨raw1583, clause1583, row1583, checked1583, derived1583⟩

def raw1584 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1584", ") = {\n    SEE = ", "1584", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1584 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000", .any 2, .fixed "1", .any 5, .fixed "010100", .any 10], 1584, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1584 : check raw1584 clause1584 = true := by rfl
def row1584 : Row := ⟨1584, 3206609920, 3089125376⟩
theorem derived1584 : clause1584.row = row1584 := by rfl
def entry1584 : CheckedRow := ⟨raw1584, clause1584, row1584, checked1584, derived1584⟩

def raw1585 : List String := ["function clause decode64 ((", "0b", "00011001100", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1585", ") = {\n    SEE = ", "1585", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "integer_tags_mcsettagandzerodata_decode", "(", "Rt", ", ", "Xn", ", ", "imm9", ")\n}\n"]
def clause1585 : Clause := ⟨[.fixed "00011001100", .any 9, .fixed "10", .any 10], 1585, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩], "integer_tags_mcsettagandzerodata_decode"⟩
theorem checked1585 : check raw1585 clause1585 = true := by rfl
def row1585 : Row := ⟨1585, 4292873216, 427821056⟩
theorem derived1585 : clause1585.row = row1585 := by rfl
def entry1585 : CheckedRow := ⟨raw1585, clause1585, row1585, checked1585, derived1585⟩

def entries69 : List CheckedRow := [entry1578, entry1579, entry1580, entry1581, entry1582, entry1583, entry1584, entry1585]
def rows69 : List Row := [row1578, row1579, row1580, row1581, row1582, row1583, row1584, row1585]
theorem indices69 : rows69.map Row.index = [1578, 1579, 1580, 1581, 1582, 1583, 1584, 1585] := by rfl
theorem bound69 : entries69.map CheckedRow.row = rows69 := by rfl
theorem choices_and_69 : choices rows69 167837696#32 (-1) = [] := by rfl
theorem choices_orr_69 : choices rows69 704708608#32 (-1) = [] := by rfl
theorem choices_eor_69 : choices rows69 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_69 : choices rows69 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
