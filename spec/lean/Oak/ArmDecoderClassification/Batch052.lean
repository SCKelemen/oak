import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1442 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "010100110", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1442", ") = {\n    SEE = ", "1442", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_general_preidx_memory_pair_general_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1442 : Clause := ⟨[.any 1, .fixed "010100110", .any 22], 1442, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_general_preidx_memory_pair_general_postidx__decode"⟩
theorem checked1442 : check raw1442 clause1442 = true := by rfl
def row1442 : Row := ⟨1442, 2143289344, 696254464⟩
theorem derived1442 : clause1442.row = row1442 := by rfl
def entry1442 : CheckedRow := ⟨raw1442, clause1442, row1442, checked1442, derived1442⟩

def raw1443 : List String := ["function clause decode64 ((", "0b", "011111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1443", ") = {\n    SEE = ", "1443", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_reduce_fpmaxnm_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ")\n}\n"]
def clause1443 : Clause := ⟨[.fixed "011111100", .any 1, .fixed "110000110010", .any 10], 1443, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_reduce_fpmaxnm_sisd_decode"⟩
theorem checked1443 : check raw1443 clause1443 = true := by rfl
def row1443 : Row := ⟨1443, 4290771968, 2117126144⟩
theorem derived1443 : clause1443.row = row1443 := by rfl
def entry1443 : CheckedRow := ⟨raw1443, clause1443, row1443, checked1443, derived1443⟩

def raw1444 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001100010000000100", " @ ", "_ : bits(", "12", ")", " as op_code) if SEE < ", "1444", ") = {\n    SEE = ", "1444", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "opcode", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1444 : Clause := ⟨[.fixed "0", .any 1, .fixed "001100010000000100", .any 12], 1444, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"opcode", 4, 15, 12, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_multiple_nowb_memory_vector_multiple_nowb__decode"⟩
theorem checked1444 : check raw1444 clause1444 = true := by rfl
def row1444 : Row := ⟨1444, 3221221376, 205537280⟩
theorem derived1444 : clause1444.row = row1444 := by rfl
def entry1444 : CheckedRow := ⟨raw1444, clause1444, row1444, checked1444, derived1444⟩

def raw1445 : List String := ["function clause decode64 ((", "0b", "01011001010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1445", ") = {\n    SEE = ", "1445", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1445 : Clause := ⟨[.fixed "01011001010", .any 9, .fixed "00", .any 10], 1445, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1445 : check raw1445 clause1445 = true := by rfl
def row1445 : Row := ⟨1445, 4292873216, 1497366528⟩
theorem derived1445 : clause1445.row = row1445 := by rfl
def entry1445 : CheckedRow := ⟨raw1445, clause1445, row1445, checked1445, derived1445⟩

def raw1446 : List String := ["function clause decode64 ((", "0b", "11010101000000110010000010011111", " as op_code) if SEE < ", "1446", ") = {\n    SEE = ", "1446", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_hints_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1446 : Clause := ⟨[.fixed "11010101000000110010000010011111"], 1446, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_hints_decode"⟩
theorem checked1446 : check raw1446 clause1446 = true := by rfl
def row1446 : Row := ⟨1446, 4294967295, 3573751967⟩
theorem derived1446 : clause1446.row = row1446 := by rfl
def entry1446 : CheckedRow := ⟨raw1446, clause1446, row1446, checked1446, derived1446⟩

def raw1447 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011010110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1447", ") = {\n    SEE = ", "1447", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "10", "]]", ";\n", "    ", "opcode2_5_1_", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_div_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "opcode2_5_1_", ", ", "Rm", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1447 : Clause := ⟨[.any 1, .fixed "0011010110", .any 5, .fixed "000011", .any 10], 1447, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 10, 10, true⟩, ⟨"opcode2_5_1_", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_div_decode"⟩
theorem checked1447 : check raw1447 clause1447 = true := by rfl
def row1447 : Row := ⟨1447, 2145451008, 448793600⟩
theorem derived1447 : clause1447.row = row1447 := by rfl
def entry1447 : CheckedRow := ⟨raw1447, clause1447, row1447, checked1447, derived1447⟩

def raw1448 : List String := ["function clause decode64 ((", "0b", "00111000011", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1448", ") = {\n    SEE = ", "1448", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_register_memory_single_general_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1448 : Clause := ⟨[.fixed "00111000011", .any 9, .fixed "10", .any 10], 1448, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_register_memory_single_general_register__decode"⟩
theorem checked1448 : check raw1448 clause1448 = true := by rfl
def row1448 : Row := ⟨1448, 4292873216, 945817600⟩
theorem derived1448 : clause1448.row = row1448 := by rfl
def entry1448 : CheckedRow := ⟨raw1448, clause1448, row1448, checked1448, derived1448⟩

def raw1449 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "101001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1449", ") = {\n    SEE = ", "1449", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_pair_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1449 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "101001", .any 10], 1449, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_pair_decode"⟩
theorem checked1449 : check raw1449 clause1449 = true := by rfl
def row1449 : Row := ⟨1449, 3206609920, 773891072⟩
theorem derived1449 : clause1449.row = row1449 := by rfl
def entry1449 : CheckedRow := ⟨raw1449, clause1449, row1449, checked1449, derived1449⟩

def entries52 : List CheckedRow := [entry1442, entry1443, entry1444, entry1445, entry1446, entry1447, entry1448, entry1449]
def rows52 : List Row := [row1442, row1443, row1444, row1445, row1446, row1447, row1448, row1449]
theorem indices52 : rows52.map Row.index = [1442, 1443, 1444, 1445, 1446, 1447, 1448, 1449] := by rfl
theorem bound52 : entries52.map CheckedRow.row = rows52 := by rfl
theorem choices_and_52 : choices rows52 167837696#32 (-1) = [] := by rfl
theorem choices_orr_52 : choices rows52 704708608#32 (-1) = [] := by rfl
theorem choices_eor_52 : choices rows52 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_52 : choices rows52 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
