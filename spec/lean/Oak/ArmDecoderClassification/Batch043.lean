import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1370 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1370", ") = {\n    SEE = ", "1370", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_saturating_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1370 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "001011", .any 10], 1370, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_sub_saturating_simd_decode"⟩
theorem checked1370 : check raw1370 clause1370 = true := by rfl
def row1370 : Row := ⟨1370, 3206609920, 773860352⟩
theorem derived1370 : clause1370.row = row1370 := by rfl
def entry1370 : CheckedRow := ⟨raw1370, clause1370, row1370, checked1370, derived1370⟩

def raw1371 : List String := ["function clause decode64 ((", "0b", "01011111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "0011", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1371", ") = {\n    SEE = ", "1371", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mulacc_double_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "o2", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1371 : Clause := ⟨[.fixed "01011111", .any 8, .fixed "0011", .any 1, .fixed "0", .any 10], 1371, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"o2", 1, 14, 14, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mulacc_double_sisd_decode"⟩
theorem checked1371 : check raw1371 clause1371 = true := by rfl
def row1371 : Row := ⟨1371, 4278252544, 1593847808⟩
theorem derived1371 : clause1371.row = row1371 := by rfl
def entry1371 : CheckedRow := ⟨raw1371, clause1371, row1371, checked1371, derived1371⟩

def raw1372 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101101", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1372", ") = {\n    SEE = ", "1372", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1372 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101101", .any 7, .fixed "0", .any 13], 1372, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1372 : check raw1372 clause1372 = true := by rfl
def row1372 : Row := ⟨1372, 3219136512, 228589568⟩
theorem derived1372 : clause1372.row = row1372 := by rfl
def entry1372 : CheckedRow := ⟨raw1372, clause1372, row1372, checked1372, derived1372⟩

def raw1373 : List String := ["function clause decode64 ((", "0b", "01111110010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1373", ") = {\n    SEE = ", "1373", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "E", ", ", "U", ")\n}\n"]
def clause1373 : Clause := ⟨[.fixed "01111110010", .any 5, .fixed "001001", .any 10], 1373, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_fp16_sisd_decode"⟩
theorem checked1373 : check raw1373 clause1373 = true := by rfl
def row1373 : Row := ⟨1373, 4292934656, 2118132736⟩
theorem derived1373 : clause1373.row = row1373 := by rfl
def entry1373 : CheckedRow := ⟨raw1373, clause1373, row1373, checked1373, derived1373⟩

def raw1374 : List String := ["function clause decode64 ((", "0b", "10011001000", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1374", ") = {\n    SEE = ", "1374", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1374 : Clause := ⟨[.fixed "10011001000", .any 9, .fixed "00", .any 10], 1374, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1374 : check raw1374 clause1374 = true := by rfl
def row1374 : Row := ⟨1374, 4292873216, 2566914048⟩
theorem derived1374 : clause1374.row = row1374 := by rfl
def entry1374 : CheckedRow := ⟨raw1374, clause1374, row1374, checked1374, derived1374⟩

def raw1375 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1375", ") = {\n    SEE = ", "1375", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_add_halving_rounding_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1375 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "000101", .any 10], 1375, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_add_halving_rounding_decode"⟩
theorem checked1375 : check raw1375 clause1375 = true := by rfl
def row1375 : Row := ⟨1375, 3206609920, 236983296⟩
theorem derived1375 : clause1375.row = row1375 := by rfl
def entry1375 : CheckedRow := ⟨raw1375, clause1375, row1375, checked1375, derived1375⟩

def raw1376 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1376", ") = {\n    SEE = ", "1376", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_simdfp_immediate_unsigned_memory_single_simdfp_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1376 : Clause := ⟨[.any 2, .fixed "111101", .any 1, .fixed "0", .any 22], 1376, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_simdfp_immediate_unsigned_memory_single_simdfp_immediate_signed_postidx__decode"⟩
theorem checked1376 : check raw1376 clause1376 = true := by rfl
def row1376 : Row := ⟨1376, 1061158912, 1023410176⟩
theorem derived1376 : clause1376.row = row1376 := by rfl
def entry1376 : CheckedRow := ⟨raw1376, clause1376, row1376, checked1376, derived1376⟩

def raw1377 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1377", ") = {\n    SEE = ", "1377", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_transfer_vector_permute_zip_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "Rm", ", ", "size", ", ", "Q", ")\n}\n"]
def clause1377 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "0", .any 5, .fixed "001110", .any 10], 1377, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 14, 14, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_transfer_vector_permute_zip_decode"⟩
theorem checked1377 : check raw1377 clause1377 = true := by rfl
def row1377 : Row := ⟨1377, 3206609920, 234895360⟩
theorem derived1377 : clause1377.row = row1377 := by rfl
def entry1377 : CheckedRow := ⟨raw1377, clause1377, row1377, checked1377, derived1377⟩

def entries43 : List CheckedRow := [entry1370, entry1371, entry1372, entry1373, entry1374, entry1375, entry1376, entry1377]
def rows43 : List Row := [row1370, row1371, row1372, row1373, row1374, row1375, row1376, row1377]
theorem indices43 : rows43.map Row.index = [1370, 1371, 1372, 1373, 1374, 1375, 1376, 1377] := by rfl
theorem bound43 : entries43.map CheckedRow.row = rows43 := by rfl
theorem choices_and_43 : choices rows43 167837696#32 (-1) = [] := by rfl
theorem choices_orr_43 : choices rows43 704708608#32 (-1) = [] := by rfl
theorem choices_eor_43 : choices rows43 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_43 : choices rows43 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
