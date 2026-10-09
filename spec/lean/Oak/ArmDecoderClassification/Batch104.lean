import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1858 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0101010", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1858", ") = {\n    SEE = ", "1858", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm6", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "N", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "shift", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "30", " .. ", "29", "]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_logical_shiftedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm6", ", ", "Rm", ", ", "N", ", ", "shift", ", ", "opc", ", ", "sf", ")\n}\n"]
def clause1858 : Clause := ⟨[.any 1, .fixed "0101010", .any 2, .fixed "0", .any 21], 1858, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm6", 6, 15, 10, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"N", 1, 21, 21, true⟩, ⟨"shift", 2, 23, 22, false⟩, ⟨"opc", 2, 30, 29, false⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_logical_shiftedreg_decode"⟩
theorem checked1858 : check raw1858 clause1858 = true := by rfl
def row1858 : Row := ⟨1858, 2132803584, 704643072⟩
theorem derived1858 : clause1858.row = row1858 := by rfl
def entry1858 : CheckedRow := ⟨raw1858, clause1858, row1858, checked1858, derived1858⟩

def raw1859 : List String := ["function clause decode64 ((", "0b", "011111101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1859", ") = {\n    SEE = ", "1859", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_sub_fp_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1859 : Clause := ⟨[.fixed "011111101", .any 1, .fixed "1", .any 5, .fixed "110101", .any 10], 1859, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_sub_fp_sisd_decode"⟩
theorem checked1859 : check raw1859 clause1859 = true := by rfl
def row1859 : Row := ⟨1859, 4288740352, 2124469248⟩
theorem derived1859 : clause1859.row = row1859 := by rfl
def entry1859 : CheckedRow := ⟨raw1859, clause1859, row1859, checked1859, derived1859⟩

def raw1860 : List String := ["function clause decode64 ((", "0b", "001110011", " @ ", "_ : bits(", "23", ")", " as op_code) if SEE < ", "1860", ") = {\n    SEE = ", "1860", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1860 : Clause := ⟨[.fixed "001110011", .any 23], 1860, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1860 : check raw1860 clause1860 = true := by rfl
def row1860 : Row := ⟨1860, 4286578688, 964689920⟩
theorem derived1860 : clause1860.row = row1860 := by rfl
def entry1860 : CheckedRow := ⟨raw1860, clause1860, row1860, checked1860, derived1860⟩

def raw1861 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1861", ") = {\n    SEE = ", "1861", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_right_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o0", ", ", "o1", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1861 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011110", .any 7, .fixed "000001", .any 10], 1861, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o0", 1, 12, 12, true⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_right_simd_decode"⟩
theorem checked1861 : check raw1861 clause1861 = true := by rfl
def row1861 : Row := ⟨1861, 3212901376, 251659264⟩
theorem derived1861 : clause1861.row = row1861 := by rfl
def entry1861 : CheckedRow := ⟨raw1861, clause1861, row1861, checked1861, derived1861⟩

def raw1862 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "1101011001", " @ ", "_ : bits(", "21", ")", " as op_code) if SEE < ", "1862", ") = {\n    SEE = ", "1862", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm3", " : bits(", "3", ") = ", "op_code[", "12", " .. ", "10", "]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opt", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "integer_arithmetic_addsub_extendedreg_decode", "(", "Rd", ", ", "Rn", ", ", "imm3", ", ", "option_name", ", ", "Rm", ", ", "opt", ", ", "S", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1862 : Clause := ⟨[.any 1, .fixed "1101011001", .any 21], 1862, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm3", 3, 12, 10, false⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opt", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"op", 1, 30, 30, true⟩, ⟨"sf", 1, 31, 31, true⟩], "integer_arithmetic_addsub_extendedreg_decode"⟩
theorem checked1862 : check raw1862 clause1862 = true := by rfl
def row1862 : Row := ⟨1862, 2145386496, 1797259264⟩
theorem derived1862 : clause1862.row = row1862 := by rfl
def entry1862 : CheckedRow := ⟨raw1862, clause1862, row1862, checked1862, derived1862⟩

def raw1863 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "101100", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1863", ") = {\n    SEE = ", "1863", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_dmacc_simd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1863 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "101100", .any 10], 1863, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 13, 13, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_mul_dmacc_simd_decode"⟩
theorem checked1863 : check raw1863 clause1863 = true := by rfl
def row1863 : Row := ⟨1863, 3206609920, 237023232⟩
theorem derived1863 : clause1863.row = row1863 := by rfl
def entry1863 : CheckedRow := ⟨raw1863, clause1863, row1863, checked1863, derived1863⟩

def raw1864 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001101110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "13", ")", " as op_code) if SEE < ", "1864", ") = {\n    SEE = ", "1864", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "11", " .. ", "10", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "memory_vector_single_postinc_memory_vector_single_nowb__decode", "(", "Rt", ", ", "Rn", ", ", "size", ", ", "S", ", ", "opcode", ", ", "Rm", ", ", "R", ", ", "L", ", ", "Q", ")\n}\n"]
def clause1864 : Clause := ⟨[.fixed "0", .any 1, .fixed "001101110", .any 7, .fixed "0", .any 13], 1864, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"size", 2, 11, 10, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"opcode", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"R", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"Q", 1, 30, 30, true⟩], "memory_vector_single_postinc_memory_vector_single_nowb__decode"⟩
theorem checked1864 : check raw1864 clause1864 = true := by rfl
def row1864 : Row := ⟨1864, 3219136512, 230686720⟩
theorem derived1864 : clause1864.row = row1864 := by rfl
def entry1864 : CheckedRow := ⟨raw1864, clause1864, row1864, checked1864, derived1864⟩

def raw1865 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "110000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1865", ") = {\n    SEE = ", "1865", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode_0_", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "opcode_1_", " : bits(", "1", ") = ", "[op_code[", "13", "]]", ";\n", "    ", "opcode_2_", " : bits(", "1", ") = ", "[op_code[", "14", "]]", ";\n", "    ", "opcode_3_", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_disparate_mul_product_decode", "(", "Rd", ", ", "Rn", ", ", "opcode_0_", ", ", "opcode_1_", ", ", "opcode_2_", ", ", "opcode_3_", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1865 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "1", .any 5, .fixed "110000", .any 10], 1865, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode_0_", 1, 12, 12, true⟩, ⟨"opcode_1_", 1, 13, 13, true⟩, ⟨"opcode_2_", 1, 14, 14, true⟩, ⟨"opcode_3_", 1, 15, 15, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_disparate_mul_product_decode"⟩
theorem checked1865 : check raw1865 clause1865 = true := by rfl
def row1865 : Row := ⟨1865, 3206609920, 773898240⟩
theorem derived1865 : clause1865.row = row1865 := by rfl
def entry1865 : CheckedRow := ⟨raw1865, clause1865, row1865, checked1865, derived1865⟩

def entries104 : List CheckedRow := [entry1858, entry1859, entry1860, entry1861, entry1862, entry1863, entry1864, entry1865]
def rows104 : List Row := [row1858, row1859, row1860, row1861, row1862, row1863, row1864, row1865]
theorem indices104 : rows104.map Row.index = [1858, 1859, 1860, 1861, 1862, 1863, 1864, 1865] := by rfl
theorem bound104 : entries104.map CheckedRow.row = rows104 := by rfl
theorem choices_and_104 : choices rows104 167837696#32 (-1) = [] := by rfl
theorem choices_orr_104 : choices rows104 704708608#32 (-1) = [1858] := by rfl
theorem choices_eor_104 : choices rows104 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_104 : choices rows104 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
