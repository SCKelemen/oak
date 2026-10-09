import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1874 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0110101", " @ ", "_ : bits(", "24", ")", " as op_code) if SEE < ", "1874", ") = {\n    SEE = ", "1874", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "imm19", " : bits(", "19", ") = ", "op_code[", "23", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "24", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "branch_conditional_compare_decode", "(", "Rt", ", ", "imm19", ", ", "op", ", ", "sf", ")\n}\n"]
def clause1874 : Clause := ⟨[.any 1, .fixed "0110101", .any 24], 1874, [⟨"Rt", 5, 4, 0, false⟩, ⟨"imm19", 19, 23, 5, false⟩, ⟨"op", 1, 24, 24, true⟩, ⟨"sf", 1, 31, 31, true⟩], "branch_conditional_compare_decode"⟩
theorem checked1874 : check raw1874 clause1874 = true := by rfl
def row1874 : Row := ⟨1874, 2130706432, 889192448⟩
theorem derived1874 : clause1874.row = row1874 := by rfl
def entry1874 : CheckedRow := ⟨raw1874, clause1874, row1874, checked1874, derived1874⟩

def raw1875 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001100010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1875", ") = {\n    SEE = ", "1875", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_float_round_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "sz", ", ", "o2", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1875 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011100", .any 1, .fixed "100001100010", .any 10], 1875, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_float_round_decode"⟩
theorem checked1875 : check raw1875 clause1875 = true := by rfl
def row1875 : Row := ⟨1875, 3217030144, 773949440⟩
theorem derived1875 : clause1875.row = row1875 := by rfl
def entry1875 : CheckedRow := ⟨raw1875, clause1875, row1875, checked1875, derived1875⟩

def raw1876 : List String := ["function clause decode64 ((", "_ : bits(", "2", ")", " @ ", "0b", "10110111", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1876", ") = {\n    SEE = ", "1876", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "imm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_pair_simdfp_preidx_memory_pair_simdfp_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "imm7", ", ", "L", ", ", "V", ", ", "opc", ")\n}\n"]
def clause1876 : Clause := ⟨[.any 2, .fixed "10110111", .any 22], 1876, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"imm7", 7, 21, 15, false⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"opc", 2, 31, 30, false⟩], "memory_pair_simdfp_preidx_memory_pair_simdfp_postidx__decode"⟩
theorem checked1876 : check raw1876 clause1876 = true := by rfl
def row1876 : Row := ⟨1876, 1069547520, 767557632⟩
theorem derived1876 : clause1876.row = row1876 := by rfl
def entry1876 : CheckedRow := ⟨raw1876, clause1876, row1876, checked1876, derived1876⟩

def raw1877 : List String := ["function clause decode64 ((", "0b", "00011001010", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "00", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1877", ") = {\n    SEE = ", "1877", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm9", " : bits(", "9", ") = ", "op_code[", "20", " .. ", "12", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode", "(", "Rt", ", ", "Rn", ", ", "imm9", ", ", "opc", ", ", "size", ")\n}\n"]
def clause1877 : Clause := ⟨[.fixed "00011001010", .any 9, .fixed "00", .any 10], 1877, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm9", 9, 20, 12, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_signed_offset_lda_stl_memory_single_general_immediate_signed_offset_lda_stl__decode"⟩
theorem checked1877 : check raw1877 clause1877 = true := by rfl
def row1877 : Row := ⟨1877, 4292873216, 423624704⟩
theorem derived1877 : clause1877.row = row1877 := by rfl
def entry1877 : CheckedRow := ⟨raw1877, clause1877, row1877, checked1877, derived1877⟩

def raw1878 : List String := ["function clause decode64 ((", "0b", "11010101000000110010000011111111", " as op_code) if SEE < ", "1878", ") = {\n    SEE = ", "1878", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "integer_pac_strip_hint_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1878 : Clause := ⟨[.fixed "11010101000000110010000011111111"], 1878, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "integer_pac_strip_hint_decode"⟩
theorem checked1878 : check raw1878 clause1878 = true := by rfl
def row1878 : Row := ⟨1878, 4294967295, 3573752063⟩
theorem derived1878 : clause1878.row = row1878 := by rfl
def entry1878 : CheckedRow := ⟨raw1878, clause1878, row1878, checked1878, derived1878⟩

def raw1879 : List String := ["function clause decode64 ((", "0b", "1", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "111000001", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1879", ") = {\n    SEE = ", "1879", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_register_memory_single_general_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1879 : Clause := ⟨[.fixed "1", .any 1, .fixed "111000001", .any 9, .fixed "10", .any 10], 1879, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_register_memory_single_general_register__decode"⟩
theorem checked1879 : check raw1879 clause1879 = true := by rfl
def row1879 : Row := ⟨1879, 3219131392, 3089106944⟩
theorem derived1879 : clause1879.row = row1879 := by rfl
def entry1879 : CheckedRow := ⟨raw1879, clause1879, row1879, checked1879, derived1879⟩

def raw1880 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110110", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "000001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1880", ") = {\n    SEE = ", "1880", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Op3", " : bits(", "3", ") = ", "op_code[", "13", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "a", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode", "(", "Rd", ", ", "Rn", ", ", "Op3", ", ", "Rm", ", ", "a", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1880 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110110", .any 5, .fixed "000001", .any 10], 1880, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Op3", 3, 13, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"a", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_maxmin_fp16_2008_decode"⟩
theorem checked1880 : check raw1880 clause1880 = true := by rfl
def row1880 : Row := ⟨1880, 3219192832, 784335872⟩
theorem derived1880 : clause1880.row = row1880 := by rfl
def entry1880 : CheckedRow := ⟨raw1880, clause1880, row1880, checked1880, derived1880⟩

def raw1881 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "101110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001001110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1881", ") = {\n    SEE = ", "1881", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_shift_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1881 : Clause := ⟨[.fixed "0", .any 1, .fixed "101110", .any 2, .fixed "100001001110", .any 10], 1881, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_shift_decode"⟩
theorem checked1881 : check raw1881 clause1881 = true := by rfl
def row1881 : Row := ⟨1881, 3208641536, 773928960⟩
theorem derived1881 : clause1881.row = row1881 := by rfl
def entry1881 : CheckedRow := ⟨raw1881, clause1881, row1881, checked1881, derived1881⟩

def entries106 : List CheckedRow := [entry1874, entry1875, entry1876, entry1877, entry1878, entry1879, entry1880, entry1881]
def rows106 : List Row := [row1874, row1875, row1876, row1877, row1878, row1879, row1880, row1881]
theorem indices106 : rows106.map Row.index = [1874, 1875, 1876, 1877, 1878, 1879, 1880, 1881] := by rfl
theorem bound106 : entries106.map CheckedRow.row = rows106 := by rfl
theorem choices_and_106 : choices rows106 167837696#32 (-1) = [] := by rfl
theorem choices_orr_106 : choices rows106 704708608#32 (-1) = [] := by rfl
theorem choices_eor_106 : choices rows106 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_106 : choices rows106 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
