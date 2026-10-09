import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1834 : List String := ["function clause decode64 ((", "_ : bits(", "1", ")", " @ ", "0b", "0011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "000011", " @ ", "_ : bits(", "16", ")", " as op_code) if SEE < ", "1834", ") = {\n    SEE = ", "1834", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "scale", " : bits(", "6", ") = ", "op_code[", "15", " .. ", "10", "]", ";\n", "    ", "opcode", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "rmode", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "sf", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_convert_fix_decode", "(", "Rd", ", ", "Rn", ", ", "scale", ", ", "opcode", ", ", "rmode", ", ", "typ", ", ", "S", ", ", "sf", ")\n}\n"]
def clause1834 : Clause := ⟨[.any 1, .fixed "0011110", .any 2, .fixed "000011", .any 16], 1834, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"scale", 6, 15, 10, false⟩, ⟨"opcode", 3, 18, 16, false⟩, ⟨"rmode", 2, 20, 19, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"sf", 1, 31, 31, true⟩], "float_convert_fix_decode"⟩
theorem checked1834 : check raw1834 clause1834 = true := by rfl
def row1834 : Row := ⟨1834, 2134835200, 503513088⟩
theorem derived1834 : clause1834.row = row1834 := by rfl
def entry1834 : CheckedRow := ⟨raw1834, clause1834, row1834, checked1834, derived1834⟩

def raw1835 : List String := ["function clause decode64 ((", "0b", "11010101000000110011", " @ ", "_ : bits(", "4", ")", " @ ", "0b", "11111111", " as op_code) if SEE < ", "1835", ") = {\n    SEE = ", "1835", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "6", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_barriers_decode", "(", "Rt", ", ", "opc", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1835 : Clause := ⟨[.fixed "11010101000000110011", .any 4, .fixed "11111111"], 1835, [⟨"Rt", 5, 4, 0, false⟩, ⟨"opc", 2, 6, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_barriers_decode"⟩
theorem checked1835 : check raw1835 clause1835 = true := by rfl
def row1835 : Row := ⟨1835, 4294963455, 3573756159⟩
theorem derived1835 : clause1835.row = row1835 := by rfl
def entry1835 : CheckedRow := ⟨raw1835, clause1835, row1835, checked1835, derived1835⟩

def raw1836 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "110000110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1836", ") = {\n    SEE = ", "1836", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_fpmaxnm_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "o1", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1836 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "110000110010", .any 10], 1836, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"o1", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_fpmaxnm_simd_decode"⟩
theorem checked1836 : check raw1836 clause1836 = true := by rfl
def row1836 : Row := ⟨1836, 3217030144, 783337472⟩
theorem derived1836 : clause1836.row = row1836 := by rfl
def entry1836 : CheckedRow := ⟨raw1836, clause1836, row1836, checked1836, derived1836⟩

def raw1837 : List String := ["function clause decode64 ((", "0b", "01001000010", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "15", ")", " as op_code) if SEE < ", "1837", ") = {\n    SEE = ", "1837", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Rt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_exclusive_single_decode", "(", "Rt", ", ", "Rn", ", ", "Rt2", ", ", "o0", ", ", "Rs", ", ", "o1", ", ", "L", ", ", "o2", ", ", "size", ")\n}\n"]
def clause1837 : Clause := ⟨[.fixed "01001000010", .any 5, .fixed "0", .any 15], 1837, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"Rt2", 5, 14, 10, false⟩, ⟨"o0", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"o1", 1, 21, 21, true⟩, ⟨"L", 1, 22, 22, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_exclusive_single_decode"⟩
theorem checked1837 : check raw1837 clause1837 = true := by rfl
def row1837 : Row := ⟨1837, 4292902912, 1212153856⟩
theorem derived1837 : clause1837.row = row1837 := by rfl
def entry1837 : CheckedRow := ⟨raw1837, clause1837, row1837, checked1837, derived1837⟩

def raw1838 : List String := ["function clause decode64 ((", "0b", "01011111", " @ ", "_ : bits(", "8", ")", " @ ", "0b", "1100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1838", ") = {\n    SEE = ", "1838", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "H", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "4", ") = ", "op_code[", "19", " .. ", "16", "]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "20", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_element_mul_high_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "H", ", ", "op", ", ", "Rm", ", ", "M", ", ", "L", ", ", "size", ", ", "U", ")\n}\n"]
def clause1838 : Clause := ⟨[.fixed "01011111", .any 8, .fixed "1100", .any 1, .fixed "0", .any 10], 1838, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"H", 1, 11, 11, true⟩, ⟨"op", 1, 12, 12, true⟩, ⟨"Rm", 4, 19, 16, false⟩, ⟨"M", 1, 20, 20, true⟩, ⟨"L", 1, 21, 21, true⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_element_mul_high_sisd_decode"⟩
theorem checked1838 : check raw1838 clause1838 = true := by rfl
def row1838 : Row := ⟨1838, 4278252544, 1593884672⟩
theorem derived1838 : clause1838.row = row1838 := by rfl
def entry1838 : CheckedRow := ⟨raw1838, clause1838, row1838, checked1838, derived1838⟩

def raw1839 : List String := ["function clause decode64 ((", "0b", "01111000011", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "10", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1839", ") = {\n    SEE = ", "1839", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "option_name", " : bits(", "3", ") = ", "op_code[", "15", " .. ", "13", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_register_memory_single_general_register__decode", "(", "Rt", ", ", "Rn", ", ", "S", ", ", "option_name", ", ", "Rm", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1839 : Clause := ⟨[.fixed "01111000011", .any 9, .fixed "10", .any 10], 1839, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 12, 12, true⟩, ⟨"option_name", 3, 15, 13, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_register_memory_single_general_register__decode"⟩
theorem checked1839 : check raw1839 clause1839 = true := by rfl
def row1839 : Row := ⟨1839, 4292873216, 2019559424⟩
theorem derived1839 : clause1839.row = row1839 := by rfl
def entry1839 : CheckedRow := ⟨raw1839, clause1839, row1839, checked1839, derived1839⟩

def raw1840 : List String := ["function clause decode64 ((", "0b", "00111000", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010000", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1840", ") = {\n    SEE = ", "1840", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opc", " : bits(", "3", ") = ", "op_code[", "14", " .. ", "12", "]", ";\n", "    ", "o3", " : bits(", "1", ") = ", "[op_code[", "15", "]]", ";\n", "    ", "Rs", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "A", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_atomicops_ld_decode", "(", "Rt", ", ", "Rn", ", ", "opc", ", ", "o3", ", ", "Rs", ", ", "R", ", ", "A", ", ", "V", ", ", "size", ")\n}\n"]
def clause1840 : Clause := ⟨[.fixed "00111000", .any 2, .fixed "1", .any 5, .fixed "010000", .any 10], 1840, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opc", 3, 14, 12, false⟩, ⟨"o3", 1, 15, 15, true⟩, ⟨"Rs", 5, 20, 16, false⟩, ⟨"R", 1, 22, 22, true⟩, ⟨"A", 1, 23, 23, true⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_atomicops_ld_decode"⟩
theorem checked1840 : check raw1840 clause1840 = true := by rfl
def row1840 : Row := ⟨1840, 4280351744, 941637632⟩
theorem derived1840 : clause1840.row = row1840 := by rfl
def entry1840 : CheckedRow := ⟨raw1840, clause1840, row1840, checked1840, derived1840⟩

def raw1841 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111011", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1841", ") = {\n    SEE = ", "1841", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_simd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1841 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011101", .any 1, .fixed "1", .any 5, .fixed "111011", .any 10], 1841, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_simd_decode"⟩
theorem checked1841 : check raw1841 clause1841 = true := by rfl
def row1841 : Row := ⟨1841, 3214998528, 782298112⟩
theorem derived1841 : clause1841.row = row1841 := by rfl
def entry1841 : CheckedRow := ⟨raw1841, clause1841, row1841, checked1841, derived1841⟩

def entries101 : List CheckedRow := [entry1834, entry1835, entry1836, entry1837, entry1838, entry1839, entry1840, entry1841]
def rows101 : List Row := [row1834, row1835, row1836, row1837, row1838, row1839, row1840, row1841]
theorem indices101 : rows101.map Row.index = [1834, 1835, 1836, 1837, 1838, 1839, 1840, 1841] := by rfl
theorem bound101 : entries101.map CheckedRow.row = rows101 := by rfl
theorem choices_and_101 : choices rows101 167837696#32 (-1) = [] := by rfl
theorem choices_orr_101 : choices rows101 704708608#32 (-1) = [] := by rfl
theorem choices_eor_101 : choices rows101 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_101 : choices rows101 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
