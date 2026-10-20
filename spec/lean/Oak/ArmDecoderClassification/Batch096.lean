import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1794 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1794", ") = {\n    SEE = ", "1794", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_simd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1794 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "1", .any 5, .fixed "010101", .any 10], 1794, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_shift_simd_decode"⟩
theorem checked1794 : check raw1794 clause1794 = true := by rfl
def row1794 : Row := ⟨1794, 3206609920, 236999680⟩
theorem derived1794 : clause1794.row = row1794 := by rfl
def entry1794 : CheckedRow := ⟨raw1794, clause1794, row1794, checked1794, derived1794⟩

def raw1795 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100001010010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1795", ") = {\n    SEE = ", "1795", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_extract_sat_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1795 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "100001010010", .any 10], 1795, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_extract_sat_sisd_decode"⟩
theorem checked1795 : check raw1795 clause1795 = true := by rfl
def row1795 : Row := ⟨1795, 4282383360, 2116110336⟩
theorem derived1795 : clause1795.row = row1795 := by rfl
def entry1795 : CheckedRow := ⟨raw1795, clause1795, row1795, checked1795, derived1795⟩

def raw1796 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "010101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1796", ") = {\n    SEE = ", "1796", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "R", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_shift_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "S", ", ", "R", ", ", "Rm", ", ", "size", ", ", "U", ")\n}\n"]
def clause1796 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "1", .any 5, .fixed "010101", .any 10], 1796, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"S", 1, 11, 11, true⟩, ⟨"R", 1, 12, 12, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_shift_sisd_decode"⟩
theorem checked1796 : check raw1796 clause1796 = true := by rfl
def row1796 : Row := ⟨1796, 4280351744, 2116047872⟩
theorem derived1796 : clause1796.row = row1796 := by rfl
def entry1796 : CheckedRow := ⟨raw1796, clause1796, row1796, checked1796, derived1796⟩

def raw1797 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000010010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1797", ") = {\n    SEE = ", "1797", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_unary_clsz_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1797 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "100000010010", .any 10], 1797, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_unary_clsz_decode"⟩
theorem checked1797 : check raw1797 clause1797 = true := by rfl
def row1797 : Row := ⟨1797, 3208641536, 236996608⟩
theorem derived1797 : clause1797.row = row1797 := by rfl
def entry1797 : CheckedRow := ⟨raw1797, clause1797, row1797, checked1797, derived1797⟩

def raw1798 : List String := ["function clause decode64 ((", "0b", "01111110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "100000101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1798", ") = {\n    SEE = ", "1798", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_diffneg_int_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ")\n}\n"]
def clause1798 : Clause := ⟨[.fixed "01111110", .any 2, .fixed "100000101110", .any 10], 1798, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_diffneg_int_sisd_decode"⟩
theorem checked1798 : check raw1798 clause1798 = true := by rfl
def row1798 : Row := ⟨1798, 4282383360, 2116073472⟩
theorem derived1798 : clause1798.row = row1798 := by rfl
def entry1798 : CheckedRow := ⟨raw1798, clause1798, row1798, checked1798, derived1798⟩

def raw1799 : List String := ["function clause decode64 ((", "0b", "11010101000000110010000001111111", " as op_code) if SEE < ", "1799", ") = {\n    SEE = ", "1799", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "op0", " : bits(", "2", ") = ", "op_code[", "20", " .. ", "19", "]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_hints_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "op0", ", ", "L", ")\n}\n"]
def clause1799 : Clause := ⟨[.fixed "11010101000000110010000001111111"], 1799, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"op0", 2, 20, 19, false⟩, ⟨"L", 1, 21, 21, true⟩], "system_hints_decode"⟩
theorem checked1799 : check raw1799 clause1799 = true := by rfl
def row1799 : Row := ⟨1799, 4294967295, 3573751935⟩
theorem derived1799 : clause1799.row = row1799 := by rfl
def entry1799 : CheckedRow := ⟨raw1799, clause1799, row1799, checked1799, derived1799⟩

def raw1800 : List String := ["function clause decode64 ((", "0b", "110101010011", " @ ", "_ : bits(", "20", ")", " as op_code) if SEE < ", "1800", ") = {\n    SEE = ", "1800", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "op2", " : bits(", "3", ") = ", "op_code[", "7", " .. ", "5", "]", ";\n", "    ", "CRm", " : bits(", "4", ") = ", "op_code[", "11", " .. ", "8", "]", ";\n", "    ", "CRn", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "op1", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "o0", " : bits(", "1", ") = ", "[op_code[", "19", "]]", ";\n", "    ", "L", " : bits(", "1", ") = ", "[op_code[", "21", "]]", ";\n", "    ", "system_register_system_decode", "(", "Rt", ", ", "op2", ", ", "CRm", ", ", "CRn", ", ", "op1", ", ", "o0", ", ", "L", ")\n}\n"]
def clause1800 : Clause := ⟨[.fixed "110101010011", .any 20], 1800, [⟨"Rt", 5, 4, 0, false⟩, ⟨"op2", 3, 7, 5, false⟩, ⟨"CRm", 4, 11, 8, false⟩, ⟨"CRn", 4, 15, 12, false⟩, ⟨"op1", 3, 18, 16, false⟩, ⟨"o0", 1, 19, 19, true⟩, ⟨"L", 1, 21, 21, true⟩], "system_register_system_decode"⟩
theorem checked1800 : check raw1800 clause1800 = true := by rfl
def row1800 : Row := ⟨1800, 4293918720, 3576692736⟩
theorem derived1800 : clause1800.row = row1800 := by rfl
def entry1800 : CheckedRow := ⟨raw1800, clause1800, row1800, checked1800, derived1800⟩

def raw1801 : List String := ["function clause decode64 ((", "0b", "010111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111001", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1801", ") = {\n    SEE = ", "1801", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "ac", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "E", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "ac", ", ", "Rm", ", ", "sz", ", ", "E", ", ", "U", ")\n}\n"]
def clause1801 : Clause := ⟨[.fixed "010111100", .any 1, .fixed "1", .any 5, .fixed "111001", .any 10], 1801, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"ac", 1, 11, 11, true⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"E", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_binary_uniform_cmp_fp_sisd_decode"⟩
theorem checked1801 : check raw1801 clause1801 = true := by rfl
def row1801 : Row := ⟨1801, 4288740352, 1579213824⟩
theorem derived1801 : clause1801.row = row1801 := by rfl
def entry1801 : CheckedRow := ⟨raw1801, clause1801, row1801, checked1801, derived1801⟩

def entries96 : List CheckedRow := [entry1794, entry1795, entry1796, entry1797, entry1798, entry1799, entry1800, entry1801]
def rows96 : List Row := [row1794, row1795, row1796, row1797, row1798, row1799, row1800, row1801]
theorem indices96 : rows96.map Row.index = [1794, 1795, 1796, 1797, 1798, 1799, 1800, 1801] := by rfl
theorem bound96 : entries96.map CheckedRow.row = rows96 := by rfl
theorem choices_and_96 : choices rows96 167837696#32 (-1) = [] := by rfl
theorem choices_orr_96 : choices rows96 704708608#32 (-1) = [] := by rfl
theorem choices_eor_96 : choices rows96 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_96 : choices rows96 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
