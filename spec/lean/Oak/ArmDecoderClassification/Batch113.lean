import Oak.ArmDecoderClassification.Checker

namespace Oak.ArmDecoderClassification.Data
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def raw1930 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "0011101", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "5", ")", " @ ", "0b", "111111", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1930", ") = {\n    SEE = ", "1930", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "15", " .. ", "11", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_arithmetic_binary_uniform_rsqrts_simd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "Rm", ", ", "sz", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1930 : Clause := ⟨[.fixed "0", .any 1, .fixed "0011101", .any 1, .fixed "1", .any 5, .fixed "111111", .any 10], 1930, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 15, 11, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_arithmetic_binary_uniform_rsqrts_simd_decode"⟩
theorem checked1930 : check raw1930 clause1930 = true := by rfl
def row1930 : Row := ⟨1930, 3214998528, 245431296⟩
theorem derived1930 : clause1930.row = row1930 := by rfl
def entry1930 : CheckedRow := ⟨raw1930, clause1930, row1930, checked1930, derived1930⟩

def raw1931 : List String := ["function clause decode64 ((", "0b", "1011100110", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1931", ") = {\n    SEE = ", "1931", ";\n", "    ", "Rt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "imm12", " : bits(", "12", ") = ", "op_code[", "21", " .. ", "10", "]", ";\n", "    ", "opc", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "V", " : bits(", "1", ") = ", "[op_code[", "26", "]]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "31", " .. ", "30", "]", ";\n", "    ", "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode", "(", "Rt", ", ", "Rn", ", ", "imm12", ", ", "opc", ", ", "V", ", ", "size", ")\n}\n"]
def clause1931 : Clause := ⟨[.fixed "1011100110", .any 22], 1931, [⟨"Rt", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"imm12", 12, 21, 10, false⟩, ⟨"opc", 2, 23, 22, false⟩, ⟨"V", 1, 26, 26, true⟩, ⟨"size", 2, 31, 30, false⟩], "memory_single_general_immediate_unsigned_memory_single_general_immediate_signed_postidx__decode"⟩
theorem checked1931 : check raw1931 clause1931 = true := by rfl
def row1931 : Row := ⟨1931, 4290772992, 3112173568⟩
theorem derived1931 : clause1931.row = row1931 := by rfl
def entry1931 : CheckedRow := ⟨raw1931, clause1931, row1931, checked1931, derived1931⟩

def raw1932 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "1011110", " @ ", "_ : bits(", "7", ")", " @ ", "0b", "100101", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1932", ") = {\n    SEE = ", "1932", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "op", " : bits(", "1", ") = ", "[op_code[", "11", "]]", ";\n", "    ", "immb", " : bits(", "3", ") = ", "op_code[", "18", " .. ", "16", "]", ";\n", "    ", "immh", " : bits(", "4", ") = ", "op_code[", "22", " .. ", "19", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_shift_rightnarrow_uniform_simd_decode", "(", "Rd", ", ", "Rn", ", ", "op", ", ", "immb", ", ", "immh", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1932 : Clause := ⟨[.fixed "0", .any 1, .fixed "1011110", .any 7, .fixed "100101", .any 10], 1932, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"op", 1, 11, 11, true⟩, ⟨"immb", 3, 18, 16, false⟩, ⟨"immh", 4, 22, 19, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_shift_rightnarrow_uniform_simd_decode"⟩
theorem checked1932 : check raw1932 clause1932 = true := by rfl
def row1932 : Row := ⟨1932, 3212901376, 788567040⟩
theorem derived1932 : clause1932.row = row1932 := by rfl
def entry1932 : CheckedRow := ⟨raw1932, clause1932, row1932, checked1932, derived1932⟩

def raw1933 : List String := ["function clause decode64 ((", "0b", "0101111001111001101110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1933", ") = {\n    SEE = ", "1933", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "o1", " : bits(", "1", ") = ", "[op_code[", "12", "]]", ";\n", "    ", "o2", " : bits(", "1", ") = ", "[op_code[", "23", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "o1", ", ", "o2", ", ", "U", ")\n}\n"]
def clause1933 : Clause := ⟨[.fixed "0101111001111001101110", .any 10], 1933, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"o1", 1, 12, 12, true⟩, ⟨"o2", 1, 23, 23, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_fp16_conv_float_bulk_sisd_decode"⟩
theorem checked1933 : check raw1933 clause1933 = true := by rfl
def row1933 : Row := ⟨1933, 4294966272, 1585035264⟩
theorem derived1933 : clause1933.row = row1933 := by rfl
def entry1933 : CheckedRow := ⟨raw1933, clause1933, row1933, checked1933, derived1933⟩

def raw1934 : List String := ["function clause decode64 ((", "0b", "010111100", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "100001110010", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1934", ") = {\n    SEE = ", "1934", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "sz", " : bits(", "1", ") = ", "[op_code[", "22", "]]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "sz", ", ", "U", ")\n}\n"]
def clause1934 : Clause := ⟨[.fixed "010111100", .any 1, .fixed "100001110010", .any 10], 1934, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"sz", 1, 22, 22, true⟩, ⟨"U", 1, 29, 29, true⟩], "vector_arithmetic_unary_float_conv_float_tieaway_sisd_decode"⟩
theorem checked1934 : check raw1934 clause1934 = true := by rfl
def row1934 : Row := ⟨1934, 4290771968, 1579272192⟩
theorem derived1934 : clause1934.row = row1934 := by rfl
def entry1934 : CheckedRow := ⟨raw1934, clause1934, row1934, checked1934, derived1934⟩

def raw1935 : List String := ["function clause decode64 ((", "0b", "0", " @ ", "_ : bits(", "1", ")", " @ ", "0b", "001110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "110000001110", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1935", ") = {\n    SEE = ", "1935", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "opcode", " : bits(", "5", ") = ", "op_code[", "16", " .. ", "12", "]", ";\n", "    ", "size", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "U", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "Q", " : bits(", "1", ") = ", "[op_code[", "30", "]]", ";\n", "    ", "vector_reduce_addlong_decode", "(", "Rd", ", ", "Rn", ", ", "opcode", ", ", "size", ", ", "U", ", ", "Q", ")\n}\n"]
def clause1935 : Clause := ⟨[.fixed "0", .any 1, .fixed "001110", .any 2, .fixed "110000001110", .any 10], 1935, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"opcode", 5, 16, 12, false⟩, ⟨"size", 2, 23, 22, false⟩, ⟨"U", 1, 29, 29, true⟩, ⟨"Q", 1, 30, 30, true⟩], "vector_reduce_addlong_decode"⟩
theorem checked1935 : check raw1935 clause1935 = true := by rfl
def row1935 : Row := ⟨1935, 3208641536, 238041088⟩
theorem derived1935 : clause1935.row = row1935 := by rfl
def entry1935 : CheckedRow := ⟨raw1935, clause1935, row1935, checked1935, derived1935⟩

def raw1936 : List String := ["function clause decode64 ((", "0b", "0110100010", " @ ", "_ : bits(", "22", ")", " as op_code) if SEE < ", "1936", ") = {\n    SEE = ", "1936", ";\n", "    ", "Xt", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Xn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "Xt2", " : bits(", "5", ") = ", "op_code[", "14", " .. ", "10", "]", ";\n", "    ", "simm7", " : bits(", "7", ") = ", "op_code[", "21", " .. ", "15", "]", ";\n", "    ", "integer_tags_mcsettaganddatapairpost_decode", "(", "Xt", ", ", "Xn", ", ", "Xt2", ", ", "simm7", ")\n}\n"]
def clause1936 : Clause := ⟨[.fixed "0110100010", .any 22], 1936, [⟨"Xt", 5, 4, 0, false⟩, ⟨"Xn", 5, 9, 5, false⟩, ⟨"Xt2", 5, 14, 10, false⟩, ⟨"simm7", 7, 21, 15, false⟩], "integer_tags_mcsettaganddatapairpost_decode"⟩
theorem checked1936 : check raw1936 clause1936 = true := by rfl
def row1936 : Row := ⟨1936, 4290772992, 1753219072⟩
theorem derived1936 : clause1936.row = row1936 := by rfl
def entry1936 : CheckedRow := ⟨raw1936, clause1936, row1936, checked1936, derived1936⟩

def raw1937 : List String := ["function clause decode64 ((", "0b", "00011110", " @ ", "_ : bits(", "2", ")", " @ ", "0b", "1", " @ ", "_ : bits(", "9", ")", " @ ", "0b", "11", " @ ", "_ : bits(", "10", ")", " as op_code) if SEE < ", "1937", ") = {\n    SEE = ", "1937", ";\n", "    ", "Rd", " : bits(", "5", ") = ", "op_code[", "4", " .. ", "0", "]", ";\n", "    ", "Rn", " : bits(", "5", ") = ", "op_code[", "9", " .. ", "5", "]", ";\n", "    ", "cond", " : bits(", "4", ") = ", "op_code[", "15", " .. ", "12", "]", ";\n", "    ", "Rm", " : bits(", "5", ") = ", "op_code[", "20", " .. ", "16", "]", ";\n", "    ", "typ", " : bits(", "2", ") = ", "op_code[", "23", " .. ", "22", "]", ";\n", "    ", "S", " : bits(", "1", ") = ", "[op_code[", "29", "]]", ";\n", "    ", "M", " : bits(", "1", ") = ", "[op_code[", "31", "]]", ";\n", "    ", "float_move_fp_select_decode", "(", "Rd", ", ", "Rn", ", ", "cond", ", ", "Rm", ", ", "typ", ", ", "S", ", ", "M", ")\n}\n"]
def clause1937 : Clause := ⟨[.fixed "00011110", .any 2, .fixed "1", .any 9, .fixed "11", .any 10], 1937, [⟨"Rd", 5, 4, 0, false⟩, ⟨"Rn", 5, 9, 5, false⟩, ⟨"cond", 4, 15, 12, false⟩, ⟨"Rm", 5, 20, 16, false⟩, ⟨"typ", 2, 23, 22, false⟩, ⟨"S", 1, 29, 29, true⟩, ⟨"M", 1, 31, 31, true⟩], "float_move_fp_select_decode"⟩
theorem checked1937 : check raw1937 clause1937 = true := by rfl
def row1937 : Row := ⟨1937, 4280290304, 505416704⟩
theorem derived1937 : clause1937.row = row1937 := by rfl
def entry1937 : CheckedRow := ⟨raw1937, clause1937, row1937, checked1937, derived1937⟩

def entries113 : List CheckedRow := [entry1930, entry1931, entry1932, entry1933, entry1934, entry1935, entry1936, entry1937]
def rows113 : List Row := [row1930, row1931, row1932, row1933, row1934, row1935, row1936, row1937]
theorem indices113 : rows113.map Row.index = [1930, 1931, 1932, 1933, 1934, 1935, 1936, 1937] := by rfl
theorem bound113 : entries113.map CheckedRow.row = rows113 := by rfl
theorem choices_and_113 : choices rows113 167837696#32 (-1) = [] := by rfl
theorem choices_orr_113 : choices rows113 704708608#32 (-1) = [] := by rfl
theorem choices_eor_113 : choices rows113 1241579520#32 (-1) = [] := by rfl
theorem choices_ret_113 : choices rows113 3596551104#32 (-1) = [] := by rfl

end Oak.ArmDecoderClassification.Data
