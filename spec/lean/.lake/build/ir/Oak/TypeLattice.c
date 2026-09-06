// Lean compiler output
// Module: Oak.TypeLattice
// Imports: public import Init public meta import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Oak"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "TypeLattice"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "term_≤ₜ_"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 123, 71, 158, 222, 143, 182, 48)}};
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3_value_aux_0),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(119, 120, 155, 211, 206, 1, 105, 139)}};
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3_value_aux_1),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(182, 100, 137, 47, 159, 250, 15, 233)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__5_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = " ≤ₜ "};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__6_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__6_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__7 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__7_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__9_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__9_value),((lean_object*)(((size_t)(51) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__5_value),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__7_value),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__11_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3_value),((lean_object*)(((size_t)(50) << 1) | 1)),((lean_object*)(((size_t)(51) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__11_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__12 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__12_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c__ = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__12_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__2_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__3_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4_value_aux_0),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4_value_aux_1),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4_value_aux_2),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Subtype"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__5_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__6;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(30, 108, 3, 75, 185, 102, 103, 84)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__7 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__7_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(238, 123, 71, 158, 222, 143, 182, 48)}};
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__8_value_aux_0),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(119, 120, 155, 211, 206, 1, 105, 139)}};
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__8_value_aux_1),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(50, 24, 176, 108, 115, 53, 69, 216)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__9_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__7_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__11_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__9_value),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__11_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__12 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__12_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__13_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__14 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__14_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___closed__1_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__6(void){
_start:
{
lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_40_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__5));
v___x_41_ = l_String_toRawSubstring_x27(v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1(lean_object* v_x_62_, lean_object* v_a_63_, lean_object* v_a_64_){
_start:
{
lean_object* v___x_65_; uint8_t v___x_66_; 
v___x_65_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3));
lean_inc(v_x_62_);
v___x_66_ = l_Lean_Syntax_isOfKind(v_x_62_, v___x_65_);
if (v___x_66_ == 0)
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_dec(v_x_62_);
v___x_67_ = lean_box(1);
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
lean_ctor_set(v___x_68_, 1, v_a_64_);
return v___x_68_;
}
else
{
lean_object* v_quotContext_69_; lean_object* v_currMacroScope_70_; lean_object* v_ref_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; uint8_t v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v_quotContext_69_ = lean_ctor_get(v_a_63_, 1);
v_currMacroScope_70_ = lean_ctor_get(v_a_63_, 2);
v_ref_71_ = lean_ctor_get(v_a_63_, 5);
v___x_72_ = lean_unsigned_to_nat(0u);
v___x_73_ = l_Lean_Syntax_getArg(v_x_62_, v___x_72_);
v___x_74_ = lean_unsigned_to_nat(2u);
v___x_75_ = l_Lean_Syntax_getArg(v_x_62_, v___x_74_);
lean_dec(v_x_62_);
v___x_76_ = 0;
v___x_77_ = l_Lean_SourceInfo_fromRef(v_ref_71_, v___x_76_);
v___x_78_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4));
v___x_79_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__6, &lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__6_once, _init_lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__6);
v___x_80_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__7));
lean_inc(v_currMacroScope_70_);
lean_inc(v_quotContext_69_);
v___x_81_ = l_Lean_addMacroScope(v_quotContext_69_, v___x_80_, v_currMacroScope_70_);
v___x_82_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__12));
lean_inc_n(v___x_77_, 2);
v___x_83_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_83_, 0, v___x_77_);
lean_ctor_set(v___x_83_, 1, v___x_79_);
lean_ctor_set(v___x_83_, 2, v___x_81_);
lean_ctor_set(v___x_83_, 3, v___x_82_);
v___x_84_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__14));
v___x_85_ = l_Lean_Syntax_node2(v___x_77_, v___x_84_, v___x_73_, v___x_75_);
v___x_86_ = l_Lean_Syntax_node2(v___x_77_, v___x_78_, v___x_83_, v___x_85_);
v___x_87_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v_a_64_);
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___boxed(lean_object* v_x_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v_res_91_; 
v_res_91_ = lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1(v_x_88_, v_a_89_, v_a_90_);
lean_dec_ref(v_a_89_);
return v_res_91_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1(lean_object* v_x_95_, lean_object* v_a_96_, lean_object* v_a_97_){
_start:
{
lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_98_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______macroRules__Oak__TypeLattice__term___u2264_u209c____1___closed__4));
lean_inc(v_x_95_);
v___x_99_ = l_Lean_Syntax_isOfKind(v_x_95_, v___x_98_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; 
lean_dec(v_x_95_);
v___x_100_ = lean_box(0);
v___x_101_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_a_97_);
return v___x_101_;
}
else
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v___x_102_ = lean_unsigned_to_nat(0u);
v___x_103_ = l_Lean_Syntax_getArg(v_x_95_, v___x_102_);
v___x_104_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___closed__1));
lean_inc(v___x_103_);
v___x_105_ = l_Lean_Syntax_isOfKind(v___x_103_, v___x_104_);
if (v___x_105_ == 0)
{
lean_object* v___x_106_; lean_object* v___x_107_; 
lean_dec(v___x_103_);
lean_dec(v_x_95_);
v___x_106_ = lean_box(0);
v___x_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v_a_97_);
return v___x_107_;
}
else
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; uint8_t v___x_111_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = l_Lean_Syntax_getArg(v_x_95_, v___x_108_);
lean_dec(v_x_95_);
v___x_110_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_109_);
v___x_111_ = l_Lean_Syntax_matchesNull(v___x_109_, v___x_110_);
if (v___x_111_ == 0)
{
lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v___x_109_);
lean_dec(v___x_103_);
v___x_112_ = lean_box(0);
v___x_113_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v_a_97_);
return v___x_113_;
}
else
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v_ref_116_; uint8_t v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_114_ = l_Lean_Syntax_getArg(v___x_109_, v___x_102_);
v___x_115_ = l_Lean_Syntax_getArg(v___x_109_, v___x_108_);
lean_dec(v___x_109_);
v_ref_116_ = l_Lean_replaceRef(v___x_103_, v_a_96_);
lean_dec(v___x_103_);
v___x_117_ = 0;
v___x_118_ = l_Lean_SourceInfo_fromRef(v_ref_116_, v___x_117_);
lean_dec(v_ref_116_);
v___x_119_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__3));
v___x_120_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeLattice_term___u2264_u209c___00__closed__6));
lean_inc(v___x_118_);
v___x_121_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_118_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = l_Lean_Syntax_node3(v___x_118_, v___x_119_, v___x_114_, v___x_121_, v___x_115_);
v___x_123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
lean_ctor_set(v___x_123_, 1, v_a_97_);
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1___boxed(lean_object* v_x_124_, lean_object* v_a_125_, lean_object* v_a_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = lp_oak_x2dspec_Oak_TypeLattice___aux__Oak__TypeLattice______unexpand__Oak__TypeLattice__Subtype__1(v_x_124_, v_a_125_, v_a_126_);
lean_dec(v_a_125_);
return v_res_127_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_TypeLattice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
