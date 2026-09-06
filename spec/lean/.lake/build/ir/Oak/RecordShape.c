// Lean compiler output
// Module: Oak.RecordShape
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__3_value),((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__9_value;
static const lean_string_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ty"};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__11_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__12;
static const lean_string_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__13_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__14;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__15;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__16 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__16_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__13_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__17 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_RecordShape_instReprField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField___closed__0_value;
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__4_value;
static lean_once_cell_t lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__5;
static lean_once_cell_t lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__6;
static const lean_ctor_object lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__7 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__7_value;
static const lean_ctor_object lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__8_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg(lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "fields"};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__2_value),((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__3_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__4;
static const lean_string_object lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "representation"};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__7;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord = (const lean_object*)&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord___closed__0_value;
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_name_3_; lean_object* v_ty_4_; lean_object* v_name_5_; lean_object* v_ty_6_; uint8_t v___x_7_; 
v_name_3_ = lean_ctor_get(v_x_1_, 0);
v_ty_4_ = lean_ctor_get(v_x_1_, 1);
v_name_5_ = lean_ctor_get(v_x_2_, 0);
v_ty_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_nat_dec_eq(v_name_3_, v_name_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_eq(v_ty_4_, v_ty_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField_decEq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField_decEq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField_decEq(v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(8u);
v___x_34_ = lean_nat_to_int(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(6u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__0));
v___x_45_ = lean_string_length(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__14, &lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__14_once, _init_lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__14);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg(lean_object* v_x_52_){
_start:
{
lean_object* v_name_53_; lean_object* v_ty_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_89_; 
v_name_53_ = lean_ctor_get(v_x_52_, 0);
v_ty_54_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_89_ == 0)
{
v___x_56_ = v_x_52_;
v_isShared_57_ = v_isSharedCheck_89_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_ty_54_);
lean_inc(v_name_53_);
lean_dec(v_x_52_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_89_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_58_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__5));
v___x_59_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__6));
v___x_60_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__7);
v___x_61_ = l_Nat_reprFast(v_name_53_);
v___x_62_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
if (v_isShared_57_ == 0)
{
lean_ctor_set_tag(v___x_56_, 4);
lean_ctor_set(v___x_56_, 1, v___x_62_);
lean_ctor_set(v___x_56_, 0, v___x_60_);
v___x_64_ = v___x_56_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___x_60_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_62_);
v___x_64_ = v_reuseFailAlloc_88_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_65_ = 0;
v___x_66_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set_uint8(v___x_66_, sizeof(void*)*1, v___x_65_);
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_59_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__9));
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_box(1);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__11));
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_58_);
v___x_75_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__12, &lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__12_once, _init_lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__12);
v___x_76_ = l_Nat_reprFast(v_ty_54_);
v___x_77_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
v___x_78_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_75_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set_uint8(v___x_79_, sizeof(void*)*1, v___x_65_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_74_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__15);
v___x_82_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__16));
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_80_);
v___x_84_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__17));
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_83_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_81_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*1, v___x_65_);
return v___x_87_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr(lean_object* v_x_90_, lean_object* v_prec_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg(v_x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___boxed(lean_object* v_x_93_, lean_object* v_prec_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_oak_x2dspec_Oak_RecordShape_instReprField_repr(v_x_93_, v_prec_94_);
lean_dec(v_prec_94_);
return v_res_95_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord_decEq(lean_object* v_x_98_, lean_object* v_x_99_){
_start:
{
lean_object* v_fields_100_; lean_object* v_representation_101_; lean_object* v_fields_102_; lean_object* v_representation_103_; lean_object* v___x_104_; uint8_t v___x_105_; 
v_fields_100_ = lean_ctor_get(v_x_98_, 0);
lean_inc(v_fields_100_);
v_representation_101_ = lean_ctor_get(v_x_98_, 1);
lean_inc(v_representation_101_);
lean_dec_ref(v_x_98_);
v_fields_102_ = lean_ctor_get(v_x_99_, 0);
lean_inc(v_fields_102_);
v_representation_103_ = lean_ctor_get(v_x_99_, 1);
lean_inc(v_representation_103_);
lean_dec_ref(v_x_99_);
v___x_104_ = lean_alloc_closure((void*)(lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField___boxed), 2, 0);
v___x_105_ = l_instDecidableEqList___redArg(v___x_104_, v_fields_100_, v_fields_102_);
if (v___x_105_ == 0)
{
lean_dec(v_representation_103_);
lean_dec(v_representation_101_);
return v___x_105_;
}
else
{
uint8_t v___x_106_; 
v___x_106_ = lean_nat_dec_eq(v_representation_101_, v_representation_103_);
lean_dec(v_representation_103_);
lean_dec(v_representation_101_);
return v___x_106_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord_decEq___boxed(lean_object* v_x_107_, lean_object* v_x_108_){
_start:
{
uint8_t v_res_109_; lean_object* v_r_110_; 
v_res_109_ = lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord_decEq(v_x_107_, v_x_108_);
v_r_110_ = lean_box(v_res_109_);
return v_r_110_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
uint8_t v___x_113_; 
v___x_113_ = lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord_decEq(v_x_111_, v_x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord___boxed(lean_object* v_x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v_res_116_; lean_object* v_r_117_; 
v_res_116_ = lp_oak_x2dspec_Oak_RecordShape_instDecidableEqSemanticRecord(v_x_114_, v_x_115_);
v_r_117_ = lean_box(v_res_116_);
return v_r_117_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_118_, lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
if (lean_obj_tag(v_x_120_) == 0)
{
lean_dec(v_x_118_);
return v_x_119_;
}
else
{
lean_object* v_head_121_; lean_object* v_tail_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_132_; 
v_head_121_ = lean_ctor_get(v_x_120_, 0);
v_tail_122_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_132_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_132_ == 0)
{
v___x_124_ = v_x_120_;
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_tail_122_);
lean_inc(v_head_121_);
lean_dec(v_x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_132_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_127_; 
lean_inc(v_x_118_);
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 5);
lean_ctor_set(v___x_124_, 1, v_x_118_);
lean_ctor_set(v___x_124_, 0, v_x_119_);
v___x_127_ = v___x_124_;
goto v_reusejp_126_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v_x_119_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v_x_118_);
v___x_127_ = v_reuseFailAlloc_131_;
goto v_reusejp_126_;
}
v_reusejp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg(v_head_121_);
v___x_129_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v___x_128_);
v_x_119_ = v___x_129_;
v_x_120_ = v_tail_122_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0_spec__0_spec__1(lean_object* v_x_133_, lean_object* v_x_134_, lean_object* v_x_135_){
_start:
{
if (lean_obj_tag(v_x_135_) == 0)
{
lean_dec(v_x_133_);
return v_x_134_;
}
else
{
lean_object* v_head_136_; lean_object* v_tail_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_147_; 
v_head_136_ = lean_ctor_get(v_x_135_, 0);
v_tail_137_ = lean_ctor_get(v_x_135_, 1);
v_isSharedCheck_147_ = !lean_is_exclusive(v_x_135_);
if (v_isSharedCheck_147_ == 0)
{
v___x_139_ = v_x_135_;
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_tail_137_);
lean_inc(v_head_136_);
lean_dec(v_x_135_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_147_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
lean_inc(v_x_133_);
if (v_isShared_140_ == 0)
{
lean_ctor_set_tag(v___x_139_, 5);
lean_ctor_set(v___x_139_, 1, v_x_133_);
lean_ctor_set(v___x_139_, 0, v_x_134_);
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_x_134_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v_x_133_);
v___x_142_ = v_reuseFailAlloc_146_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_143_ = lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg(v_head_136_);
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_142_);
lean_ctor_set(v___x_144_, 1, v___x_143_);
v___x_145_ = lp_oak_x2dspec_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0_spec__0_spec__1_spec__2(v_x_133_, v___x_144_, v_tail_137_);
return v___x_145_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0_spec__0(lean_object* v_x_148_, lean_object* v_x_149_){
_start:
{
if (lean_obj_tag(v_x_148_) == 0)
{
lean_object* v___x_150_; 
lean_dec(v_x_149_);
v___x_150_ = lean_box(0);
return v___x_150_;
}
else
{
lean_object* v_tail_151_; 
v_tail_151_ = lean_ctor_get(v_x_148_, 1);
if (lean_obj_tag(v_tail_151_) == 0)
{
lean_object* v_head_152_; lean_object* v___x_153_; 
lean_dec(v_x_149_);
v_head_152_ = lean_ctor_get(v_x_148_, 0);
lean_inc(v_head_152_);
lean_dec_ref_known(v_x_148_, 2);
v___x_153_ = lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg(v_head_152_);
return v___x_153_;
}
else
{
lean_object* v_head_154_; lean_object* v___x_155_; lean_object* v___x_156_; 
lean_inc(v_tail_151_);
v_head_154_ = lean_ctor_get(v_x_148_, 0);
lean_inc(v_head_154_);
lean_dec_ref_known(v_x_148_, 2);
v___x_155_ = lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg(v_head_154_);
v___x_156_ = lp_oak_x2dspec_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0_spec__0_spec__1(v_x_149_, v___x_155_, v_tail_151_);
return v___x_156_;
}
}
}
}
static lean_object* _init_lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__2));
v___x_166_ = lean_string_length(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_obj_once(&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__5, &lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__5_once, _init_lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__5);
v___x_168_ = lean_nat_to_int(v___x_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg(lean_object* v_a_173_){
_start:
{
if (lean_obj_tag(v_a_173_) == 0)
{
lean_object* v___x_174_; 
v___x_174_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__1));
return v___x_174_;
}
else
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; lean_object* v___x_184_; 
v___x_175_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__3));
v___x_176_ = lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0_spec__0(v_a_173_, v___x_175_);
v___x_177_ = lean_obj_once(&lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__6, &lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__6_once, _init_lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__6);
v___x_178_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__7));
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___x_176_);
v___x_180_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg___closed__8));
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_179_);
lean_ctor_set(v___x_181_, 1, v___x_180_);
v___x_182_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_177_);
lean_ctor_set(v___x_182_, 1, v___x_181_);
v___x_183_ = 0;
v___x_184_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set_uint8(v___x_184_, sizeof(void*)*1, v___x_183_);
return v___x_184_;
}
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = lean_unsigned_to_nat(10u);
v___x_195_ = lean_nat_to_int(v___x_194_);
return v___x_195_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(18u);
v___x_200_ = lean_nat_to_int(v___x_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg(lean_object* v_x_201_){
_start:
{
lean_object* v_fields_202_; lean_object* v_representation_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_237_; 
v_fields_202_ = lean_ctor_get(v_x_201_, 0);
v_representation_203_ = lean_ctor_get(v_x_201_, 1);
v_isSharedCheck_237_ = !lean_is_exclusive(v_x_201_);
if (v_isSharedCheck_237_ == 0)
{
v___x_205_ = v_x_201_;
v_isShared_206_ = v_isSharedCheck_237_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_representation_203_);
lean_inc(v_fields_202_);
lean_dec(v_x_201_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_237_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_207_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__5));
v___x_208_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__3));
v___x_209_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__4, &lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__4_once, _init_lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__4);
v___x_210_ = lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg(v_fields_202_);
if (v_isShared_206_ == 0)
{
lean_ctor_set_tag(v___x_205_, 4);
lean_ctor_set(v___x_205_, 1, v___x_210_);
lean_ctor_set(v___x_205_, 0, v___x_209_);
v___x_212_ = v___x_205_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v___x_209_);
lean_ctor_set(v_reuseFailAlloc_236_, 1, v___x_210_);
v___x_212_ = v_reuseFailAlloc_236_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
uint8_t v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v___x_213_ = 0;
v___x_214_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set_uint8(v___x_214_, sizeof(void*)*1, v___x_213_);
v___x_215_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_208_);
lean_ctor_set(v___x_215_, 1, v___x_214_);
v___x_216_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__9));
v___x_217_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
v___x_218_ = lean_box(1);
v___x_219_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__6));
v___x_221_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___x_207_);
v___x_223_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg___closed__7);
v___x_224_ = l_Nat_reprFast(v_representation_203_);
v___x_225_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_225_, 0, v___x_224_);
v___x_226_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_223_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_227_, 0, v___x_226_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1, v___x_213_);
v___x_228_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_222_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__15);
v___x_230_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__16));
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
lean_ctor_set(v___x_231_, 1, v___x_228_);
v___x_232_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordShape_instReprField_repr___redArg___closed__17));
v___x_233_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_231_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_229_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_235_, 0, v___x_234_);
lean_ctor_set_uint8(v___x_235_, sizeof(void*)*1, v___x_213_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr(lean_object* v_x_238_, lean_object* v_prec_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___redArg(v_x_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr___boxed(lean_object* v_x_241_, lean_object* v_prec_242_){
_start:
{
lean_object* v_res_243_; 
v_res_243_ = lp_oak_x2dspec_Oak_RecordShape_instReprSemanticRecord_repr(v_x_241_, v_prec_242_);
lean_dec(v_prec_242_);
return v_res_243_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0(lean_object* v_a_244_, lean_object* v_n_245_){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg(v_a_244_);
return v___x_246_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___boxed(lean_object* v_a_247_, lean_object* v_n_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0(v_a_247_, v_n_248_);
lean_dec(v_n_248_);
return v_res_249_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_RecordShape(uint8_t builtin) {
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
