// Lean compiler output
// Module: Oak.GeneralizationSafety
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
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "mutableAuthority"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__3_value),((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__9_value;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "uniqueAuthority"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__11_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__12;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "regionBound"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__13_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__13_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__14 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__14_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__15;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "externalAuthority"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__16 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__16_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__16_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__17 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__17_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__18;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "effectfulCapture"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__19 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__19_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__19_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__20 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__20_value;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unsafeAssumption"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__21 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__21_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__21_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__22 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__22_value;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "unknownAuthority"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__23 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__23_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__23_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__24 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__24_value;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__25 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__25_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__26;
static lean_once_cell_t lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__27;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__28 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__28_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__25_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__29 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__29_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts___closed__0_value;
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inferredType"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__2_value),((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__3_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__4;
static const lean_string_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "generalized"};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding = (const lean_object*)&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_decideGeneralization(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_decideGeneralization___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
uint8_t v_mutableAuthority_3_; uint8_t v_uniqueAuthority_4_; uint8_t v_regionBound_5_; uint8_t v_externalAuthority_6_; uint8_t v_effectfulCapture_7_; uint8_t v_unsafeAssumption_8_; uint8_t v_unknownAuthority_9_; uint8_t v_mutableAuthority_10_; uint8_t v_uniqueAuthority_11_; uint8_t v_regionBound_12_; uint8_t v_externalAuthority_13_; uint8_t v_effectfulCapture_14_; uint8_t v_unsafeAssumption_15_; uint8_t v_unknownAuthority_16_; 
v_mutableAuthority_3_ = lean_ctor_get_uint8(v_x_1_, 0);
v_uniqueAuthority_4_ = lean_ctor_get_uint8(v_x_1_, 1);
v_regionBound_5_ = lean_ctor_get_uint8(v_x_1_, 2);
v_externalAuthority_6_ = lean_ctor_get_uint8(v_x_1_, 3);
v_effectfulCapture_7_ = lean_ctor_get_uint8(v_x_1_, 4);
v_unsafeAssumption_8_ = lean_ctor_get_uint8(v_x_1_, 5);
v_unknownAuthority_9_ = lean_ctor_get_uint8(v_x_1_, 6);
v_mutableAuthority_10_ = lean_ctor_get_uint8(v_x_2_, 0);
v_uniqueAuthority_11_ = lean_ctor_get_uint8(v_x_2_, 1);
v_regionBound_12_ = lean_ctor_get_uint8(v_x_2_, 2);
v_externalAuthority_13_ = lean_ctor_get_uint8(v_x_2_, 3);
v_effectfulCapture_14_ = lean_ctor_get_uint8(v_x_2_, 4);
v_unsafeAssumption_15_ = lean_ctor_get_uint8(v_x_2_, 5);
v_unknownAuthority_16_ = lean_ctor_get_uint8(v_x_2_, 6);
if (v_mutableAuthority_3_ == 0)
{
if (v_mutableAuthority_10_ == 0)
{
goto v___jp_23_;
}
else
{
return v_mutableAuthority_3_;
}
}
else
{
if (v_mutableAuthority_10_ == 0)
{
return v_mutableAuthority_10_;
}
else
{
goto v___jp_23_;
}
}
v___jp_17_:
{
if (v_unknownAuthority_9_ == 0)
{
if (v_unknownAuthority_16_ == 0)
{
uint8_t v___x_18_; 
v___x_18_ = 1;
return v___x_18_;
}
else
{
return v_unknownAuthority_9_;
}
}
else
{
return v_unknownAuthority_16_;
}
}
v___jp_19_:
{
if (v_unsafeAssumption_8_ == 0)
{
if (v_unsafeAssumption_15_ == 0)
{
goto v___jp_17_;
}
else
{
return v_unsafeAssumption_8_;
}
}
else
{
if (v_unsafeAssumption_15_ == 0)
{
return v_unsafeAssumption_15_;
}
else
{
goto v___jp_17_;
}
}
}
v___jp_20_:
{
if (v_effectfulCapture_7_ == 0)
{
if (v_effectfulCapture_14_ == 0)
{
goto v___jp_19_;
}
else
{
return v_effectfulCapture_7_;
}
}
else
{
if (v_effectfulCapture_14_ == 0)
{
return v_effectfulCapture_14_;
}
else
{
goto v___jp_19_;
}
}
}
v___jp_21_:
{
if (v_externalAuthority_6_ == 0)
{
if (v_externalAuthority_13_ == 0)
{
goto v___jp_20_;
}
else
{
return v_externalAuthority_6_;
}
}
else
{
if (v_externalAuthority_13_ == 0)
{
return v_externalAuthority_13_;
}
else
{
goto v___jp_20_;
}
}
}
v___jp_22_:
{
if (v_regionBound_5_ == 0)
{
if (v_regionBound_12_ == 0)
{
goto v___jp_21_;
}
else
{
return v_regionBound_5_;
}
}
else
{
if (v_regionBound_12_ == 0)
{
return v_regionBound_12_;
}
else
{
goto v___jp_21_;
}
}
}
v___jp_23_:
{
if (v_uniqueAuthority_4_ == 0)
{
if (v_uniqueAuthority_11_ == 0)
{
goto v___jp_22_;
}
else
{
return v_uniqueAuthority_4_;
}
}
else
{
if (v_uniqueAuthority_11_ == 0)
{
return v_uniqueAuthority_11_;
}
else
{
goto v___jp_22_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts_decEq___boxed(lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
uint8_t v_res_26_; lean_object* v_r_27_; 
v_res_26_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts_decEq(v_x_24_, v_x_25_);
lean_dec_ref(v_x_25_);
lean_dec_ref(v_x_24_);
v_r_27_ = lean_box(v_res_26_);
return v_r_27_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts(lean_object* v_x_28_, lean_object* v_x_29_){
_start:
{
uint8_t v___x_30_; 
v___x_30_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts_decEq(v_x_28_, v_x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts___boxed(lean_object* v_x_31_, lean_object* v_x_32_){
_start:
{
uint8_t v_res_33_; lean_object* v_r_34_; 
v_res_33_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqFacts(v_x_31_, v_x_32_);
lean_dec_ref(v_x_32_);
lean_dec_ref(v_x_31_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_48_ = lean_unsigned_to_nat(20u);
v___x_49_ = lean_nat_to_int(v___x_48_);
return v___x_49_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = lean_unsigned_to_nat(19u);
v___x_57_ = lean_nat_to_int(v___x_56_);
return v___x_57_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(15u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_unsigned_to_nat(21u);
v___x_67_ = lean_nat_to_int(v___x_66_);
return v___x_67_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__26(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__0));
v___x_79_ = lean_string_length(v___x_78_);
return v___x_79_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__27(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_obj_once(&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__26, &lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__26_once, _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__26);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg(lean_object* v_x_86_){
_start:
{
uint8_t v_mutableAuthority_87_; uint8_t v_uniqueAuthority_88_; uint8_t v_regionBound_89_; uint8_t v_externalAuthority_90_; uint8_t v_effectfulCapture_91_; uint8_t v_unsafeAssumption_92_; uint8_t v_unknownAuthority_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_mutableAuthority_87_ = lean_ctor_get_uint8(v_x_86_, 0);
v_uniqueAuthority_88_ = lean_ctor_get_uint8(v_x_86_, 1);
v_regionBound_89_ = lean_ctor_get_uint8(v_x_86_, 2);
v_externalAuthority_90_ = lean_ctor_get_uint8(v_x_86_, 3);
v_effectfulCapture_91_ = lean_ctor_get_uint8(v_x_86_, 4);
v_unsafeAssumption_92_ = lean_ctor_get_uint8(v_x_86_, 5);
v_unknownAuthority_93_ = lean_ctor_get_uint8(v_x_86_, 6);
v___x_94_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__5));
v___x_95_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__6));
v___x_96_ = lean_obj_once(&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__7);
v___x_97_ = l_Bool_repr___redArg(v_mutableAuthority_87_);
v___x_98_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = 0;
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_99_);
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_95_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__9));
v___x_103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_101_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = lean_box(1);
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__11));
v___x_107_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_105_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
lean_ctor_set(v___x_108_, 1, v___x_94_);
v___x_109_ = lean_obj_once(&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__12, &lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__12_once, _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__12);
v___x_110_ = l_Bool_repr___redArg(v_uniqueAuthority_88_);
v___x_111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_111_, 0, v___x_109_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_112_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_112_, sizeof(void*)*1, v___x_99_);
v___x_113_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_108_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v___x_102_);
v___x_115_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_114_);
lean_ctor_set(v___x_115_, 1, v___x_104_);
v___x_116_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__14));
v___x_117_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set(v___x_117_, 1, v___x_116_);
v___x_118_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_94_);
v___x_119_ = lean_obj_once(&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__15);
v___x_120_ = l_Bool_repr___redArg(v_regionBound_89_);
v___x_121_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_121_, 0, v___x_119_);
lean_ctor_set(v___x_121_, 1, v___x_120_);
v___x_122_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_122_, 0, v___x_121_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*1, v___x_99_);
v___x_123_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_123_, 0, v___x_118_);
lean_ctor_set(v___x_123_, 1, v___x_122_);
v___x_124_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_124_, 0, v___x_123_);
lean_ctor_set(v___x_124_, 1, v___x_102_);
v___x_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_104_);
v___x_126_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__17));
v___x_127_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_128_, 0, v___x_127_);
lean_ctor_set(v___x_128_, 1, v___x_94_);
v___x_129_ = lean_obj_once(&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__18, &lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__18_once, _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__18);
v___x_130_ = l_Bool_repr___redArg(v_externalAuthority_90_);
v___x_131_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_131_, 0, v___x_129_);
lean_ctor_set(v___x_131_, 1, v___x_130_);
v___x_132_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set_uint8(v___x_132_, sizeof(void*)*1, v___x_99_);
v___x_133_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_128_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
lean_ctor_set(v___x_134_, 1, v___x_102_);
v___x_135_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v___x_104_);
v___x_136_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__20));
v___x_137_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_137_, 0, v___x_135_);
lean_ctor_set(v___x_137_, 1, v___x_136_);
v___x_138_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_94_);
v___x_139_ = l_Bool_repr___redArg(v_effectfulCapture_91_);
v___x_140_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_140_, 0, v___x_96_);
lean_ctor_set(v___x_140_, 1, v___x_139_);
v___x_141_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set_uint8(v___x_141_, sizeof(void*)*1, v___x_99_);
v___x_142_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_142_, 0, v___x_138_);
lean_ctor_set(v___x_142_, 1, v___x_141_);
v___x_143_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_143_, 0, v___x_142_);
lean_ctor_set(v___x_143_, 1, v___x_102_);
v___x_144_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_144_, 0, v___x_143_);
lean_ctor_set(v___x_144_, 1, v___x_104_);
v___x_145_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__22));
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
lean_ctor_set(v___x_147_, 1, v___x_94_);
v___x_148_ = l_Bool_repr___redArg(v_unsafeAssumption_92_);
v___x_149_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_96_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_150_, 0, v___x_149_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*1, v___x_99_);
v___x_151_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_147_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_102_);
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_152_);
lean_ctor_set(v___x_153_, 1, v___x_104_);
v___x_154_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__24));
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_153_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_156_, 0, v___x_155_);
lean_ctor_set(v___x_156_, 1, v___x_94_);
v___x_157_ = l_Bool_repr___redArg(v_unknownAuthority_93_);
v___x_158_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_158_, 0, v___x_96_);
lean_ctor_set(v___x_158_, 1, v___x_157_);
v___x_159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_99_);
v___x_160_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_160_, 0, v___x_156_);
lean_ctor_set(v___x_160_, 1, v___x_159_);
v___x_161_ = lean_obj_once(&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__27, &lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__27_once, _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__27);
v___x_162_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__28));
v___x_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_162_);
lean_ctor_set(v___x_163_, 1, v___x_160_);
v___x_164_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__29));
v___x_165_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_163_);
lean_ctor_set(v___x_165_, 1, v___x_164_);
v___x_166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_161_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_99_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___boxed(lean_object* v_x_168_){
_start:
{
lean_object* v_res_169_; 
v_res_169_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg(v_x_168_);
lean_dec_ref(v_x_168_);
return v_res_169_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr(lean_object* v_x_170_, lean_object* v_prec_171_){
_start:
{
lean_object* v___x_172_; 
v___x_172_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg(v_x_170_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___boxed(lean_object* v_x_173_, lean_object* v_prec_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr(v_x_173_, v_prec_174_);
lean_dec(v_prec_174_);
lean_dec_ref(v_x_173_);
return v_res_175_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding_decEq(lean_object* v_x_178_, lean_object* v_x_179_){
_start:
{
lean_object* v_inferredType_180_; uint8_t v_generalized_181_; lean_object* v_inferredType_182_; uint8_t v_generalized_183_; uint8_t v___x_184_; 
v_inferredType_180_ = lean_ctor_get(v_x_178_, 0);
v_generalized_181_ = lean_ctor_get_uint8(v_x_178_, sizeof(void*)*1);
v_inferredType_182_ = lean_ctor_get(v_x_179_, 0);
v_generalized_183_ = lean_ctor_get_uint8(v_x_179_, sizeof(void*)*1);
v___x_184_ = lean_nat_dec_eq(v_inferredType_180_, v_inferredType_182_);
if (v___x_184_ == 0)
{
return v___x_184_;
}
else
{
if (v_generalized_181_ == 0)
{
if (v_generalized_183_ == 0)
{
return v___x_184_;
}
else
{
return v_generalized_181_;
}
}
else
{
return v_generalized_183_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding_decEq___boxed(lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding_decEq(v_x_185_, v_x_186_);
lean_dec_ref(v_x_186_);
lean_dec_ref(v_x_185_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding_decEq(v_x_189_, v_x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding___boxed(lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instDecidableEqBinding(v_x_192_, v_x_193_);
lean_dec_ref(v_x_193_);
lean_dec_ref(v_x_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(16u);
v___x_206_ = lean_nat_to_int(v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg(lean_object* v_x_210_){
_start:
{
lean_object* v_inferredType_211_; uint8_t v_generalized_212_; lean_object* v___x_214_; uint8_t v_isShared_215_; uint8_t v_isSharedCheck_246_; 
v_inferredType_211_ = lean_ctor_get(v_x_210_, 0);
v_generalized_212_ = lean_ctor_get_uint8(v_x_210_, sizeof(void*)*1);
v_isSharedCheck_246_ = !lean_is_exclusive(v_x_210_);
if (v_isSharedCheck_246_ == 0)
{
v___x_214_ = v_x_210_;
v_isShared_215_ = v_isSharedCheck_246_;
goto v_resetjp_213_;
}
else
{
lean_inc(v_inferredType_211_);
lean_dec(v_x_210_);
v___x_214_ = lean_box(0);
v_isShared_215_ = v_isSharedCheck_246_;
goto v_resetjp_213_;
}
v_resetjp_213_:
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; lean_object* v___x_224_; 
v___x_216_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__5));
v___x_217_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__3));
v___x_218_ = lean_obj_once(&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__4, &lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__4_once, _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__4);
v___x_219_ = l_Nat_reprFast(v_inferredType_211_);
v___x_220_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_220_, 0, v___x_219_);
v___x_221_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_218_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = 0;
if (v_isShared_215_ == 0)
{
lean_ctor_set_tag(v___x_214_, 6);
lean_ctor_set(v___x_214_, 0, v___x_221_);
v___x_224_ = v___x_214_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v___x_221_);
v___x_224_ = v_reuseFailAlloc_245_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
lean_ctor_set_uint8(v___x_224_, sizeof(void*)*1, v___x_222_);
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_217_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__9));
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = lean_box(1);
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg___closed__6));
v___x_231_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_231_, 0, v___x_229_);
lean_ctor_set(v___x_231_, 1, v___x_230_);
v___x_232_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
lean_ctor_set(v___x_232_, 1, v___x_216_);
v___x_233_ = lean_obj_once(&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__15);
v___x_234_ = l_Bool_repr___redArg(v_generalized_212_);
v___x_235_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set_uint8(v___x_236_, sizeof(void*)*1, v___x_222_);
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_232_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v___x_238_ = lean_obj_once(&lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__27, &lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__27_once, _init_lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__27);
v___x_239_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__28));
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_237_);
v___x_241_ = ((lean_object*)(lp_oak_x2dspec_Oak_GeneralizationSafety_instReprFacts_repr___redArg___closed__29));
v___x_242_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_238_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*1, v___x_222_);
return v___x_244_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr(lean_object* v_x_247_, lean_object* v_prec_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___redArg(v_x_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr___boxed(lean_object* v_x_250_, lean_object* v_prec_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = lp_oak_x2dspec_Oak_GeneralizationSafety_instReprBinding_repr(v_x_250_, v_prec_251_);
lean_dec(v_prec_251_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_decideGeneralization(lean_object* v_inferredType_255_, lean_object* v_facts_256_){
_start:
{
uint8_t v_mutableAuthority_260_; 
v_mutableAuthority_260_ = lean_ctor_get_uint8(v_facts_256_, 0);
if (v_mutableAuthority_260_ == 0)
{
uint8_t v_uniqueAuthority_261_; 
v_uniqueAuthority_261_ = lean_ctor_get_uint8(v_facts_256_, 1);
if (v_uniqueAuthority_261_ == 0)
{
uint8_t v_regionBound_262_; 
v_regionBound_262_ = lean_ctor_get_uint8(v_facts_256_, 2);
if (v_regionBound_262_ == 0)
{
uint8_t v_externalAuthority_263_; 
v_externalAuthority_263_ = lean_ctor_get_uint8(v_facts_256_, 3);
if (v_externalAuthority_263_ == 0)
{
uint8_t v_effectfulCapture_264_; 
v_effectfulCapture_264_ = lean_ctor_get_uint8(v_facts_256_, 4);
if (v_effectfulCapture_264_ == 0)
{
uint8_t v_unsafeAssumption_265_; 
v_unsafeAssumption_265_ = lean_ctor_get_uint8(v_facts_256_, 5);
if (v_unsafeAssumption_265_ == 0)
{
uint8_t v_unknownAuthority_266_; 
v_unknownAuthority_266_ = lean_ctor_get_uint8(v_facts_256_, 6);
if (v_unknownAuthority_266_ == 0)
{
uint8_t v___x_267_; lean_object* v___x_268_; 
v___x_267_ = 1;
v___x_268_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_268_, 0, v_inferredType_255_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v___x_267_);
return v___x_268_;
}
else
{
goto v___jp_257_;
}
}
else
{
goto v___jp_257_;
}
}
else
{
goto v___jp_257_;
}
}
else
{
goto v___jp_257_;
}
}
else
{
goto v___jp_257_;
}
}
else
{
goto v___jp_257_;
}
}
else
{
goto v___jp_257_;
}
v___jp_257_:
{
uint8_t v___x_258_; lean_object* v___x_259_; 
v___x_258_ = 0;
v___x_259_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_259_, 0, v_inferredType_255_);
lean_ctor_set_uint8(v___x_259_, sizeof(void*)*1, v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GeneralizationSafety_decideGeneralization___boxed(lean_object* v_inferredType_269_, lean_object* v_facts_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = lp_oak_x2dspec_Oak_GeneralizationSafety_decideGeneralization(v_inferredType_269_, v_facts_270_);
lean_dec_ref(v_facts_270_);
return v_res_271_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_GeneralizationSafety(uint8_t builtin) {
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
