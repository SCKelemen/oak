// Lean compiler output
// Module: Oak.Diagnostics
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_Severity_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSeverity(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSeverity___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Oak.Diagnostics.Severity.error"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Oak.Diagnostics.Severity.warning"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Oak.Diagnostics.Severity.information"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__5_value;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Oak.Diagnostics.Severity.hint"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__6_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__6_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__7 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__7_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity___closed__0_value;
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "source"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__3_value),((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__9_value;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "start"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__11_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__12;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "stop"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__13_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__13_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__14 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__14_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__15;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__16 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__16_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__17;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__18;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__19 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__19_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__16_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__20 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__20_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Diagnostics_instReprSpan___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan___closed__0_value;
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__1_value;
static const lean_string_object lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__4_value;
static lean_once_cell_t lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__5;
static lean_once_cell_t lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__6;
static const lean_ctor_object lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__7 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__7_value;
static const lean_ctor_object lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__8_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2___lam__0(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1___redArg(lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__2_value),((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "severity"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__5_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__6;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "title"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__7 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__7_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__7_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__8_value;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "primary"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__9_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__9_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__10_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__11;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "secondary"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__12 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__12_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__12_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__13_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__14;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "notes"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__15 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__15_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__15_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__16 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__16_value;
static const lean_string_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "help"};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__17 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__17_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__17_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__18 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__18_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic = (const lean_object*)&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_retitle(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_addSecondary(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_addNote(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_addHelp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorIdx(uint8_t v_x_1_){
_start:
{
switch(v_x_1_)
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
case 2:
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_x_boxed_7_; lean_object* v_res_8_; 
v_x_boxed_7_ = lean_unbox(v_x_6_);
v_res_8_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorIdx(v_x_boxed_7_);
return v_res_8_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_toCtorIdx(uint8_t v_x_9_){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorIdx(v_x_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_toCtorIdx___boxed(lean_object* v_x_11_){
_start:
{
uint8_t v_x_4__boxed_12_; lean_object* v_res_13_; 
v_x_4__boxed_12_ = lean_unbox(v_x_11_);
v_res_13_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_toCtorIdx(v_x_4__boxed_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim___redArg(lean_object* v_k_14_){
_start:
{
lean_inc(v_k_14_);
return v_k_14_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim___redArg___boxed(lean_object* v_k_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim___redArg(v_k_15_);
lean_dec(v_k_15_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, uint8_t v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_inc(v_k_21_);
return v_k_21_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim___boxed(lean_object* v_motive_22_, lean_object* v_ctorIdx_23_, lean_object* v_t_24_, lean_object* v_h_25_, lean_object* v_k_26_){
_start:
{
uint8_t v_t_boxed_27_; lean_object* v_res_28_; 
v_t_boxed_27_ = lean_unbox(v_t_24_);
v_res_28_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorElim(v_motive_22_, v_ctorIdx_23_, v_t_boxed_27_, v_h_25_, v_k_26_);
lean_dec(v_k_26_);
lean_dec(v_ctorIdx_23_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim___redArg(lean_object* v_error_29_){
_start:
{
lean_inc(v_error_29_);
return v_error_29_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim___redArg___boxed(lean_object* v_error_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim___redArg(v_error_30_);
lean_dec(v_error_30_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim(lean_object* v_motive_32_, uint8_t v_t_33_, lean_object* v_h_34_, lean_object* v_error_35_){
_start:
{
lean_inc(v_error_35_);
return v_error_35_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim___boxed(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_error_39_){
_start:
{
uint8_t v_t_boxed_40_; lean_object* v_res_41_; 
v_t_boxed_40_ = lean_unbox(v_t_37_);
v_res_41_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_error_elim(v_motive_36_, v_t_boxed_40_, v_h_38_, v_error_39_);
lean_dec(v_error_39_);
return v_res_41_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim___redArg(lean_object* v_warning_42_){
_start:
{
lean_inc(v_warning_42_);
return v_warning_42_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim___redArg___boxed(lean_object* v_warning_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim___redArg(v_warning_43_);
lean_dec(v_warning_43_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim(lean_object* v_motive_45_, uint8_t v_t_46_, lean_object* v_h_47_, lean_object* v_warning_48_){
_start:
{
lean_inc(v_warning_48_);
return v_warning_48_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim___boxed(lean_object* v_motive_49_, lean_object* v_t_50_, lean_object* v_h_51_, lean_object* v_warning_52_){
_start:
{
uint8_t v_t_boxed_53_; lean_object* v_res_54_; 
v_t_boxed_53_ = lean_unbox(v_t_50_);
v_res_54_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_warning_elim(v_motive_49_, v_t_boxed_53_, v_h_51_, v_warning_52_);
lean_dec(v_warning_52_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim___redArg(lean_object* v_information_55_){
_start:
{
lean_inc(v_information_55_);
return v_information_55_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim___redArg___boxed(lean_object* v_information_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim___redArg(v_information_56_);
lean_dec(v_information_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim(lean_object* v_motive_58_, uint8_t v_t_59_, lean_object* v_h_60_, lean_object* v_information_61_){
_start:
{
lean_inc(v_information_61_);
return v_information_61_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim___boxed(lean_object* v_motive_62_, lean_object* v_t_63_, lean_object* v_h_64_, lean_object* v_information_65_){
_start:
{
uint8_t v_t_boxed_66_; lean_object* v_res_67_; 
v_t_boxed_66_ = lean_unbox(v_t_63_);
v_res_67_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_information_elim(v_motive_62_, v_t_boxed_66_, v_h_64_, v_information_65_);
lean_dec(v_information_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim___redArg(lean_object* v_hint_68_){
_start:
{
lean_inc(v_hint_68_);
return v_hint_68_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim___redArg___boxed(lean_object* v_hint_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim___redArg(v_hint_69_);
lean_dec(v_hint_69_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim(lean_object* v_motive_71_, uint8_t v_t_72_, lean_object* v_h_73_, lean_object* v_hint_74_){
_start:
{
lean_inc(v_hint_74_);
return v_hint_74_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim___boxed(lean_object* v_motive_75_, lean_object* v_t_76_, lean_object* v_h_77_, lean_object* v_hint_78_){
_start:
{
uint8_t v_t_boxed_79_; lean_object* v_res_80_; 
v_t_boxed_79_ = lean_unbox(v_t_76_);
v_res_80_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_hint_elim(v_motive_75_, v_t_boxed_79_, v_h_77_, v_hint_78_);
lean_dec(v_hint_78_);
return v_res_80_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_Severity_ofNat(lean_object* v_n_81_){
_start:
{
lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_dec_le(v_n_81_, v___x_82_);
if (v___x_83_ == 0)
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = lean_unsigned_to_nat(2u);
v___x_85_ = lean_nat_dec_le(v_n_81_, v___x_84_);
if (v___x_85_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 3;
return v___x_86_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = 2;
return v___x_87_;
}
}
else
{
lean_object* v___x_88_; uint8_t v___x_89_; 
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_nat_dec_le(v_n_81_, v___x_88_);
if (v___x_89_ == 0)
{
uint8_t v___x_90_; 
v___x_90_ = 1;
return v___x_90_;
}
else
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_Severity_ofNat___boxed(lean_object* v_n_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_ofNat(v_n_92_);
lean_dec(v_n_92_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSeverity(uint8_t v_x_95_, uint8_t v_y_96_){
_start:
{
lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_97_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorIdx(v_x_95_);
v___x_98_ = lp_oak_x2dspec_Oak_Diagnostics_Severity_ctorIdx(v_y_96_);
v___x_99_ = lean_nat_dec_eq(v___x_97_, v___x_98_);
lean_dec(v___x_98_);
lean_dec(v___x_97_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSeverity___boxed(lean_object* v_x_100_, lean_object* v_y_101_){
_start:
{
uint8_t v_x_13__boxed_102_; uint8_t v_y_14__boxed_103_; uint8_t v_res_104_; lean_object* v_r_105_; 
v_x_13__boxed_102_ = lean_unbox(v_x_100_);
v_y_14__boxed_103_ = lean_unbox(v_y_101_);
v_res_104_ = lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSeverity(v_x_13__boxed_102_, v_y_14__boxed_103_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8(void){
_start:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_unsigned_to_nat(2u);
v___x_119_ = lean_nat_to_int(v___x_118_);
return v___x_119_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9(void){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1u);
v___x_121_ = lean_nat_to_int(v___x_120_);
return v___x_121_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr(uint8_t v_x_122_, lean_object* v_prec_123_){
_start:
{
lean_object* v___y_125_; lean_object* v___y_132_; lean_object* v___y_139_; lean_object* v___y_146_; 
switch(v_x_122_)
{
case 0:
{
lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1024u);
v___x_153_ = lean_nat_dec_le(v___x_152_, v_prec_123_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8, &lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8);
v___y_125_ = v___x_154_;
goto v___jp_124_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9, &lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9);
v___y_125_ = v___x_155_;
goto v___jp_124_;
}
}
case 1:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1024u);
v___x_157_ = lean_nat_dec_le(v___x_156_, v_prec_123_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; 
v___x_158_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8, &lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8);
v___y_132_ = v___x_158_;
goto v___jp_131_;
}
else
{
lean_object* v___x_159_; 
v___x_159_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9, &lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9);
v___y_132_ = v___x_159_;
goto v___jp_131_;
}
}
case 2:
{
lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(1024u);
v___x_161_ = lean_nat_dec_le(v___x_160_, v_prec_123_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8, &lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8);
v___y_139_ = v___x_162_;
goto v___jp_138_;
}
else
{
lean_object* v___x_163_; 
v___x_163_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9, &lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9);
v___y_139_ = v___x_163_;
goto v___jp_138_;
}
}
default: 
{
lean_object* v___x_164_; uint8_t v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(1024u);
v___x_165_ = lean_nat_dec_le(v___x_164_, v_prec_123_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
v___x_166_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8, &lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__8);
v___y_146_ = v___x_166_;
goto v___jp_145_;
}
else
{
lean_object* v___x_167_; 
v___x_167_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9, &lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__9);
v___y_146_ = v___x_167_;
goto v___jp_145_;
}
}
}
v___jp_124_:
{
lean_object* v___x_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_126_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__1));
lean_inc(v___y_125_);
v___x_127_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_127_, 0, v___y_125_);
lean_ctor_set(v___x_127_, 1, v___x_126_);
v___x_128_ = 0;
v___x_129_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set_uint8(v___x_129_, sizeof(void*)*1, v___x_128_);
v___x_130_ = l_Repr_addAppParen(v___x_129_, v_prec_123_);
return v___x_130_;
}
v___jp_131_:
{
lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_133_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__3));
lean_inc(v___y_132_);
v___x_134_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_134_, 0, v___y_132_);
lean_ctor_set(v___x_134_, 1, v___x_133_);
v___x_135_ = 0;
v___x_136_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_136_, 0, v___x_134_);
lean_ctor_set_uint8(v___x_136_, sizeof(void*)*1, v___x_135_);
v___x_137_ = l_Repr_addAppParen(v___x_136_, v_prec_123_);
return v___x_137_;
}
v___jp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_140_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__5));
lean_inc(v___y_139_);
v___x_141_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_141_, 0, v___y_139_);
lean_ctor_set(v___x_141_, 1, v___x_140_);
v___x_142_ = 0;
v___x_143_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_143_, 0, v___x_141_);
lean_ctor_set_uint8(v___x_143_, sizeof(void*)*1, v___x_142_);
v___x_144_ = l_Repr_addAppParen(v___x_143_, v_prec_123_);
return v___x_144_;
}
v___jp_145_:
{
lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_147_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___closed__7));
lean_inc(v___y_146_);
v___x_148_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_148_, 0, v___y_146_);
lean_ctor_set(v___x_148_, 1, v___x_147_);
v___x_149_ = 0;
v___x_150_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_150_, 0, v___x_148_);
lean_ctor_set_uint8(v___x_150_, sizeof(void*)*1, v___x_149_);
v___x_151_ = l_Repr_addAppParen(v___x_150_, v_prec_123_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr___boxed(lean_object* v_x_168_, lean_object* v_prec_169_){
_start:
{
uint8_t v_x_233__boxed_170_; lean_object* v_res_171_; 
v_x_233__boxed_170_ = lean_unbox(v_x_168_);
v_res_171_ = lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr(v_x_233__boxed_170_, v_prec_169_);
lean_dec(v_prec_169_);
return v_res_171_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan_decEq(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
lean_object* v_source_176_; lean_object* v_start_177_; lean_object* v_stop_178_; lean_object* v_source_179_; lean_object* v_start_180_; lean_object* v_stop_181_; uint8_t v___x_182_; 
v_source_176_ = lean_ctor_get(v_x_174_, 0);
v_start_177_ = lean_ctor_get(v_x_174_, 1);
v_stop_178_ = lean_ctor_get(v_x_174_, 2);
v_source_179_ = lean_ctor_get(v_x_175_, 0);
v_start_180_ = lean_ctor_get(v_x_175_, 1);
v_stop_181_ = lean_ctor_get(v_x_175_, 2);
v___x_182_ = lean_nat_dec_eq(v_source_176_, v_source_179_);
if (v___x_182_ == 0)
{
return v___x_182_;
}
else
{
uint8_t v___x_183_; 
v___x_183_ = lean_nat_dec_eq(v_start_177_, v_start_180_);
if (v___x_183_ == 0)
{
return v___x_183_;
}
else
{
uint8_t v___x_184_; 
v___x_184_ = lean_nat_dec_eq(v_stop_178_, v_stop_181_);
return v___x_184_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan_decEq___boxed(lean_object* v_x_185_, lean_object* v_x_186_){
_start:
{
uint8_t v_res_187_; lean_object* v_r_188_; 
v_res_187_ = lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan_decEq(v_x_185_, v_x_186_);
lean_dec_ref(v_x_186_);
lean_dec_ref(v_x_185_);
v_r_188_ = lean_box(v_res_187_);
return v_r_188_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
uint8_t v___x_191_; 
v___x_191_ = lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan_decEq(v_x_189_, v_x_190_);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan___boxed(lean_object* v_x_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan(v_x_192_, v_x_193_);
lean_dec_ref(v_x_193_);
lean_dec_ref(v_x_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_209_ = lean_unsigned_to_nat(10u);
v___x_210_ = lean_nat_to_int(v___x_209_);
return v___x_210_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(9u);
v___x_218_ = lean_nat_to_int(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_unsigned_to_nat(8u);
v___x_223_ = lean_nat_to_int(v___x_222_);
return v___x_223_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__0));
v___x_226_ = lean_string_length(v___x_225_);
return v___x_226_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_227_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__17, &lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__17_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__17);
v___x_228_ = lean_nat_to_int(v___x_227_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg(lean_object* v_x_233_){
_start:
{
lean_object* v_source_234_; lean_object* v_start_235_; lean_object* v_stop_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; 
v_source_234_ = lean_ctor_get(v_x_233_, 0);
lean_inc(v_source_234_);
v_start_235_ = lean_ctor_get(v_x_233_, 1);
lean_inc(v_start_235_);
v_stop_236_ = lean_ctor_get(v_x_233_, 2);
lean_inc(v_stop_236_);
lean_dec_ref(v_x_233_);
v___x_237_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__5));
v___x_238_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__6));
v___x_239_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__7);
v___x_240_ = l_Nat_reprFast(v_source_234_);
v___x_241_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
v___x_242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_239_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = 0;
v___x_244_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set_uint8(v___x_244_, sizeof(void*)*1, v___x_243_);
v___x_245_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_238_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__9));
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_box(1);
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__11));
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___x_237_);
v___x_253_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__12, &lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__12_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__12);
v___x_254_ = l_Nat_reprFast(v_start_235_);
v___x_255_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
v___x_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_253_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_257_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_257_, sizeof(void*)*1, v___x_243_);
v___x_258_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_252_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v___x_246_);
v___x_260_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_260_, 0, v___x_259_);
lean_ctor_set(v___x_260_, 1, v___x_248_);
v___x_261_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__14));
v___x_262_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_262_, 0, v___x_260_);
lean_ctor_set(v___x_262_, 1, v___x_261_);
v___x_263_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_237_);
v___x_264_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__15);
v___x_265_ = l_Nat_reprFast(v_stop_236_);
v___x_266_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_266_, 0, v___x_265_);
v___x_267_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_267_, 0, v___x_264_);
lean_ctor_set(v___x_267_, 1, v___x_266_);
v___x_268_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set_uint8(v___x_268_, sizeof(void*)*1, v___x_243_);
v___x_269_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_263_);
lean_ctor_set(v___x_269_, 1, v___x_268_);
v___x_270_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__18, &lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__18_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__18);
v___x_271_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__19));
v___x_272_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
lean_ctor_set(v___x_272_, 1, v___x_269_);
v___x_273_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__20));
v___x_274_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_272_);
lean_ctor_set(v___x_274_, 1, v___x_273_);
v___x_275_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_270_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___x_276_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_276_, 0, v___x_275_);
lean_ctor_set_uint8(v___x_276_, sizeof(void*)*1, v___x_243_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr(lean_object* v_x_277_, lean_object* v_prec_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg(v_x_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___boxed(lean_object* v_x_280_, lean_object* v_prec_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr(v_x_280_, v_prec_281_);
lean_dec(v_prec_281_);
return v_res_282_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic_decEq(lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_code_287_; uint8_t v_severity_288_; lean_object* v_title_289_; lean_object* v_primary_290_; lean_object* v_secondary_291_; lean_object* v_notes_292_; lean_object* v_help_293_; lean_object* v_code_294_; uint8_t v_severity_295_; lean_object* v_title_296_; lean_object* v_primary_297_; lean_object* v_secondary_298_; lean_object* v_notes_299_; lean_object* v_help_300_; uint8_t v___x_301_; 
v_code_287_ = lean_ctor_get(v_x_285_, 0);
lean_inc(v_code_287_);
v_severity_288_ = lean_ctor_get_uint8(v_x_285_, sizeof(void*)*6);
v_title_289_ = lean_ctor_get(v_x_285_, 1);
lean_inc(v_title_289_);
v_primary_290_ = lean_ctor_get(v_x_285_, 2);
lean_inc_ref(v_primary_290_);
v_secondary_291_ = lean_ctor_get(v_x_285_, 3);
lean_inc(v_secondary_291_);
v_notes_292_ = lean_ctor_get(v_x_285_, 4);
lean_inc(v_notes_292_);
v_help_293_ = lean_ctor_get(v_x_285_, 5);
lean_inc(v_help_293_);
lean_dec_ref(v_x_285_);
v_code_294_ = lean_ctor_get(v_x_286_, 0);
lean_inc(v_code_294_);
v_severity_295_ = lean_ctor_get_uint8(v_x_286_, sizeof(void*)*6);
v_title_296_ = lean_ctor_get(v_x_286_, 1);
lean_inc(v_title_296_);
v_primary_297_ = lean_ctor_get(v_x_286_, 2);
lean_inc_ref(v_primary_297_);
v_secondary_298_ = lean_ctor_get(v_x_286_, 3);
lean_inc(v_secondary_298_);
v_notes_299_ = lean_ctor_get(v_x_286_, 4);
lean_inc(v_notes_299_);
v_help_300_ = lean_ctor_get(v_x_286_, 5);
lean_inc(v_help_300_);
lean_dec_ref(v_x_286_);
v___x_301_ = lean_nat_dec_eq(v_code_287_, v_code_294_);
lean_dec(v_code_294_);
lean_dec(v_code_287_);
if (v___x_301_ == 0)
{
lean_dec(v_help_300_);
lean_dec(v_notes_299_);
lean_dec(v_secondary_298_);
lean_dec_ref(v_primary_297_);
lean_dec(v_title_296_);
lean_dec(v_help_293_);
lean_dec(v_notes_292_);
lean_dec(v_secondary_291_);
lean_dec_ref(v_primary_290_);
lean_dec(v_title_289_);
return v___x_301_;
}
else
{
uint8_t v___x_302_; 
v___x_302_ = lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSeverity(v_severity_288_, v_severity_295_);
if (v___x_302_ == 0)
{
lean_dec(v_help_300_);
lean_dec(v_notes_299_);
lean_dec(v_secondary_298_);
lean_dec_ref(v_primary_297_);
lean_dec(v_title_296_);
lean_dec(v_help_293_);
lean_dec(v_notes_292_);
lean_dec(v_secondary_291_);
lean_dec_ref(v_primary_290_);
lean_dec(v_title_289_);
return v___x_302_;
}
else
{
uint8_t v___x_303_; 
v___x_303_ = lean_nat_dec_eq(v_title_289_, v_title_296_);
lean_dec(v_title_296_);
lean_dec(v_title_289_);
if (v___x_303_ == 0)
{
lean_dec(v_help_300_);
lean_dec(v_notes_299_);
lean_dec(v_secondary_298_);
lean_dec_ref(v_primary_297_);
lean_dec(v_help_293_);
lean_dec(v_notes_292_);
lean_dec(v_secondary_291_);
lean_dec_ref(v_primary_290_);
return v___x_303_;
}
else
{
uint8_t v___x_304_; 
v___x_304_ = lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan_decEq(v_primary_290_, v_primary_297_);
lean_dec_ref(v_primary_297_);
lean_dec_ref(v_primary_290_);
if (v___x_304_ == 0)
{
lean_dec(v_help_300_);
lean_dec(v_notes_299_);
lean_dec(v_secondary_298_);
lean_dec(v_help_293_);
lean_dec(v_notes_292_);
lean_dec(v_secondary_291_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; uint8_t v___x_306_; 
v___x_305_ = lean_alloc_closure((void*)(lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqSpan___boxed), 2, 0);
v___x_306_ = l_instDecidableEqList___redArg(v___x_305_, v_secondary_291_, v_secondary_298_);
if (v___x_306_ == 0)
{
lean_dec(v_help_300_);
lean_dec(v_notes_299_);
lean_dec(v_help_293_);
lean_dec(v_notes_292_);
return v___x_306_;
}
else
{
lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
lean_inc_ref(v___x_307_);
v___x_308_ = l_instDecidableEqList___redArg(v___x_307_, v_notes_292_, v_notes_299_);
if (v___x_308_ == 0)
{
lean_dec_ref(v___x_307_);
lean_dec(v_help_300_);
lean_dec(v_help_293_);
return v___x_308_;
}
else
{
uint8_t v___x_309_; 
v___x_309_ = l_instDecidableEqList___redArg(v___x_307_, v_help_293_, v_help_300_);
return v___x_309_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic_decEq___boxed(lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
uint8_t v_res_312_; lean_object* v_r_313_; 
v_res_312_ = lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic_decEq(v_x_310_, v_x_311_);
v_r_313_ = lean_box(v_res_312_);
return v_r_313_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic(lean_object* v_x_314_, lean_object* v_x_315_){
_start:
{
uint8_t v___x_316_; 
v___x_316_ = lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic_decEq(v_x_314_, v_x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic___boxed(lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
uint8_t v_res_319_; lean_object* v_r_320_; 
v_res_319_ = lp_oak_x2dspec_Oak_Diagnostics_instDecidableEqDiagnostic(v_x_317_, v_x_318_);
v_r_320_ = lean_box(v_res_319_);
return v_r_320_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_dec(v_x_321_);
return v_x_322_;
}
else
{
lean_object* v_head_324_; lean_object* v_tail_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_335_; 
v_head_324_ = lean_ctor_get(v_x_323_, 0);
v_tail_325_ = lean_ctor_get(v_x_323_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_323_);
if (v_isSharedCheck_335_ == 0)
{
v___x_327_ = v_x_323_;
v_isShared_328_ = v_isSharedCheck_335_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_tail_325_);
lean_inc(v_head_324_);
lean_dec(v_x_323_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_335_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
lean_inc(v_x_321_);
if (v_isShared_328_ == 0)
{
lean_ctor_set_tag(v___x_327_, 5);
lean_ctor_set(v___x_327_, 1, v_x_321_);
lean_ctor_set(v___x_327_, 0, v_x_322_);
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v_x_322_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v_x_321_);
v___x_330_ = v_reuseFailAlloc_334_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg(v_head_324_);
v___x_332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v_x_322_ = v___x_332_;
v_x_323_ = v_tail_325_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0_spec__0_spec__1(lean_object* v_x_336_, lean_object* v_x_337_, lean_object* v_x_338_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_dec(v_x_336_);
return v_x_337_;
}
else
{
lean_object* v_head_339_; lean_object* v_tail_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_350_; 
v_head_339_ = lean_ctor_get(v_x_338_, 0);
v_tail_340_ = lean_ctor_get(v_x_338_, 1);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_350_ == 0)
{
v___x_342_ = v_x_338_;
v_isShared_343_ = v_isSharedCheck_350_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_tail_340_);
lean_inc(v_head_339_);
lean_dec(v_x_338_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_350_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
lean_object* v___x_345_; 
lean_inc(v_x_336_);
if (v_isShared_343_ == 0)
{
lean_ctor_set_tag(v___x_342_, 5);
lean_ctor_set(v___x_342_, 1, v_x_336_);
lean_ctor_set(v___x_342_, 0, v_x_337_);
v___x_345_ = v___x_342_;
goto v_reusejp_344_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_x_337_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_x_336_);
v___x_345_ = v_reuseFailAlloc_349_;
goto v_reusejp_344_;
}
v_reusejp_344_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; 
v___x_346_ = lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg(v_head_339_);
v___x_347_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_347_, 0, v___x_345_);
lean_ctor_set(v___x_347_, 1, v___x_346_);
v___x_348_ = lp_oak_x2dspec_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0_spec__0_spec__1_spec__3(v_x_336_, v___x_347_, v_tail_340_);
return v___x_348_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0_spec__0(lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
if (lean_obj_tag(v_x_351_) == 0)
{
lean_object* v___x_353_; 
lean_dec(v_x_352_);
v___x_353_ = lean_box(0);
return v___x_353_;
}
else
{
lean_object* v_tail_354_; 
v_tail_354_ = lean_ctor_get(v_x_351_, 1);
if (lean_obj_tag(v_tail_354_) == 0)
{
lean_object* v_head_355_; lean_object* v___x_356_; 
lean_dec(v_x_352_);
v_head_355_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_head_355_);
lean_dec_ref_known(v_x_351_, 2);
v___x_356_ = lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg(v_head_355_);
return v___x_356_;
}
else
{
lean_object* v_head_357_; lean_object* v___x_358_; lean_object* v___x_359_; 
lean_inc(v_tail_354_);
v_head_357_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_head_357_);
lean_dec_ref_known(v_x_351_, 2);
v___x_358_ = lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg(v_head_357_);
v___x_359_ = lp_oak_x2dspec_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0_spec__0_spec__1(v_x_352_, v___x_358_, v_tail_354_);
return v___x_359_;
}
}
}
}
static lean_object* _init_lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_368_; lean_object* v___x_369_; 
v___x_368_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__2));
v___x_369_ = lean_string_length(v___x_368_);
return v___x_369_;
}
}
static lean_object* _init_lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = lean_obj_once(&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__5, &lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__5_once, _init_lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__5);
v___x_371_ = lean_nat_to_int(v___x_370_);
return v___x_371_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg(lean_object* v_a_376_){
_start:
{
if (lean_obj_tag(v_a_376_) == 0)
{
lean_object* v___x_377_; 
v___x_377_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__1));
return v___x_377_;
}
else
{
lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; uint8_t v___x_386_; lean_object* v___x_387_; 
v___x_378_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__3));
v___x_379_ = lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0_spec__0(v_a_376_, v___x_378_);
v___x_380_ = lean_obj_once(&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__6, &lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__6_once, _init_lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__6);
v___x_381_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__7));
v___x_382_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
lean_ctor_set(v___x_382_, 1, v___x_379_);
v___x_383_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__8));
v___x_384_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_384_, 0, v___x_382_);
lean_ctor_set(v___x_384_, 1, v___x_383_);
v___x_385_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_380_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = 0;
v___x_387_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_387_, 0, v___x_385_);
lean_ctor_set_uint8(v___x_387_, sizeof(void*)*1, v___x_386_);
return v___x_387_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2___lam__0(lean_object* v___y_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; 
v___x_389_ = l_Nat_reprFast(v___y_388_);
v___x_390_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_){
_start:
{
if (lean_obj_tag(v_x_393_) == 0)
{
lean_dec(v_x_391_);
return v_x_392_;
}
else
{
lean_object* v_head_394_; lean_object* v_tail_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_406_; 
v_head_394_ = lean_ctor_get(v_x_393_, 0);
v_tail_395_ = lean_ctor_get(v_x_393_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_393_);
if (v_isSharedCheck_406_ == 0)
{
v___x_397_ = v_x_393_;
v_isShared_398_ = v_isSharedCheck_406_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_tail_395_);
lean_inc(v_head_394_);
lean_dec(v_x_393_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_406_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
lean_inc(v_x_391_);
if (v_isShared_398_ == 0)
{
lean_ctor_set_tag(v___x_397_, 5);
lean_ctor_set(v___x_397_, 1, v_x_391_);
lean_ctor_set(v___x_397_, 0, v_x_392_);
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_x_392_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v_x_391_);
v___x_400_ = v_reuseFailAlloc_405_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
v___x_401_ = l_Nat_reprFast(v_head_394_);
v___x_402_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_402_, 0, v___x_401_);
v___x_403_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_403_, 0, v___x_400_);
lean_ctor_set(v___x_403_, 1, v___x_402_);
v_x_392_ = v___x_403_;
v_x_393_ = v_tail_395_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2_spec__4(lean_object* v_x_407_, lean_object* v_x_408_, lean_object* v_x_409_){
_start:
{
if (lean_obj_tag(v_x_409_) == 0)
{
lean_dec(v_x_407_);
return v_x_408_;
}
else
{
lean_object* v_head_410_; lean_object* v_tail_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_422_; 
v_head_410_ = lean_ctor_get(v_x_409_, 0);
v_tail_411_ = lean_ctor_get(v_x_409_, 1);
v_isSharedCheck_422_ = !lean_is_exclusive(v_x_409_);
if (v_isSharedCheck_422_ == 0)
{
v___x_413_ = v_x_409_;
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_tail_411_);
lean_inc(v_head_410_);
lean_dec(v_x_409_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_422_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_416_; 
lean_inc(v_x_407_);
if (v_isShared_414_ == 0)
{
lean_ctor_set_tag(v___x_413_, 5);
lean_ctor_set(v___x_413_, 1, v_x_407_);
lean_ctor_set(v___x_413_, 0, v_x_408_);
v___x_416_ = v___x_413_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_x_408_);
lean_ctor_set(v_reuseFailAlloc_421_, 1, v_x_407_);
v___x_416_ = v_reuseFailAlloc_421_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_417_ = l_Nat_reprFast(v_head_410_);
v___x_418_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_418_, 0, v___x_417_);
v___x_419_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_416_);
lean_ctor_set(v___x_419_, 1, v___x_418_);
v___x_420_ = lp_oak_x2dspec_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2_spec__4_spec__6(v_x_407_, v___x_419_, v_tail_411_);
return v___x_420_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2(lean_object* v_x_423_, lean_object* v_x_424_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v___x_425_; 
lean_dec(v_x_424_);
v___x_425_ = lean_box(0);
return v___x_425_;
}
else
{
lean_object* v_tail_426_; 
v_tail_426_ = lean_ctor_get(v_x_423_, 1);
if (lean_obj_tag(v_tail_426_) == 0)
{
lean_object* v_head_427_; lean_object* v___x_428_; 
lean_dec(v_x_424_);
v_head_427_ = lean_ctor_get(v_x_423_, 0);
lean_inc(v_head_427_);
lean_dec_ref_known(v_x_423_, 2);
v___x_428_ = lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2___lam__0(v_head_427_);
return v___x_428_;
}
else
{
lean_object* v_head_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
lean_inc(v_tail_426_);
v_head_429_ = lean_ctor_get(v_x_423_, 0);
lean_inc(v_head_429_);
lean_dec_ref_known(v_x_423_, 2);
v___x_430_ = lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2___lam__0(v_head_429_);
v___x_431_ = lp_oak_x2dspec_List_foldl___at___00Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2_spec__4(v_x_424_, v___x_430_, v_tail_426_);
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1___redArg(lean_object* v_a_432_){
_start:
{
if (lean_obj_tag(v_a_432_) == 0)
{
lean_object* v___x_433_; 
v___x_433_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__1));
return v___x_433_;
}
else
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_434_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__3));
v___x_435_ = lp_oak_x2dspec_Std_Format_joinSep___at___00List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1_spec__2(v_a_432_, v___x_434_);
v___x_436_ = lean_obj_once(&lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__6, &lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__6_once, _init_lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__6);
v___x_437_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__7));
v___x_438_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v___x_435_);
v___x_439_ = ((lean_object*)(lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg___closed__8));
v___x_440_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_440_, 0, v___x_438_);
lean_ctor_set(v___x_440_, 1, v___x_439_);
v___x_441_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_436_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v___x_442_ = l_Std_Format_fill(v___x_441_);
return v___x_442_;
}
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__6(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = lean_unsigned_to_nat(12u);
v___x_456_ = lean_nat_to_int(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__11(void){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(11u);
v___x_464_ = lean_nat_to_int(v___x_463_);
return v___x_464_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(13u);
v___x_469_ = lean_nat_to_int(v___x_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg(lean_object* v_x_476_){
_start:
{
lean_object* v_code_477_; uint8_t v_severity_478_; lean_object* v_title_479_; lean_object* v_primary_480_; lean_object* v_secondary_481_; lean_object* v_notes_482_; lean_object* v_help_483_; lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v_code_477_ = lean_ctor_get(v_x_476_, 0);
lean_inc(v_code_477_);
v_severity_478_ = lean_ctor_get_uint8(v_x_476_, sizeof(void*)*6);
v_title_479_ = lean_ctor_get(v_x_476_, 1);
lean_inc(v_title_479_);
v_primary_480_ = lean_ctor_get(v_x_476_, 2);
lean_inc_ref(v_primary_480_);
v_secondary_481_ = lean_ctor_get(v_x_476_, 3);
lean_inc(v_secondary_481_);
v_notes_482_ = lean_ctor_get(v_x_476_, 4);
lean_inc(v_notes_482_);
v_help_483_ = lean_ctor_get(v_x_476_, 5);
lean_inc(v_help_483_);
lean_dec_ref(v_x_476_);
v___x_484_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__5));
v___x_485_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__3));
v___x_486_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__15);
v___x_487_ = l_Nat_reprFast(v_code_477_);
v___x_488_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
v___x_489_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_486_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = 0;
v___x_491_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_491_, 0, v___x_489_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*1, v___x_490_);
v___x_492_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_492_, 0, v___x_485_);
lean_ctor_set(v___x_492_, 1, v___x_491_);
v___x_493_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__9));
v___x_494_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_492_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = lean_box(1);
v___x_496_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_494_);
lean_ctor_set(v___x_496_, 1, v___x_495_);
v___x_497_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__5));
v___x_498_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_498_, 0, v___x_496_);
lean_ctor_set(v___x_498_, 1, v___x_497_);
v___x_499_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v___x_484_);
v___x_500_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__6, &lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__6_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__6);
v___x_501_ = lean_unsigned_to_nat(0u);
v___x_502_ = lp_oak_x2dspec_Oak_Diagnostics_instReprSeverity_repr(v_severity_478_, v___x_501_);
v___x_503_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_500_);
lean_ctor_set(v___x_503_, 1, v___x_502_);
v___x_504_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_504_, 0, v___x_503_);
lean_ctor_set_uint8(v___x_504_, sizeof(void*)*1, v___x_490_);
v___x_505_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_499_);
lean_ctor_set(v___x_505_, 1, v___x_504_);
v___x_506_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
lean_ctor_set(v___x_506_, 1, v___x_493_);
v___x_507_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
lean_ctor_set(v___x_507_, 1, v___x_495_);
v___x_508_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__8));
v___x_509_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_509_, 0, v___x_507_);
lean_ctor_set(v___x_509_, 1, v___x_508_);
v___x_510_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_510_, 0, v___x_509_);
lean_ctor_set(v___x_510_, 1, v___x_484_);
v___x_511_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__12, &lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__12_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__12);
v___x_512_ = l_Nat_reprFast(v_title_479_);
v___x_513_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___x_514_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_511_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
v___x_515_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set_uint8(v___x_515_, sizeof(void*)*1, v___x_490_);
v___x_516_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_516_, 0, v___x_510_);
lean_ctor_set(v___x_516_, 1, v___x_515_);
v___x_517_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
lean_ctor_set(v___x_517_, 1, v___x_493_);
v___x_518_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
lean_ctor_set(v___x_518_, 1, v___x_495_);
v___x_519_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__10));
v___x_520_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_520_, 0, v___x_518_);
lean_ctor_set(v___x_520_, 1, v___x_519_);
v___x_521_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
lean_ctor_set(v___x_521_, 1, v___x_484_);
v___x_522_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__11, &lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__11_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__11);
v___x_523_ = lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg(v_primary_480_);
v___x_524_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_524_, 0, v___x_522_);
lean_ctor_set(v___x_524_, 1, v___x_523_);
v___x_525_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_525_, 0, v___x_524_);
lean_ctor_set_uint8(v___x_525_, sizeof(void*)*1, v___x_490_);
v___x_526_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_521_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_527_, 0, v___x_526_);
lean_ctor_set(v___x_527_, 1, v___x_493_);
v___x_528_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_527_);
lean_ctor_set(v___x_528_, 1, v___x_495_);
v___x_529_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__13));
v___x_530_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_530_, 0, v___x_528_);
lean_ctor_set(v___x_530_, 1, v___x_529_);
v___x_531_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_530_);
lean_ctor_set(v___x_531_, 1, v___x_484_);
v___x_532_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__14, &lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__14_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__14);
v___x_533_ = lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg(v_secondary_481_);
v___x_534_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_532_);
lean_ctor_set(v___x_534_, 1, v___x_533_);
v___x_535_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_535_, 0, v___x_534_);
lean_ctor_set_uint8(v___x_535_, sizeof(void*)*1, v___x_490_);
v___x_536_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_531_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v___x_493_);
v___x_538_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
lean_ctor_set(v___x_538_, 1, v___x_495_);
v___x_539_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__16));
v___x_540_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_538_);
lean_ctor_set(v___x_540_, 1, v___x_539_);
v___x_541_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
lean_ctor_set(v___x_541_, 1, v___x_484_);
v___x_542_ = lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1___redArg(v_notes_482_);
v___x_543_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_511_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_544_, 0, v___x_543_);
lean_ctor_set_uint8(v___x_544_, sizeof(void*)*1, v___x_490_);
v___x_545_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_545_, 0, v___x_541_);
lean_ctor_set(v___x_545_, 1, v___x_544_);
v___x_546_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
lean_ctor_set(v___x_546_, 1, v___x_493_);
v___x_547_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_546_);
lean_ctor_set(v___x_547_, 1, v___x_495_);
v___x_548_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg___closed__18));
v___x_549_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_549_, 0, v___x_547_);
lean_ctor_set(v___x_549_, 1, v___x_548_);
v___x_550_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_484_);
v___x_551_ = lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1___redArg(v_help_483_);
v___x_552_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_486_);
lean_ctor_set(v___x_552_, 1, v___x_551_);
v___x_553_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_553_, 0, v___x_552_);
lean_ctor_set_uint8(v___x_553_, sizeof(void*)*1, v___x_490_);
v___x_554_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_550_);
lean_ctor_set(v___x_554_, 1, v___x_553_);
v___x_555_ = lean_obj_once(&lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__18, &lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__18_once, _init_lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__18);
v___x_556_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__19));
v___x_557_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v___x_554_);
v___x_558_ = ((lean_object*)(lp_oak_x2dspec_Oak_Diagnostics_instReprSpan_repr___redArg___closed__20));
v___x_559_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_560_, 0, v___x_555_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
v___x_561_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_561_, 0, v___x_560_);
lean_ctor_set_uint8(v___x_561_, sizeof(void*)*1, v___x_490_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr(lean_object* v_x_562_, lean_object* v_prec_563_){
_start:
{
lean_object* v___x_564_; 
v___x_564_ = lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___redArg(v_x_562_);
return v___x_564_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr___boxed(lean_object* v_x_565_, lean_object* v_prec_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = lp_oak_x2dspec_Oak_Diagnostics_instReprDiagnostic_repr(v_x_565_, v_prec_566_);
lean_dec(v_prec_566_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0(lean_object* v_a_568_, lean_object* v_n_569_){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___redArg(v_a_568_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0___boxed(lean_object* v_a_571_, lean_object* v_n_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = lp_oak_x2dspec_List_repr___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__0(v_a_571_, v_n_572_);
lean_dec(v_n_572_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1(lean_object* v_a_574_, lean_object* v_n_575_){
_start:
{
lean_object* v___x_576_; 
v___x_576_ = lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1___redArg(v_a_574_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1___boxed(lean_object* v_a_577_, lean_object* v_n_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = lp_oak_x2dspec_List_repr_x27___at___00Oak_Diagnostics_instReprDiagnostic_repr_spec__1(v_a_577_, v_n_578_);
lean_dec(v_n_578_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_retitle(lean_object* v_d_582_, lean_object* v_title_583_){
_start:
{
lean_object* v_code_584_; uint8_t v_severity_585_; lean_object* v_primary_586_; lean_object* v_secondary_587_; lean_object* v_notes_588_; lean_object* v_help_589_; lean_object* v___x_591_; uint8_t v_isShared_592_; uint8_t v_isSharedCheck_596_; 
v_code_584_ = lean_ctor_get(v_d_582_, 0);
v_severity_585_ = lean_ctor_get_uint8(v_d_582_, sizeof(void*)*6);
v_primary_586_ = lean_ctor_get(v_d_582_, 2);
v_secondary_587_ = lean_ctor_get(v_d_582_, 3);
v_notes_588_ = lean_ctor_get(v_d_582_, 4);
v_help_589_ = lean_ctor_get(v_d_582_, 5);
v_isSharedCheck_596_ = !lean_is_exclusive(v_d_582_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_d_582_, 1);
lean_dec(v_unused_597_);
v___x_591_ = v_d_582_;
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
else
{
lean_inc(v_help_589_);
lean_inc(v_notes_588_);
lean_inc(v_secondary_587_);
lean_inc(v_primary_586_);
lean_inc(v_code_584_);
lean_dec(v_d_582_);
v___x_591_ = lean_box(0);
v_isShared_592_ = v_isSharedCheck_596_;
goto v_resetjp_590_;
}
v_resetjp_590_:
{
lean_object* v___x_594_; 
if (v_isShared_592_ == 0)
{
lean_ctor_set(v___x_591_, 1, v_title_583_);
v___x_594_ = v___x_591_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_code_584_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_title_583_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v_primary_586_);
lean_ctor_set(v_reuseFailAlloc_595_, 3, v_secondary_587_);
lean_ctor_set(v_reuseFailAlloc_595_, 4, v_notes_588_);
lean_ctor_set(v_reuseFailAlloc_595_, 5, v_help_589_);
lean_ctor_set_uint8(v_reuseFailAlloc_595_, sizeof(void*)*6, v_severity_585_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_addSecondary(lean_object* v_d_598_, lean_object* v_span_599_){
_start:
{
lean_object* v_code_600_; uint8_t v_severity_601_; lean_object* v_title_602_; lean_object* v_primary_603_; lean_object* v_secondary_604_; lean_object* v_notes_605_; lean_object* v_help_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_616_; 
v_code_600_ = lean_ctor_get(v_d_598_, 0);
v_severity_601_ = lean_ctor_get_uint8(v_d_598_, sizeof(void*)*6);
v_title_602_ = lean_ctor_get(v_d_598_, 1);
v_primary_603_ = lean_ctor_get(v_d_598_, 2);
v_secondary_604_ = lean_ctor_get(v_d_598_, 3);
v_notes_605_ = lean_ctor_get(v_d_598_, 4);
v_help_606_ = lean_ctor_get(v_d_598_, 5);
v_isSharedCheck_616_ = !lean_is_exclusive(v_d_598_);
if (v_isSharedCheck_616_ == 0)
{
v___x_608_ = v_d_598_;
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_help_606_);
lean_inc(v_notes_605_);
lean_inc(v_secondary_604_);
lean_inc(v_primary_603_);
lean_inc(v_title_602_);
lean_inc(v_code_600_);
lean_dec(v_d_598_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_616_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_614_; 
v___x_610_ = lean_box(0);
v___x_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_611_, 0, v_span_599_);
lean_ctor_set(v___x_611_, 1, v___x_610_);
v___x_612_ = l_List_appendTR___redArg(v_secondary_604_, v___x_611_);
if (v_isShared_609_ == 0)
{
lean_ctor_set(v___x_608_, 3, v___x_612_);
v___x_614_ = v___x_608_;
goto v_reusejp_613_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_code_600_);
lean_ctor_set(v_reuseFailAlloc_615_, 1, v_title_602_);
lean_ctor_set(v_reuseFailAlloc_615_, 2, v_primary_603_);
lean_ctor_set(v_reuseFailAlloc_615_, 3, v___x_612_);
lean_ctor_set(v_reuseFailAlloc_615_, 4, v_notes_605_);
lean_ctor_set(v_reuseFailAlloc_615_, 5, v_help_606_);
lean_ctor_set_uint8(v_reuseFailAlloc_615_, sizeof(void*)*6, v_severity_601_);
v___x_614_ = v_reuseFailAlloc_615_;
goto v_reusejp_613_;
}
v_reusejp_613_:
{
return v___x_614_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_addNote(lean_object* v_d_617_, lean_object* v_note_618_){
_start:
{
lean_object* v_code_619_; uint8_t v_severity_620_; lean_object* v_title_621_; lean_object* v_primary_622_; lean_object* v_secondary_623_; lean_object* v_notes_624_; lean_object* v_help_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_635_; 
v_code_619_ = lean_ctor_get(v_d_617_, 0);
v_severity_620_ = lean_ctor_get_uint8(v_d_617_, sizeof(void*)*6);
v_title_621_ = lean_ctor_get(v_d_617_, 1);
v_primary_622_ = lean_ctor_get(v_d_617_, 2);
v_secondary_623_ = lean_ctor_get(v_d_617_, 3);
v_notes_624_ = lean_ctor_get(v_d_617_, 4);
v_help_625_ = lean_ctor_get(v_d_617_, 5);
v_isSharedCheck_635_ = !lean_is_exclusive(v_d_617_);
if (v_isSharedCheck_635_ == 0)
{
v___x_627_ = v_d_617_;
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_help_625_);
lean_inc(v_notes_624_);
lean_inc(v_secondary_623_);
lean_inc(v_primary_622_);
lean_inc(v_title_621_);
lean_inc(v_code_619_);
lean_dec(v_d_617_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_635_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_629_ = lean_box(0);
v___x_630_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_630_, 0, v_note_618_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_List_appendTR___redArg(v_notes_624_, v___x_630_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 4, v___x_631_);
v___x_633_ = v___x_627_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_code_619_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_title_621_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_primary_622_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_secondary_623_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_634_, 5, v_help_625_);
lean_ctor_set_uint8(v_reuseFailAlloc_634_, sizeof(void*)*6, v_severity_620_);
v___x_633_ = v_reuseFailAlloc_634_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
return v___x_633_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Diagnostics_addHelp(lean_object* v_d_636_, lean_object* v_help_637_){
_start:
{
lean_object* v_code_638_; uint8_t v_severity_639_; lean_object* v_title_640_; lean_object* v_primary_641_; lean_object* v_secondary_642_; lean_object* v_notes_643_; lean_object* v_help_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_654_; 
v_code_638_ = lean_ctor_get(v_d_636_, 0);
v_severity_639_ = lean_ctor_get_uint8(v_d_636_, sizeof(void*)*6);
v_title_640_ = lean_ctor_get(v_d_636_, 1);
v_primary_641_ = lean_ctor_get(v_d_636_, 2);
v_secondary_642_ = lean_ctor_get(v_d_636_, 3);
v_notes_643_ = lean_ctor_get(v_d_636_, 4);
v_help_644_ = lean_ctor_get(v_d_636_, 5);
v_isSharedCheck_654_ = !lean_is_exclusive(v_d_636_);
if (v_isSharedCheck_654_ == 0)
{
v___x_646_ = v_d_636_;
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_help_644_);
lean_inc(v_notes_643_);
lean_inc(v_secondary_642_);
lean_inc(v_primary_641_);
lean_inc(v_title_640_);
lean_inc(v_code_638_);
lean_dec(v_d_636_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_654_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v_help_637_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_List_appendTR___redArg(v_help_644_, v___x_649_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 5, v___x_650_);
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_code_638_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_title_640_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_primary_641_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_secondary_642_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_notes_643_);
lean_ctor_set(v_reuseFailAlloc_653_, 5, v___x_650_);
lean_ctor_set_uint8(v_reuseFailAlloc_653_, sizeof(void*)*6, v_severity_639_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_Diagnostics(uint8_t builtin) {
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
