// Lean compiler output
// Module: Oak.PhantomRepresentation
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
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bits"};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__3_value),((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__9_value;
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "size"};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__11_value;
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "alignment"};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__12 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__12_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__12_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__13_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__14;
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__15 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__15_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__16;
static lean_once_cell_t lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__18 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__18_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__15_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__19 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__19_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation___closed__0_value;
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "nominal"};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__2_value),((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__3_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__4;
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__6_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate___closed__0_value;
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "phantom"};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg___closed__1_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance = (const lean_object*)&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instantiate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instantiate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_erasePhantom(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_erasePhantom___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_rebindPhantom(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_bits_3_; lean_object* v_size_4_; lean_object* v_alignment_5_; lean_object* v_bits_6_; lean_object* v_size_7_; lean_object* v_alignment_8_; uint8_t v___x_9_; 
v_bits_3_ = lean_ctor_get(v_x_1_, 0);
v_size_4_ = lean_ctor_get(v_x_1_, 1);
v_alignment_5_ = lean_ctor_get(v_x_1_, 2);
v_bits_6_ = lean_ctor_get(v_x_2_, 0);
v_size_7_ = lean_ctor_get(v_x_2_, 1);
v_alignment_8_ = lean_ctor_get(v_x_2_, 2);
v___x_9_ = lean_nat_dec_eq(v_bits_3_, v_bits_6_);
if (v___x_9_ == 0)
{
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_eq(v_size_4_, v_size_7_);
if (v___x_10_ == 0)
{
return v___x_10_;
}
else
{
uint8_t v___x_11_; 
v___x_11_ = lean_nat_dec_eq(v_alignment_5_, v_alignment_8_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation_decEq___boxed(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation_decEq(v_x_12_, v_x_13_);
lean_dec_ref(v_x_13_);
lean_dec_ref(v_x_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation_decEq(v_x_16_, v_x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation___boxed(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation(v_x_19_, v_x_20_);
lean_dec_ref(v_x_20_);
lean_dec_ref(v_x_19_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(8u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_47_; lean_object* v___x_48_; 
v___x_47_ = lean_unsigned_to_nat(13u);
v___x_48_ = lean_nat_to_int(v___x_47_);
return v___x_48_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__16(void){
_start:
{
lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_50_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__0));
v___x_51_ = lean_string_length(v___x_50_);
return v___x_51_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_obj_once(&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__16, &lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__16_once, _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__16);
v___x_53_ = lean_nat_to_int(v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg(lean_object* v_x_58_){
_start:
{
lean_object* v_bits_59_; lean_object* v_size_60_; lean_object* v_alignment_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; uint8_t v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_bits_59_ = lean_ctor_get(v_x_58_, 0);
lean_inc(v_bits_59_);
v_size_60_ = lean_ctor_get(v_x_58_, 1);
lean_inc(v_size_60_);
v_alignment_61_ = lean_ctor_get(v_x_58_, 2);
lean_inc(v_alignment_61_);
lean_dec_ref(v_x_58_);
v___x_62_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__5));
v___x_63_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__6));
v___x_64_ = lean_obj_once(&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__7);
v___x_65_ = l_Nat_reprFast(v_bits_59_);
v___x_66_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
v___x_67_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_64_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = 0;
v___x_69_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set_uint8(v___x_69_, sizeof(void*)*1, v___x_68_);
v___x_70_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_70_, 0, v___x_63_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
v___x_71_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__9));
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_70_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = lean_box(1);
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__11));
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_62_);
v___x_78_ = l_Nat_reprFast(v_size_60_);
v___x_79_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___x_80_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_64_);
lean_ctor_set(v___x_80_, 1, v___x_79_);
v___x_81_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*1, v___x_68_);
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_77_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_71_);
v___x_84_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set(v___x_84_, 1, v___x_73_);
v___x_85_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__13));
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_62_);
v___x_88_ = lean_obj_once(&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__14, &lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__14_once, _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__14);
v___x_89_ = l_Nat_reprFast(v_alignment_61_);
v___x_90_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
v___x_91_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_88_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_92_, 0, v___x_91_);
lean_ctor_set_uint8(v___x_92_, sizeof(void*)*1, v___x_68_);
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_87_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_obj_once(&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17, &lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17_once, _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17);
v___x_95_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__18));
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_95_);
lean_ctor_set(v___x_96_, 1, v___x_93_);
v___x_97_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__19));
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_94_);
lean_ctor_set(v___x_99_, 1, v___x_98_);
v___x_100_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*1, v___x_68_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr(lean_object* v_x_101_, lean_object* v_prec_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg(v_x_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___boxed(lean_object* v_x_104_, lean_object* v_prec_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr(v_x_104_, v_prec_105_);
lean_dec(v_prec_105_);
return v_res_106_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate_decEq(lean_object* v_x_109_, lean_object* v_x_110_){
_start:
{
lean_object* v_nominal_111_; lean_object* v_runtime_112_; lean_object* v_nominal_113_; lean_object* v_runtime_114_; uint8_t v___x_115_; 
v_nominal_111_ = lean_ctor_get(v_x_109_, 0);
v_runtime_112_ = lean_ctor_get(v_x_109_, 1);
v_nominal_113_ = lean_ctor_get(v_x_110_, 0);
v_runtime_114_ = lean_ctor_get(v_x_110_, 1);
v___x_115_ = lean_nat_dec_eq(v_nominal_111_, v_nominal_113_);
if (v___x_115_ == 0)
{
return v___x_115_;
}
else
{
uint8_t v___x_116_; 
v___x_116_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation_decEq(v_runtime_112_, v_runtime_114_);
return v___x_116_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate_decEq___boxed(lean_object* v_x_117_, lean_object* v_x_118_){
_start:
{
uint8_t v_res_119_; lean_object* v_r_120_; 
v_res_119_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate_decEq(v_x_117_, v_x_118_);
lean_dec_ref(v_x_118_);
lean_dec_ref(v_x_117_);
v_r_120_ = lean_box(v_res_119_);
return v_r_120_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate(lean_object* v_x_121_, lean_object* v_x_122_){
_start:
{
uint8_t v___x_123_; 
v___x_123_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate_decEq(v_x_121_, v_x_122_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate___boxed(lean_object* v_x_124_, lean_object* v_x_125_){
_start:
{
uint8_t v_res_126_; lean_object* v_r_127_; 
v_res_126_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqPhantomTemplate(v_x_124_, v_x_125_);
lean_dec_ref(v_x_125_);
lean_dec_ref(v_x_124_);
v_r_127_ = lean_box(v_res_126_);
return v_r_127_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_unsigned_to_nat(11u);
v___x_138_ = lean_nat_to_int(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg(lean_object* v_x_142_){
_start:
{
lean_object* v_nominal_143_; lean_object* v_runtime_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_177_; 
v_nominal_143_ = lean_ctor_get(v_x_142_, 0);
v_runtime_144_ = lean_ctor_get(v_x_142_, 1);
v_isSharedCheck_177_ = !lean_is_exclusive(v_x_142_);
if (v_isSharedCheck_177_ == 0)
{
v___x_146_ = v_x_142_;
v_isShared_147_ = v_isSharedCheck_177_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_runtime_144_);
lean_inc(v_nominal_143_);
lean_dec(v_x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_177_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_154_; 
v___x_148_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__5));
v___x_149_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__3));
v___x_150_ = lean_obj_once(&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__4, &lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__4_once, _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__4);
v___x_151_ = l_Nat_reprFast(v_nominal_143_);
v___x_152_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
if (v_isShared_147_ == 0)
{
lean_ctor_set_tag(v___x_146_, 4);
lean_ctor_set(v___x_146_, 1, v___x_152_);
lean_ctor_set(v___x_146_, 0, v___x_150_);
v___x_154_ = v___x_146_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v___x_152_);
v___x_154_ = v_reuseFailAlloc_176_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_155_ = 0;
v___x_156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_155_);
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_149_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__9));
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = lean_box(1);
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__6));
v___x_163_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v___x_148_);
v___x_165_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg(v_runtime_144_);
v___x_166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_150_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_155_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_164_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_obj_once(&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17, &lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17_once, _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17);
v___x_170_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__18));
v___x_171_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_168_);
v___x_172_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__19));
v___x_173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_174_, 0, v___x_169_);
lean_ctor_set(v___x_174_, 1, v___x_173_);
v___x_175_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_175_, 0, v___x_174_);
lean_ctor_set_uint8(v___x_175_, sizeof(void*)*1, v___x_155_);
return v___x_175_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr(lean_object* v_x_178_, lean_object* v_prec_179_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg(v_x_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___boxed(lean_object* v_x_181_, lean_object* v_prec_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr(v_x_181_, v_prec_182_);
lean_dec(v_prec_182_);
return v_res_183_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance_decEq(lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
lean_object* v_nominal_188_; lean_object* v_phantom_189_; lean_object* v_runtime_190_; lean_object* v_nominal_191_; lean_object* v_phantom_192_; lean_object* v_runtime_193_; uint8_t v___x_194_; 
v_nominal_188_ = lean_ctor_get(v_x_186_, 0);
v_phantom_189_ = lean_ctor_get(v_x_186_, 1);
v_runtime_190_ = lean_ctor_get(v_x_186_, 2);
v_nominal_191_ = lean_ctor_get(v_x_187_, 0);
v_phantom_192_ = lean_ctor_get(v_x_187_, 1);
v_runtime_193_ = lean_ctor_get(v_x_187_, 2);
v___x_194_ = lean_nat_dec_eq(v_nominal_188_, v_nominal_191_);
if (v___x_194_ == 0)
{
return v___x_194_;
}
else
{
uint8_t v___x_195_; 
v___x_195_ = lean_nat_dec_eq(v_phantom_189_, v_phantom_192_);
if (v___x_195_ == 0)
{
return v___x_195_;
}
else
{
uint8_t v___x_196_; 
v___x_196_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqRuntimeRepresentation_decEq(v_runtime_190_, v_runtime_193_);
return v___x_196_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance_decEq___boxed(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance_decEq(v_x_197_, v_x_198_);
lean_dec_ref(v_x_198_);
lean_dec_ref(v_x_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance(lean_object* v_x_201_, lean_object* v_x_202_){
_start:
{
uint8_t v___x_203_; 
v___x_203_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance_decEq(v_x_201_, v_x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance___boxed(lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
uint8_t v_res_206_; lean_object* v_r_207_; 
v_res_206_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instDecidableEqInstance(v_x_204_, v_x_205_);
lean_dec_ref(v_x_205_);
lean_dec_ref(v_x_204_);
v_r_207_ = lean_box(v_res_206_);
return v_r_207_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg(lean_object* v_x_211_){
_start:
{
lean_object* v_nominal_212_; lean_object* v_phantom_213_; lean_object* v_runtime_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; uint8_t v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v_nominal_212_ = lean_ctor_get(v_x_211_, 0);
lean_inc(v_nominal_212_);
v_phantom_213_ = lean_ctor_get(v_x_211_, 1);
lean_inc(v_phantom_213_);
v_runtime_214_ = lean_ctor_get(v_x_211_, 2);
lean_inc_ref(v_runtime_214_);
lean_dec_ref(v_x_211_);
v___x_215_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__5));
v___x_216_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__3));
v___x_217_ = lean_obj_once(&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__4, &lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__4_once, _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__4);
v___x_218_ = l_Nat_reprFast(v_nominal_212_);
v___x_219_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_219_, 0, v___x_218_);
v___x_220_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_217_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = 0;
v___x_222_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_222_, 0, v___x_220_);
lean_ctor_set_uint8(v___x_222_, sizeof(void*)*1, v___x_221_);
v___x_223_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_216_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__9));
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_box(1);
v___x_227_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set(v___x_227_, 1, v___x_226_);
v___x_228_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg___closed__1));
v___x_229_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_227_);
lean_ctor_set(v___x_229_, 1, v___x_228_);
v___x_230_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___x_215_);
v___x_231_ = l_Nat_reprFast(v_phantom_213_);
v___x_232_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_232_, 0, v___x_231_);
v___x_233_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_217_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_234_, 0, v___x_233_);
lean_ctor_set_uint8(v___x_234_, sizeof(void*)*1, v___x_221_);
v___x_235_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_230_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v___x_224_);
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_226_);
v___x_238_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprPhantomTemplate_repr___redArg___closed__6));
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_237_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
v___x_240_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___x_215_);
v___x_241_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg(v_runtime_214_);
v___x_242_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_217_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set_uint8(v___x_243_, sizeof(void*)*1, v___x_221_);
v___x_244_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_240_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_obj_once(&lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17, &lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17_once, _init_lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__17);
v___x_246_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__18));
v___x_247_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_246_);
lean_ctor_set(v___x_247_, 1, v___x_244_);
v___x_248_ = ((lean_object*)(lp_oak_x2dspec_Oak_PhantomRepresentation_instReprRuntimeRepresentation_repr___redArg___closed__19));
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_245_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_251_, 0, v___x_250_);
lean_ctor_set_uint8(v___x_251_, sizeof(void*)*1, v___x_221_);
return v___x_251_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr(lean_object* v_x_252_, lean_object* v_prec_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___redArg(v_x_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr___boxed(lean_object* v_x_255_, lean_object* v_prec_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instReprInstance_repr(v_x_255_, v_prec_256_);
lean_dec(v_prec_256_);
return v_res_257_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instantiate(lean_object* v_template_260_, lean_object* v_phantom_261_){
_start:
{
lean_object* v_nominal_262_; lean_object* v_runtime_263_; lean_object* v___x_264_; 
v_nominal_262_ = lean_ctor_get(v_template_260_, 0);
v_runtime_263_ = lean_ctor_get(v_template_260_, 1);
lean_inc_ref(v_runtime_263_);
lean_inc(v_nominal_262_);
v___x_264_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_264_, 0, v_nominal_262_);
lean_ctor_set(v___x_264_, 1, v_phantom_261_);
lean_ctor_set(v___x_264_, 2, v_runtime_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_instantiate___boxed(lean_object* v_template_265_, lean_object* v_phantom_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = lp_oak_x2dspec_Oak_PhantomRepresentation_instantiate(v_template_265_, v_phantom_266_);
lean_dec_ref(v_template_265_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_erasePhantom(lean_object* v_inst_268_){
_start:
{
lean_object* v_runtime_269_; 
v_runtime_269_ = lean_ctor_get(v_inst_268_, 2);
lean_inc_ref(v_runtime_269_);
return v_runtime_269_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_erasePhantom___boxed(lean_object* v_inst_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = lp_oak_x2dspec_Oak_PhantomRepresentation_erasePhantom(v_inst_270_);
lean_dec_ref(v_inst_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_PhantomRepresentation_rebindPhantom(lean_object* v_inst_272_, lean_object* v_phantom_273_){
_start:
{
lean_object* v_nominal_274_; lean_object* v_runtime_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
v_nominal_274_ = lean_ctor_get(v_inst_272_, 0);
v_runtime_275_ = lean_ctor_get(v_inst_272_, 2);
v_isSharedCheck_282_ = !lean_is_exclusive(v_inst_272_);
if (v_isSharedCheck_282_ == 0)
{
lean_object* v_unused_283_; 
v_unused_283_ = lean_ctor_get(v_inst_272_, 1);
lean_dec(v_unused_283_);
v___x_277_ = v_inst_272_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_runtime_275_);
lean_inc(v_nominal_274_);
lean_dec(v_inst_272_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 1, v_phantom_273_);
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_nominal_274_);
lean_ctor_set(v_reuseFailAlloc_281_, 1, v_phantom_273_);
lean_ctor_set(v_reuseFailAlloc_281_, 2, v_runtime_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_PhantomRepresentation(uint8_t builtin) {
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
