// Lean compiler output
// Module: Oak.TypeVarIdentity
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binder"};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__3_value),((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__9_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "name"};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__11_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__12;
static const lean_string_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__13_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__14;
static lean_once_cell_t lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__15;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__16 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__16_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__13_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__17 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_atom_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_atom_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_arrow_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_arrow_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Oak.TypeVarIdentity.Ty.var"};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__2_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3;
static lean_once_cell_t lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4;
static const lean_string_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Oak.TypeVarIdentity.Ty.atom"};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__6_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__7 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__7_value;
static const lean_string_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Oak.TypeVarIdentity.Ty.arrow"};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__9_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__10_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy = (const lean_object*)&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_empty(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_empty___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_singleton(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_singleton___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_apply(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_TypeVarIdentity_0__Oak_TypeVarIdentity_instReprTy_repr_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_TypeVarIdentity_0__Oak_TypeVarIdentity_instReprTy_repr_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_TypeVarIdentity_0__Oak_TypeVarIdentity_apply_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_TypeVarIdentity_0__Oak_TypeVarIdentity_apply_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_binder_3_; lean_object* v_name_4_; lean_object* v_binder_5_; lean_object* v_name_6_; uint8_t v___x_7_; 
v_binder_3_ = lean_ctor_get(v_x_1_, 0);
v_name_4_ = lean_ctor_get(v_x_1_, 1);
v_binder_5_ = lean_ctor_get(v_x_2_, 0);
v_name_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_nat_dec_eq(v_binder_3_, v_binder_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_eq(v_name_4_, v_name_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar_decEq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar_decEq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar_decEq(v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(10u);
v___x_34_ = lean_nat_to_int(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(8u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__0));
v___x_45_ = lean_string_length(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__14, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__14_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__14);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg(lean_object* v_x_52_){
_start:
{
lean_object* v_binder_53_; lean_object* v_name_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_89_; 
v_binder_53_ = lean_ctor_get(v_x_52_, 0);
v_name_54_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_89_ == 0)
{
v___x_56_ = v_x_52_;
v_isShared_57_ = v_isSharedCheck_89_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_name_54_);
lean_inc(v_binder_53_);
lean_dec(v_x_52_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_89_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_58_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__5));
v___x_59_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__6));
v___x_60_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__7);
v___x_61_ = l_Nat_reprFast(v_binder_53_);
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
v___x_68_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__9));
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_box(1);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__11));
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_58_);
v___x_75_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__12, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__12_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__12);
v___x_76_ = l_Nat_reprFast(v_name_54_);
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
v___x_81_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__15);
v___x_82_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__16));
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_80_);
v___x_84_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg___closed__17));
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
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr(lean_object* v_x_90_, lean_object* v_prec_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg(v_x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___boxed(lean_object* v_x_93_, lean_object* v_prec_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr(v_x_93_, v_prec_94_);
lean_dec(v_prec_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorIdx(lean_object* v_x_98_){
_start:
{
switch(lean_obj_tag(v_x_98_))
{
case 0:
{
lean_object* v___x_99_; 
v___x_99_ = lean_unsigned_to_nat(0u);
return v___x_99_;
}
case 1:
{
lean_object* v___x_100_; 
v___x_100_ = lean_unsigned_to_nat(1u);
return v___x_100_;
}
default: 
{
lean_object* v___x_101_; 
v___x_101_ = lean_unsigned_to_nat(2u);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorIdx___boxed(lean_object* v_x_102_){
_start:
{
lean_object* v_res_103_; 
v_res_103_ = lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorIdx(v_x_102_);
lean_dec_ref(v_x_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___redArg(lean_object* v_t_104_, lean_object* v_k_105_){
_start:
{
switch(lean_obj_tag(v_t_104_))
{
case 0:
{
lean_object* v_a_106_; lean_object* v___x_107_; 
v_a_106_ = lean_ctor_get(v_t_104_, 0);
lean_inc_ref(v_a_106_);
lean_dec_ref_known(v_t_104_, 1);
v___x_107_ = lean_apply_1(v_k_105_, v_a_106_);
return v___x_107_;
}
case 1:
{
lean_object* v_a_108_; lean_object* v___x_109_; 
v_a_108_ = lean_ctor_get(v_t_104_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v_t_104_, 1);
v___x_109_ = lean_apply_1(v_k_105_, v_a_108_);
return v___x_109_;
}
default: 
{
lean_object* v_a_110_; lean_object* v_a_111_; lean_object* v___x_112_; 
v_a_110_ = lean_ctor_get(v_t_104_, 0);
lean_inc_ref(v_a_110_);
v_a_111_ = lean_ctor_get(v_t_104_, 1);
lean_inc_ref(v_a_111_);
lean_dec_ref_known(v_t_104_, 2);
v___x_112_ = lean_apply_2(v_k_105_, v_a_110_, v_a_111_);
return v___x_112_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim(lean_object* v_motive_113_, lean_object* v_ctorIdx_114_, lean_object* v_t_115_, lean_object* v_h_116_, lean_object* v_k_117_){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___redArg(v_t_115_, v_k_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___boxed(lean_object* v_motive_119_, lean_object* v_ctorIdx_120_, lean_object* v_t_121_, lean_object* v_h_122_, lean_object* v_k_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim(v_motive_119_, v_ctorIdx_120_, v_t_121_, v_h_122_, v_k_123_);
lean_dec(v_ctorIdx_120_);
return v_res_124_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_var_elim___redArg(lean_object* v_t_125_, lean_object* v_var_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___redArg(v_t_125_, v_var_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_var_elim(lean_object* v_motive_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_var_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___redArg(v_t_129_, v_var_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_atom_elim___redArg(lean_object* v_t_133_, lean_object* v_atom_134_){
_start:
{
lean_object* v___x_135_; 
v___x_135_ = lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___redArg(v_t_133_, v_atom_134_);
return v___x_135_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_atom_elim(lean_object* v_motive_136_, lean_object* v_t_137_, lean_object* v_h_138_, lean_object* v_atom_139_){
_start:
{
lean_object* v___x_140_; 
v___x_140_ = lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___redArg(v_t_137_, v_atom_139_);
return v___x_140_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_arrow_elim___redArg(lean_object* v_t_141_, lean_object* v_arrow_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___redArg(v_t_141_, v_arrow_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_arrow_elim(lean_object* v_motive_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_arrow_147_){
_start:
{
lean_object* v___x_148_; 
v___x_148_ = lp_oak_x2dspec_Oak_TypeVarIdentity_Ty_ctorElim___redArg(v_t_145_, v_arrow_147_);
return v___x_148_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy_decEq(lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
switch(lean_obj_tag(v_x_149_))
{
case 0:
{
if (lean_obj_tag(v_x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v_a_152_; uint8_t v___x_153_; 
v_a_151_ = lean_ctor_get(v_x_149_, 0);
v_a_152_ = lean_ctor_get(v_x_150_, 0);
v___x_153_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar_decEq(v_a_151_, v_a_152_);
return v___x_153_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 0;
return v___x_154_;
}
}
case 1:
{
if (lean_obj_tag(v_x_150_) == 1)
{
lean_object* v_a_155_; lean_object* v_a_156_; uint8_t v___x_157_; 
v_a_155_ = lean_ctor_get(v_x_149_, 0);
v_a_156_ = lean_ctor_get(v_x_150_, 0);
v___x_157_ = lean_nat_dec_eq(v_a_155_, v_a_156_);
return v___x_157_;
}
else
{
uint8_t v___x_158_; 
v___x_158_ = 0;
return v___x_158_;
}
}
default: 
{
if (lean_obj_tag(v_x_150_) == 2)
{
lean_object* v_a_159_; lean_object* v_a_160_; lean_object* v_a_161_; lean_object* v_a_162_; uint8_t v_inst_163_; 
v_a_159_ = lean_ctor_get(v_x_149_, 0);
v_a_160_ = lean_ctor_get(v_x_149_, 1);
v_a_161_ = lean_ctor_get(v_x_150_, 0);
v_a_162_ = lean_ctor_get(v_x_150_, 1);
v_inst_163_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy_decEq(v_a_159_, v_a_161_);
if (v_inst_163_ == 0)
{
return v_inst_163_;
}
else
{
v_x_149_ = v_a_160_;
v_x_150_ = v_a_162_;
goto _start;
}
}
else
{
uint8_t v___x_165_; 
v___x_165_ = 0;
return v___x_165_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy_decEq___boxed(lean_object* v_x_166_, lean_object* v_x_167_){
_start:
{
uint8_t v_res_168_; lean_object* v_r_169_; 
v_res_168_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy_decEq(v_x_166_, v_x_167_);
lean_dec_ref(v_x_167_);
lean_dec_ref(v_x_166_);
v_r_169_ = lean_box(v_res_168_);
return v_r_169_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy(lean_object* v_x_170_, lean_object* v_x_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy_decEq(v_x_170_, v_x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy___boxed(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
uint8_t v_res_175_; lean_object* v_r_176_; 
v_res_175_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTy(v_x_173_, v_x_174_);
lean_dec_ref(v_x_174_);
lean_dec_ref(v_x_173_);
v_r_176_ = lean_box(v_res_175_);
return v_r_176_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_unsigned_to_nat(2u);
v___x_184_ = lean_nat_to_int(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_unsigned_to_nat(1u);
v___x_186_ = lean_nat_to_int(v___x_185_);
return v___x_186_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr(lean_object* v_x_199_, lean_object* v_prec_200_){
_start:
{
switch(lean_obj_tag(v_x_199_))
{
case 0:
{
lean_object* v_a_201_; lean_object* v___y_203_; lean_object* v___x_211_; uint8_t v___x_212_; 
v_a_201_ = lean_ctor_get(v_x_199_, 0);
lean_inc_ref(v_a_201_);
lean_dec_ref_known(v_x_199_, 1);
v___x_211_ = lean_unsigned_to_nat(1024u);
v___x_212_ = lean_nat_dec_le(v___x_211_, v_prec_200_);
if (v___x_212_ == 0)
{
lean_object* v___x_213_; 
v___x_213_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3);
v___y_203_ = v___x_213_;
goto v___jp_202_;
}
else
{
lean_object* v___x_214_; 
v___x_214_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4);
v___y_203_ = v___x_214_;
goto v___jp_202_;
}
v___jp_202_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v___x_204_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__2));
v___x_205_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTypeVar_repr___redArg(v_a_201_);
v___x_206_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
lean_inc(v___y_203_);
v___x_207_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_207_, 0, v___y_203_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = 0;
v___x_209_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set_uint8(v___x_209_, sizeof(void*)*1, v___x_208_);
v___x_210_ = l_Repr_addAppParen(v___x_209_, v_prec_200_);
return v___x_210_;
}
}
case 1:
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_235_; 
v_a_215_ = lean_ctor_get(v_x_199_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_235_ == 0)
{
v___x_217_ = v_x_199_;
v_isShared_218_ = v_isSharedCheck_235_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v_x_199_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_235_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___y_220_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(1024u);
v___x_232_ = lean_nat_dec_le(v___x_231_, v_prec_200_);
if (v___x_232_ == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3);
v___y_220_ = v___x_233_;
goto v___jp_219_;
}
else
{
lean_object* v___x_234_; 
v___x_234_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4);
v___y_220_ = v___x_234_;
goto v___jp_219_;
}
v___jp_219_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__7));
v___x_222_ = l_Nat_reprFast(v_a_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set_tag(v___x_217_, 3);
lean_ctor_set(v___x_217_, 0, v___x_222_);
v___x_224_ = v___x_217_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_230_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; uint8_t v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v___x_225_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_221_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
lean_inc(v___y_220_);
v___x_226_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_226_, 0, v___y_220_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = 0;
v___x_228_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set_uint8(v___x_228_, sizeof(void*)*1, v___x_227_);
v___x_229_ = l_Repr_addAppParen(v___x_228_, v_prec_200_);
return v___x_229_;
}
}
}
}
default: 
{
lean_object* v_a_236_; lean_object* v_a_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_260_; 
v_a_236_ = lean_ctor_get(v_x_199_, 0);
v_a_237_ = lean_ctor_get(v_x_199_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_199_);
if (v_isSharedCheck_260_ == 0)
{
v___x_239_ = v_x_199_;
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_a_237_);
lean_inc(v_a_236_);
lean_dec(v_x_199_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_260_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___y_243_; uint8_t v___x_257_; 
v___x_241_ = lean_unsigned_to_nat(1024u);
v___x_257_ = lean_nat_dec_le(v___x_241_, v_prec_200_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
v___x_258_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__3);
v___y_243_ = v___x_258_;
goto v___jp_242_;
}
else
{
lean_object* v___x_259_; 
v___x_259_ = lean_obj_once(&lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4, &lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__4);
v___y_243_ = v___x_259_;
goto v___jp_242_;
}
v___jp_242_:
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
v___x_244_ = lean_box(1);
v___x_245_ = ((lean_object*)(lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___closed__10));
v___x_246_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr(v_a_236_, v___x_241_);
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 5);
lean_ctor_set(v___x_239_, 1, v___x_246_);
lean_ctor_set(v___x_239_, 0, v___x_245_);
v___x_248_ = v___x_239_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_246_);
v___x_248_ = v_reuseFailAlloc_256_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_249_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_244_);
v___x_250_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr(v_a_237_, v___x_241_);
v___x_251_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
lean_inc(v___y_243_);
v___x_252_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_252_, 0, v___y_243_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = 0;
v___x_254_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set_uint8(v___x_254_, sizeof(void*)*1, v___x_253_);
v___x_255_ = l_Repr_addAppParen(v___x_254_, v_prec_200_);
return v___x_255_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr___boxed(lean_object* v_x_261_, lean_object* v_prec_262_){
_start:
{
lean_object* v_res_263_; 
v_res_263_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instReprTy_repr(v_x_261_, v_prec_262_);
lean_dec(v_prec_262_);
return v_res_263_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_empty(lean_object* v_x_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = lean_box(0);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_empty___boxed(lean_object* v_x_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = lp_oak_x2dspec_Oak_TypeVarIdentity_empty(v_x_268_);
lean_dec_ref(v_x_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_singleton(lean_object* v_v_270_, lean_object* v_replacement_271_, lean_object* v_candidate_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lp_oak_x2dspec_Oak_TypeVarIdentity_instDecidableEqTypeVar_decEq(v_candidate_272_, v_v_270_);
if (v___x_273_ == 0)
{
lean_object* v___x_274_; 
lean_dec_ref(v_replacement_271_);
v___x_274_ = lean_box(0);
return v___x_274_;
}
else
{
lean_object* v___x_275_; 
v___x_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_275_, 0, v_replacement_271_);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_singleton___boxed(lean_object* v_v_276_, lean_object* v_replacement_277_, lean_object* v_candidate_278_){
_start:
{
lean_object* v_res_279_; 
v_res_279_ = lp_oak_x2dspec_Oak_TypeVarIdentity_singleton(v_v_276_, v_replacement_277_, v_candidate_278_);
lean_dec_ref(v_candidate_278_);
lean_dec_ref(v_v_276_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_TypeVarIdentity_apply(lean_object* v_sub_280_, lean_object* v_x_281_){
_start:
{
switch(lean_obj_tag(v_x_281_))
{
case 0:
{
lean_object* v_a_282_; lean_object* v___x_283_; 
v_a_282_ = lean_ctor_get(v_x_281_, 0);
lean_inc_ref(v_a_282_);
v___x_283_ = lean_apply_1(v_sub_280_, v_a_282_);
if (lean_obj_tag(v___x_283_) == 0)
{
return v_x_281_;
}
else
{
lean_object* v_val_284_; 
lean_dec_ref_known(v_x_281_, 1);
v_val_284_ = lean_ctor_get(v___x_283_, 0);
lean_inc(v_val_284_);
lean_dec_ref_known(v___x_283_, 1);
return v_val_284_;
}
}
case 1:
{
lean_dec_ref(v_sub_280_);
return v_x_281_;
}
default: 
{
lean_object* v_a_285_; lean_object* v_a_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_295_; 
v_a_285_ = lean_ctor_get(v_x_281_, 0);
v_a_286_ = lean_ctor_get(v_x_281_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_x_281_);
if (v_isSharedCheck_295_ == 0)
{
v___x_288_ = v_x_281_;
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_a_286_);
lean_inc(v_a_285_);
lean_dec(v_x_281_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_295_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_293_; 
lean_inc_ref(v_sub_280_);
v___x_290_ = lp_oak_x2dspec_Oak_TypeVarIdentity_apply(v_sub_280_, v_a_285_);
v___x_291_ = lp_oak_x2dspec_Oak_TypeVarIdentity_apply(v_sub_280_, v_a_286_);
if (v_isShared_289_ == 0)
{
lean_ctor_set(v___x_288_, 1, v___x_291_);
lean_ctor_set(v___x_288_, 0, v___x_290_);
v___x_293_ = v___x_288_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v___x_290_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v___x_291_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_TypeVarIdentity_0__Oak_TypeVarIdentity_instReprTy_repr_match__1_splitter___redArg(lean_object* v_x_296_, lean_object* v_h__1_297_, lean_object* v_h__2_298_, lean_object* v_h__3_299_){
_start:
{
switch(lean_obj_tag(v_x_296_))
{
case 0:
{
lean_object* v_a_300_; lean_object* v___x_301_; 
lean_dec(v_h__3_299_);
lean_dec(v_h__2_298_);
v_a_300_ = lean_ctor_get(v_x_296_, 0);
lean_inc_ref(v_a_300_);
lean_dec_ref_known(v_x_296_, 1);
v___x_301_ = lean_apply_1(v_h__1_297_, v_a_300_);
return v___x_301_;
}
case 1:
{
lean_object* v_a_302_; lean_object* v___x_303_; 
lean_dec(v_h__3_299_);
lean_dec(v_h__1_297_);
v_a_302_ = lean_ctor_get(v_x_296_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v_x_296_, 1);
v___x_303_ = lean_apply_1(v_h__2_298_, v_a_302_);
return v___x_303_;
}
default: 
{
lean_object* v_a_304_; lean_object* v_a_305_; lean_object* v___x_306_; 
lean_dec(v_h__2_298_);
lean_dec(v_h__1_297_);
v_a_304_ = lean_ctor_get(v_x_296_, 0);
lean_inc_ref(v_a_304_);
v_a_305_ = lean_ctor_get(v_x_296_, 1);
lean_inc_ref(v_a_305_);
lean_dec_ref_known(v_x_296_, 2);
v___x_306_ = lean_apply_2(v_h__3_299_, v_a_304_, v_a_305_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_TypeVarIdentity_0__Oak_TypeVarIdentity_instReprTy_repr_match__1_splitter(lean_object* v_motive_307_, lean_object* v_x_308_, lean_object* v_h__1_309_, lean_object* v_h__2_310_, lean_object* v_h__3_311_){
_start:
{
switch(lean_obj_tag(v_x_308_))
{
case 0:
{
lean_object* v_a_312_; lean_object* v___x_313_; 
lean_dec(v_h__3_311_);
lean_dec(v_h__2_310_);
v_a_312_ = lean_ctor_get(v_x_308_, 0);
lean_inc_ref(v_a_312_);
lean_dec_ref_known(v_x_308_, 1);
v___x_313_ = lean_apply_1(v_h__1_309_, v_a_312_);
return v___x_313_;
}
case 1:
{
lean_object* v_a_314_; lean_object* v___x_315_; 
lean_dec(v_h__3_311_);
lean_dec(v_h__1_309_);
v_a_314_ = lean_ctor_get(v_x_308_, 0);
lean_inc(v_a_314_);
lean_dec_ref_known(v_x_308_, 1);
v___x_315_ = lean_apply_1(v_h__2_310_, v_a_314_);
return v___x_315_;
}
default: 
{
lean_object* v_a_316_; lean_object* v_a_317_; lean_object* v___x_318_; 
lean_dec(v_h__2_310_);
lean_dec(v_h__1_309_);
v_a_316_ = lean_ctor_get(v_x_308_, 0);
lean_inc_ref(v_a_316_);
v_a_317_ = lean_ctor_get(v_x_308_, 1);
lean_inc_ref(v_a_317_);
lean_dec_ref_known(v_x_308_, 2);
v___x_318_ = lean_apply_2(v_h__3_311_, v_a_316_, v_a_317_);
return v___x_318_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_TypeVarIdentity_0__Oak_TypeVarIdentity_apply_match__1_splitter___redArg(lean_object* v_x_319_, lean_object* v_h__1_320_, lean_object* v_h__2_321_){
_start:
{
if (lean_obj_tag(v_x_319_) == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v_h__1_320_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_apply_1(v_h__2_321_, v___x_322_);
return v___x_323_;
}
else
{
lean_object* v_val_324_; lean_object* v___x_325_; 
lean_dec(v_h__2_321_);
v_val_324_ = lean_ctor_get(v_x_319_, 0);
lean_inc(v_val_324_);
lean_dec_ref_known(v_x_319_, 1);
v___x_325_ = lean_apply_1(v_h__1_320_, v_val_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_TypeVarIdentity_0__Oak_TypeVarIdentity_apply_match__1_splitter(lean_object* v_motive_326_, lean_object* v_x_327_, lean_object* v_h__1_328_, lean_object* v_h__2_329_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_h__1_328_);
v___x_330_ = lean_box(0);
v___x_331_ = lean_apply_1(v_h__2_329_, v___x_330_);
return v___x_331_;
}
else
{
lean_object* v_val_332_; lean_object* v___x_333_; 
lean_dec(v_h__2_329_);
v_val_332_ = lean_ctor_get(v_x_327_, 0);
lean_inc(v_val_332_);
lean_dec_ref_known(v_x_327_, 1);
v___x_333_ = lean_apply_1(v_h__1_328_, v_val_332_);
return v___x_333_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_TypeVarIdentity(uint8_t builtin) {
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
