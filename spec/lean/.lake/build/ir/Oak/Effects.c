// Lean compiler output
// Module: Oak.Effects
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_memoryAllocate_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_memoryAllocate_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_threadBlock_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_threadBlock_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_osSyscall_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_osSyscall_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_mmio_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_mmio_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_io_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_io_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_user_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_user_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Oak.Effects.Family.io"};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Oak.Effects.Family.mmio"};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Oak.Effects.Family.osSyscall"};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__5_value;
static const lean_string_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Oak.Effects.Family.threadBlock"};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__6_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__6_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__7 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__7_value;
static const lean_string_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Oak.Effects.Family.memoryAllocate"};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__9_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10;
static lean_once_cell_t lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11;
static const lean_string_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Oak.Effects.Family.user"};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__12 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__12_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__12_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__13_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__13_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__14 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__14_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Effects_instReprFamily___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprFamily___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_broad_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_broad_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_scoped_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_scoped_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Oak.Effects.Effect.broad"};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__2_value;
static const lean_string_object lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Oak.Effects.Effect.scoped"};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__3_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__3_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__4_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__5_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Effects_instReprEffect___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect = (const lean_object*)&lp_oak_x2dspec_Oak_Effects_instReprEffect___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
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
case 3:
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
case 4:
{
lean_object* v___x_6_; 
v___x_6_ = lean_unsigned_to_nat(4u);
return v___x_6_;
}
default: 
{
lean_object* v___x_7_; 
v___x_7_ = lean_unsigned_to_nat(5u);
return v___x_7_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorIdx___boxed(lean_object* v_x_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = lp_oak_x2dspec_Oak_Effects_Family_ctorIdx(v_x_8_);
lean_dec(v_x_8_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(lean_object* v_t_10_, lean_object* v_k_11_){
_start:
{
if (lean_obj_tag(v_t_10_) == 5)
{
lean_object* v_a_12_; lean_object* v___x_13_; 
v_a_12_ = lean_ctor_get(v_t_10_, 0);
lean_inc(v_a_12_);
lean_dec_ref_known(v_t_10_, 1);
v___x_13_ = lean_apply_1(v_k_11_, v_a_12_);
return v___x_13_;
}
else
{
lean_dec(v_t_10_);
return v_k_11_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorElim(lean_object* v_motive_14_, lean_object* v_ctorIdx_15_, lean_object* v_t_16_, lean_object* v_h_17_, lean_object* v_k_18_){
_start:
{
lean_object* v___x_19_; 
v___x_19_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_16_, v_k_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_ctorElim___boxed(lean_object* v_motive_20_, lean_object* v_ctorIdx_21_, lean_object* v_t_22_, lean_object* v_h_23_, lean_object* v_k_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim(v_motive_20_, v_ctorIdx_21_, v_t_22_, v_h_23_, v_k_24_);
lean_dec(v_ctorIdx_21_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_memoryAllocate_elim___redArg(lean_object* v_t_26_, lean_object* v_memoryAllocate_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_26_, v_memoryAllocate_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_memoryAllocate_elim(lean_object* v_motive_29_, lean_object* v_t_30_, lean_object* v_h_31_, lean_object* v_memoryAllocate_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_30_, v_memoryAllocate_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_threadBlock_elim___redArg(lean_object* v_t_34_, lean_object* v_threadBlock_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_34_, v_threadBlock_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_threadBlock_elim(lean_object* v_motive_37_, lean_object* v_t_38_, lean_object* v_h_39_, lean_object* v_threadBlock_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_38_, v_threadBlock_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_osSyscall_elim___redArg(lean_object* v_t_42_, lean_object* v_osSyscall_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_42_, v_osSyscall_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_osSyscall_elim(lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_osSyscall_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_46_, v_osSyscall_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_mmio_elim___redArg(lean_object* v_t_50_, lean_object* v_mmio_51_){
_start:
{
lean_object* v___x_52_; 
v___x_52_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_50_, v_mmio_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_mmio_elim(lean_object* v_motive_53_, lean_object* v_t_54_, lean_object* v_h_55_, lean_object* v_mmio_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_54_, v_mmio_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_io_elim___redArg(lean_object* v_t_58_, lean_object* v_io_59_){
_start:
{
lean_object* v___x_60_; 
v___x_60_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_58_, v_io_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_io_elim(lean_object* v_motive_61_, lean_object* v_t_62_, lean_object* v_h_63_, lean_object* v_io_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_62_, v_io_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_user_elim___redArg(lean_object* v_t_66_, lean_object* v_user_67_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_66_, v_user_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Family_user_elim(lean_object* v_motive_69_, lean_object* v_t_70_, lean_object* v_h_71_, lean_object* v_user_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = lp_oak_x2dspec_Oak_Effects_Family_ctorElim___redArg(v_t_70_, v_user_72_);
return v___x_73_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily_decEq(lean_object* v_x_74_, lean_object* v_x_75_){
_start:
{
switch(lean_obj_tag(v_x_74_))
{
case 0:
{
switch(lean_obj_tag(v_x_75_))
{
case 0:
{
uint8_t v___x_76_; 
v___x_76_ = 1;
return v___x_76_;
}
case 5:
{
uint8_t v___x_77_; 
v___x_77_ = 0;
return v___x_77_;
}
default: 
{
uint8_t v___x_78_; 
v___x_78_ = 0;
return v___x_78_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_75_))
{
case 1:
{
uint8_t v___x_79_; 
v___x_79_ = 1;
return v___x_79_;
}
case 5:
{
uint8_t v___x_80_; 
v___x_80_ = 0;
return v___x_80_;
}
default: 
{
uint8_t v___x_81_; 
v___x_81_ = 0;
return v___x_81_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_x_75_))
{
case 2:
{
uint8_t v___x_82_; 
v___x_82_ = 1;
return v___x_82_;
}
case 5:
{
uint8_t v___x_83_; 
v___x_83_ = 0;
return v___x_83_;
}
default: 
{
uint8_t v___x_84_; 
v___x_84_ = 0;
return v___x_84_;
}
}
}
case 3:
{
switch(lean_obj_tag(v_x_75_))
{
case 3:
{
uint8_t v___x_85_; 
v___x_85_ = 1;
return v___x_85_;
}
case 5:
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
default: 
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
}
}
case 4:
{
switch(lean_obj_tag(v_x_75_))
{
case 4:
{
uint8_t v___x_88_; 
v___x_88_ = 1;
return v___x_88_;
}
case 5:
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
default: 
{
uint8_t v___x_90_; 
v___x_90_ = 0;
return v___x_90_;
}
}
}
default: 
{
lean_object* v_a_91_; uint8_t v___x_92_; 
v_a_91_ = lean_ctor_get(v_x_74_, 0);
v___x_92_ = 0;
if (lean_obj_tag(v_x_75_) == 5)
{
lean_object* v_a_93_; uint8_t v___x_94_; 
v_a_93_ = lean_ctor_get(v_x_75_, 0);
v___x_94_ = lean_nat_dec_eq(v_a_91_, v_a_93_);
if (v___x_94_ == 0)
{
return v___x_92_;
}
else
{
return v___x_94_;
}
}
else
{
return v___x_92_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily_decEq___boxed(lean_object* v_x_95_, lean_object* v_x_96_){
_start:
{
uint8_t v_res_97_; lean_object* v_r_98_; 
v_res_97_ = lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily_decEq(v_x_95_, v_x_96_);
lean_dec(v_x_96_);
lean_dec(v_x_95_);
v_r_98_ = lean_box(v_res_97_);
return v_r_98_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily(lean_object* v_x_99_, lean_object* v_x_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily_decEq(v_x_99_, v_x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily___boxed(lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
uint8_t v_res_104_; lean_object* v_r_105_; 
v_res_104_ = lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily(v_x_102_, v_x_103_);
lean_dec(v_x_103_);
lean_dec(v_x_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10(void){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(2u);
v___x_122_ = lean_nat_to_int(v___x_121_);
return v___x_122_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = lean_unsigned_to_nat(1u);
v___x_124_ = lean_nat_to_int(v___x_123_);
return v___x_124_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr(lean_object* v_x_131_, lean_object* v_prec_132_){
_start:
{
lean_object* v___y_134_; lean_object* v___y_141_; lean_object* v___y_148_; lean_object* v___y_155_; lean_object* v___y_162_; 
switch(lean_obj_tag(v_x_131_))
{
case 0:
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_unsigned_to_nat(1024u);
v___x_169_ = lean_nat_dec_le(v___x_168_, v_prec_132_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
v___x_170_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10);
v___y_162_ = v___x_170_;
goto v___jp_161_;
}
else
{
lean_object* v___x_171_; 
v___x_171_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11);
v___y_162_ = v___x_171_;
goto v___jp_161_;
}
}
case 1:
{
lean_object* v___x_172_; uint8_t v___x_173_; 
v___x_172_ = lean_unsigned_to_nat(1024u);
v___x_173_ = lean_nat_dec_le(v___x_172_, v_prec_132_);
if (v___x_173_ == 0)
{
lean_object* v___x_174_; 
v___x_174_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10);
v___y_155_ = v___x_174_;
goto v___jp_154_;
}
else
{
lean_object* v___x_175_; 
v___x_175_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11);
v___y_155_ = v___x_175_;
goto v___jp_154_;
}
}
case 2:
{
lean_object* v___x_176_; uint8_t v___x_177_; 
v___x_176_ = lean_unsigned_to_nat(1024u);
v___x_177_ = lean_nat_dec_le(v___x_176_, v_prec_132_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10);
v___y_148_ = v___x_178_;
goto v___jp_147_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11);
v___y_148_ = v___x_179_;
goto v___jp_147_;
}
}
case 3:
{
lean_object* v___x_180_; uint8_t v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(1024u);
v___x_181_ = lean_nat_dec_le(v___x_180_, v_prec_132_);
if (v___x_181_ == 0)
{
lean_object* v___x_182_; 
v___x_182_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10);
v___y_141_ = v___x_182_;
goto v___jp_140_;
}
else
{
lean_object* v___x_183_; 
v___x_183_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11);
v___y_141_ = v___x_183_;
goto v___jp_140_;
}
}
case 4:
{
lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_184_ = lean_unsigned_to_nat(1024u);
v___x_185_ = lean_nat_dec_le(v___x_184_, v_prec_132_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
v___x_186_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10);
v___y_134_ = v___x_186_;
goto v___jp_133_;
}
else
{
lean_object* v___x_187_; 
v___x_187_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11);
v___y_134_ = v___x_187_;
goto v___jp_133_;
}
}
default: 
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_208_; 
v_a_188_ = lean_ctor_get(v_x_131_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v_x_131_);
if (v_isSharedCheck_208_ == 0)
{
v___x_190_ = v_x_131_;
v_isShared_191_ = v_isSharedCheck_208_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v_x_131_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_208_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___y_193_; lean_object* v___x_204_; uint8_t v___x_205_; 
v___x_204_ = lean_unsigned_to_nat(1024u);
v___x_205_ = lean_nat_dec_le(v___x_204_, v_prec_132_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10);
v___y_193_ = v___x_206_;
goto v___jp_192_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11);
v___y_193_ = v___x_207_;
goto v___jp_192_;
}
v___jp_192_:
{
lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_197_; 
v___x_194_ = ((lean_object*)(lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__14));
v___x_195_ = l_Nat_reprFast(v_a_188_);
if (v_isShared_191_ == 0)
{
lean_ctor_set_tag(v___x_190_, 3);
lean_ctor_set(v___x_190_, 0, v___x_195_);
v___x_197_ = v___x_190_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v___x_195_);
v___x_197_ = v_reuseFailAlloc_203_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_194_);
lean_ctor_set(v___x_198_, 1, v___x_197_);
lean_inc(v___y_193_);
v___x_199_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_199_, 0, v___y_193_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = 0;
v___x_201_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set_uint8(v___x_201_, sizeof(void*)*1, v___x_200_);
v___x_202_ = l_Repr_addAppParen(v___x_201_, v_prec_132_);
return v___x_202_;
}
}
}
}
}
v___jp_133_:
{
lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_135_ = ((lean_object*)(lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__1));
lean_inc(v___y_134_);
v___x_136_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_136_, 0, v___y_134_);
lean_ctor_set(v___x_136_, 1, v___x_135_);
v___x_137_ = 0;
v___x_138_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_138_, 0, v___x_136_);
lean_ctor_set_uint8(v___x_138_, sizeof(void*)*1, v___x_137_);
v___x_139_ = l_Repr_addAppParen(v___x_138_, v_prec_132_);
return v___x_139_;
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; uint8_t v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_142_ = ((lean_object*)(lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__3));
lean_inc(v___y_141_);
v___x_143_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_143_, 0, v___y_141_);
lean_ctor_set(v___x_143_, 1, v___x_142_);
v___x_144_ = 0;
v___x_145_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_145_, 0, v___x_143_);
lean_ctor_set_uint8(v___x_145_, sizeof(void*)*1, v___x_144_);
v___x_146_ = l_Repr_addAppParen(v___x_145_, v_prec_132_);
return v___x_146_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_149_ = ((lean_object*)(lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__5));
lean_inc(v___y_148_);
v___x_150_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_150_, 0, v___y_148_);
lean_ctor_set(v___x_150_, 1, v___x_149_);
v___x_151_ = 0;
v___x_152_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_152_, 0, v___x_150_);
lean_ctor_set_uint8(v___x_152_, sizeof(void*)*1, v___x_151_);
v___x_153_ = l_Repr_addAppParen(v___x_152_, v_prec_132_);
return v___x_153_;
}
v___jp_154_:
{
lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_156_ = ((lean_object*)(lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__7));
lean_inc(v___y_155_);
v___x_157_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_157_, 0, v___y_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = 0;
v___x_159_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*1, v___x_158_);
v___x_160_ = l_Repr_addAppParen(v___x_159_, v_prec_132_);
return v___x_160_;
}
v___jp_161_:
{
lean_object* v___x_163_; lean_object* v___x_164_; uint8_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_163_ = ((lean_object*)(lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__9));
lean_inc(v___y_162_);
v___x_164_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_164_, 0, v___y_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = 0;
v___x_166_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set_uint8(v___x_166_, sizeof(void*)*1, v___x_165_);
v___x_167_ = l_Repr_addAppParen(v___x_166_, v_prec_132_);
return v___x_167_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___boxed(lean_object* v_x_209_, lean_object* v_prec_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = lp_oak_x2dspec_Oak_Effects_instReprFamily_repr(v_x_209_, v_prec_210_);
lean_dec(v_prec_210_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorIdx(lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_unsigned_to_nat(0u);
return v___x_215_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = lean_unsigned_to_nat(1u);
return v___x_216_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorIdx___boxed(lean_object* v_x_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = lp_oak_x2dspec_Oak_Effects_Effect_ctorIdx(v_x_217_);
lean_dec_ref(v_x_217_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorElim___redArg(lean_object* v_t_219_, lean_object* v_k_220_){
_start:
{
if (lean_obj_tag(v_t_219_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; 
v_a_221_ = lean_ctor_get(v_t_219_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v_t_219_, 1);
v___x_222_ = lean_apply_1(v_k_220_, v_a_221_);
return v___x_222_;
}
else
{
lean_object* v_a_223_; lean_object* v_a_224_; lean_object* v___x_225_; 
v_a_223_ = lean_ctor_get(v_t_219_, 0);
lean_inc(v_a_223_);
v_a_224_ = lean_ctor_get(v_t_219_, 1);
lean_inc(v_a_224_);
lean_dec_ref_known(v_t_219_, 2);
v___x_225_ = lean_apply_2(v_k_220_, v_a_223_, v_a_224_);
return v___x_225_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorElim(lean_object* v_motive_226_, lean_object* v_ctorIdx_227_, lean_object* v_t_228_, lean_object* v_h_229_, lean_object* v_k_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lp_oak_x2dspec_Oak_Effects_Effect_ctorElim___redArg(v_t_228_, v_k_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_ctorElim___boxed(lean_object* v_motive_232_, lean_object* v_ctorIdx_233_, lean_object* v_t_234_, lean_object* v_h_235_, lean_object* v_k_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = lp_oak_x2dspec_Oak_Effects_Effect_ctorElim(v_motive_232_, v_ctorIdx_233_, v_t_234_, v_h_235_, v_k_236_);
lean_dec(v_ctorIdx_233_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_broad_elim___redArg(lean_object* v_t_238_, lean_object* v_broad_239_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = lp_oak_x2dspec_Oak_Effects_Effect_ctorElim___redArg(v_t_238_, v_broad_239_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_broad_elim(lean_object* v_motive_241_, lean_object* v_t_242_, lean_object* v_h_243_, lean_object* v_broad_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lp_oak_x2dspec_Oak_Effects_Effect_ctorElim___redArg(v_t_242_, v_broad_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_scoped_elim___redArg(lean_object* v_t_246_, lean_object* v_scoped_247_){
_start:
{
lean_object* v___x_248_; 
v___x_248_ = lp_oak_x2dspec_Oak_Effects_Effect_ctorElim___redArg(v_t_246_, v_scoped_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_Effect_scoped_elim(lean_object* v_motive_249_, lean_object* v_t_250_, lean_object* v_h_251_, lean_object* v_scoped_252_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = lp_oak_x2dspec_Oak_Effects_Effect_ctorElim___redArg(v_t_250_, v_scoped_252_);
return v___x_253_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect_decEq(lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
if (lean_obj_tag(v_x_254_) == 0)
{
if (lean_obj_tag(v_x_255_) == 0)
{
lean_object* v_a_256_; lean_object* v_a_257_; uint8_t v___x_258_; 
v_a_256_ = lean_ctor_get(v_x_254_, 0);
v_a_257_ = lean_ctor_get(v_x_255_, 0);
v___x_258_ = lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily_decEq(v_a_256_, v_a_257_);
return v___x_258_;
}
else
{
uint8_t v___x_259_; 
v___x_259_ = 0;
return v___x_259_;
}
}
else
{
if (lean_obj_tag(v_x_255_) == 0)
{
uint8_t v___x_260_; 
v___x_260_ = 0;
return v___x_260_;
}
else
{
lean_object* v_a_261_; lean_object* v_a_262_; lean_object* v_a_263_; lean_object* v_a_264_; uint8_t v___x_265_; 
v_a_261_ = lean_ctor_get(v_x_254_, 0);
v_a_262_ = lean_ctor_get(v_x_254_, 1);
v_a_263_ = lean_ctor_get(v_x_255_, 0);
v_a_264_ = lean_ctor_get(v_x_255_, 1);
v___x_265_ = lp_oak_x2dspec_Oak_Effects_instDecidableEqFamily_decEq(v_a_261_, v_a_263_);
if (v___x_265_ == 0)
{
return v___x_265_;
}
else
{
uint8_t v___x_266_; 
v___x_266_ = lean_nat_dec_eq(v_a_262_, v_a_264_);
return v___x_266_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect_decEq___boxed(lean_object* v_x_267_, lean_object* v_x_268_){
_start:
{
uint8_t v_res_269_; lean_object* v_r_270_; 
v_res_269_ = lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect_decEq(v_x_267_, v_x_268_);
lean_dec_ref(v_x_268_);
lean_dec_ref(v_x_267_);
v_r_270_ = lean_box(v_res_269_);
return v_r_270_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect(lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
uint8_t v___x_273_; 
v___x_273_ = lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect_decEq(v_x_271_, v_x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect___boxed(lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
uint8_t v_res_276_; lean_object* v_r_277_; 
v_res_276_ = lp_oak_x2dspec_Oak_Effects_instDecidableEqEffect(v_x_274_, v_x_275_);
lean_dec_ref(v_x_275_);
lean_dec_ref(v_x_274_);
v_r_277_ = lean_box(v_res_276_);
return v_r_277_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr(lean_object* v_x_290_, lean_object* v_prec_291_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v_a_292_; lean_object* v___y_294_; lean_object* v___x_303_; uint8_t v___x_304_; 
v_a_292_ = lean_ctor_get(v_x_290_, 0);
lean_inc(v_a_292_);
lean_dec_ref_known(v_x_290_, 1);
v___x_303_ = lean_unsigned_to_nat(1024u);
v___x_304_ = lean_nat_dec_le(v___x_303_, v_prec_291_);
if (v___x_304_ == 0)
{
lean_object* v___x_305_; 
v___x_305_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10);
v___y_294_ = v___x_305_;
goto v___jp_293_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11);
v___y_294_ = v___x_306_;
goto v___jp_293_;
}
v___jp_293_:
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_295_ = ((lean_object*)(lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__2));
v___x_296_ = lean_unsigned_to_nat(1024u);
v___x_297_ = lp_oak_x2dspec_Oak_Effects_instReprFamily_repr(v_a_292_, v___x_296_);
v___x_298_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_298_, 0, v___x_295_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_inc(v___y_294_);
v___x_299_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_299_, 0, v___y_294_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
v___x_300_ = 0;
v___x_301_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_301_, 0, v___x_299_);
lean_ctor_set_uint8(v___x_301_, sizeof(void*)*1, v___x_300_);
v___x_302_ = l_Repr_addAppParen(v___x_301_, v_prec_291_);
return v___x_302_;
}
}
else
{
lean_object* v_a_307_; lean_object* v_a_308_; lean_object* v___x_310_; uint8_t v_isShared_311_; uint8_t v_isSharedCheck_333_; 
v_a_307_ = lean_ctor_get(v_x_290_, 0);
v_a_308_ = lean_ctor_get(v_x_290_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_333_ == 0)
{
v___x_310_ = v_x_290_;
v_isShared_311_ = v_isSharedCheck_333_;
goto v_resetjp_309_;
}
else
{
lean_inc(v_a_308_);
lean_inc(v_a_307_);
lean_dec(v_x_290_);
v___x_310_ = lean_box(0);
v_isShared_311_ = v_isSharedCheck_333_;
goto v_resetjp_309_;
}
v_resetjp_309_:
{
lean_object* v___y_313_; lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = lean_unsigned_to_nat(1024u);
v___x_330_ = lean_nat_dec_le(v___x_329_, v_prec_291_);
if (v___x_330_ == 0)
{
lean_object* v___x_331_; 
v___x_331_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__10);
v___y_313_ = v___x_331_;
goto v___jp_312_;
}
else
{
lean_object* v___x_332_; 
v___x_332_ = lean_obj_once(&lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11, &lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11_once, _init_lp_oak_x2dspec_Oak_Effects_instReprFamily_repr___closed__11);
v___y_313_ = v___x_332_;
goto v___jp_312_;
}
v___jp_312_:
{
lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_314_ = lean_box(1);
v___x_315_ = ((lean_object*)(lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___closed__5));
v___x_316_ = lean_unsigned_to_nat(1024u);
v___x_317_ = lp_oak_x2dspec_Oak_Effects_instReprFamily_repr(v_a_307_, v___x_316_);
if (v_isShared_311_ == 0)
{
lean_ctor_set_tag(v___x_310_, 5);
lean_ctor_set(v___x_310_, 1, v___x_317_);
lean_ctor_set(v___x_310_, 0, v___x_315_);
v___x_319_ = v___x_310_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_328_; 
v_reuseFailAlloc_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_328_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_328_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_328_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v___x_314_);
v___x_321_ = l_Nat_reprFast(v_a_308_);
v___x_322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___x_323_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
lean_inc(v___y_313_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___y_313_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = 0;
v___x_326_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_326_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_326_, sizeof(void*)*1, v___x_325_);
v___x_327_ = l_Repr_addAppParen(v___x_326_, v_prec_291_);
return v___x_327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Effects_instReprEffect_repr___boxed(lean_object* v_x_334_, lean_object* v_prec_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = lp_oak_x2dspec_Oak_Effects_instReprEffect_repr(v_x_334_, v_prec_335_);
lean_dec(v_prec_335_);
return v_res_336_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_Effects(uint8_t builtin) {
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
