// Lean compiler output
// Module: Oak.Borrowing
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
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_free_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_free_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_shared_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_shared_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_unique_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_unique_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Oak.Borrowing.State.free"};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Oak.Borrowing.State.unique"};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__3_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4;
static lean_once_cell_t lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5;
static const lean_string_object lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "Oak.Borrowing.State.shared"};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__6_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__6_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__7 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__7_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__7_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__8_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Borrowing_instReprState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprState___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Borrowing_Action_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Borrowing_instDecidableEqAction(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instDecidableEqAction___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Oak.Borrowing.Action.acquireRead"};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Oak.Borrowing.Action.acquireWrite"};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Oak.Borrowing.Action.releaseRead"};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__5_value;
static const lean_string_object lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "Oak.Borrowing.Action.releaseWrite"};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__6_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__6_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__7 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__7_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Borrowing_instReprAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction = (const lean_object*)&lp_oak_x2dspec_Oak_Borrowing_instReprAction___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_instReprState_repr_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_instReprState_repr_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_HasReaders_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_HasReaders_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_HasWriter_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_HasWriter_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorIdx(lean_object* v_x_1_){
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
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_oak_x2dspec_Oak_Borrowing_State_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 1)
{
lean_object* v_a_9_; lean_object* v___x_10_; 
v_a_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_a_9_);
lean_dec_ref_known(v_t_7_, 1);
v___x_10_ = lean_apply_1(v_k_8_, v_a_9_);
return v___x_10_;
}
else
{
lean_dec(v_t_7_);
return v_k_8_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_oak_x2dspec_Oak_Borrowing_State_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_free_elim___redArg(lean_object* v_t_23_, lean_object* v_free_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___redArg(v_t_23_, v_free_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_free_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_free_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___redArg(v_t_27_, v_free_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_shared_elim___redArg(lean_object* v_t_31_, lean_object* v_shared_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___redArg(v_t_31_, v_shared_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_shared_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_shared_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___redArg(v_t_35_, v_shared_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_unique_elim___redArg(lean_object* v_t_39_, lean_object* v_unique_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___redArg(v_t_39_, v_unique_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_State_unique_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_unique_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_oak_x2dspec_Oak_Borrowing_State_ctorElim___redArg(v_t_43_, v_unique_45_);
return v___x_46_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState_decEq(lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 0:
{
if (lean_obj_tag(v_x_48_) == 0)
{
uint8_t v___x_49_; 
v___x_49_ = 1;
return v___x_49_;
}
else
{
uint8_t v___x_50_; 
v___x_50_ = 0;
return v___x_50_;
}
}
case 1:
{
lean_object* v_a_51_; uint8_t v___x_52_; 
v_a_51_ = lean_ctor_get(v_x_47_, 0);
v___x_52_ = 0;
if (lean_obj_tag(v_x_48_) == 1)
{
lean_object* v_a_53_; uint8_t v___x_54_; 
v_a_53_ = lean_ctor_get(v_x_48_, 0);
v___x_54_ = lean_nat_dec_eq(v_a_51_, v_a_53_);
if (v___x_54_ == 0)
{
return v___x_52_;
}
else
{
return v___x_54_;
}
}
else
{
return v___x_52_;
}
}
default: 
{
if (lean_obj_tag(v_x_48_) == 2)
{
uint8_t v___x_55_; 
v___x_55_ = 1;
return v___x_55_;
}
else
{
uint8_t v___x_56_; 
v___x_56_ = 0;
return v___x_56_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState_decEq___boxed(lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState_decEq(v_x_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec(v_x_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState_decEq(v_x_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState___boxed(lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = lp_oak_x2dspec_Oak_Borrowing_instDecidableEqState(v_x_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec(v_x_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_unsigned_to_nat(2u);
v___x_75_ = lean_nat_to_int(v___x_74_);
return v___x_75_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5(void){
_start:
{
lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_76_ = lean_unsigned_to_nat(1u);
v___x_77_ = lean_nat_to_int(v___x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr(lean_object* v_x_84_, lean_object* v_prec_85_){
_start:
{
lean_object* v___y_87_; lean_object* v___y_94_; 
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
lean_object* v___x_100_; uint8_t v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1024u);
v___x_101_ = lean_nat_dec_le(v___x_100_, v_prec_85_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4);
v___y_87_ = v___x_102_;
goto v___jp_86_;
}
else
{
lean_object* v___x_103_; 
v___x_103_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5);
v___y_87_ = v___x_103_;
goto v___jp_86_;
}
}
case 1:
{
lean_object* v_a_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_124_; 
v_a_104_ = lean_ctor_get(v_x_84_, 0);
v_isSharedCheck_124_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_124_ == 0)
{
v___x_106_ = v_x_84_;
v_isShared_107_ = v_isSharedCheck_124_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_a_104_);
lean_dec(v_x_84_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_124_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___y_109_; lean_object* v___x_120_; uint8_t v___x_121_; 
v___x_120_ = lean_unsigned_to_nat(1024u);
v___x_121_ = lean_nat_dec_le(v___x_120_, v_prec_85_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; 
v___x_122_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4);
v___y_109_ = v___x_122_;
goto v___jp_108_;
}
else
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5);
v___y_109_ = v___x_123_;
goto v___jp_108_;
}
v___jp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_110_ = ((lean_object*)(lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__8));
v___x_111_ = l_Nat_reprFast(v_a_104_);
if (v_isShared_107_ == 0)
{
lean_ctor_set_tag(v___x_106_, 3);
lean_ctor_set(v___x_106_, 0, v___x_111_);
v___x_113_ = v___x_106_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_111_);
v___x_113_ = v_reuseFailAlloc_119_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; uint8_t v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_114_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_110_);
lean_ctor_set(v___x_114_, 1, v___x_113_);
lean_inc(v___y_109_);
v___x_115_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_115_, 0, v___y_109_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = 0;
v___x_117_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_117_, 0, v___x_115_);
lean_ctor_set_uint8(v___x_117_, sizeof(void*)*1, v___x_116_);
v___x_118_ = l_Repr_addAppParen(v___x_117_, v_prec_85_);
return v___x_118_;
}
}
}
}
default: 
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(1024u);
v___x_126_ = lean_nat_dec_le(v___x_125_, v_prec_85_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4);
v___y_94_ = v___x_127_;
goto v___jp_93_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5);
v___y_94_ = v___x_128_;
goto v___jp_93_;
}
}
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__1));
lean_inc(v___y_87_);
v___x_89_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_89_, 0, v___y_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = 0;
v___x_91_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set_uint8(v___x_91_, sizeof(void*)*1, v___x_90_);
v___x_92_ = l_Repr_addAppParen(v___x_91_, v_prec_85_);
return v___x_92_;
}
v___jp_93_:
{
lean_object* v___x_95_; lean_object* v___x_96_; uint8_t v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_95_ = ((lean_object*)(lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__3));
lean_inc(v___y_94_);
v___x_96_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_96_, 0, v___y_94_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = 0;
v___x_98_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_98_, 0, v___x_96_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*1, v___x_97_);
v___x_99_ = l_Repr_addAppParen(v___x_98_, v_prec_85_);
return v___x_99_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___boxed(lean_object* v_x_129_, lean_object* v_prec_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_oak_x2dspec_Oak_Borrowing_instReprState_repr(v_x_129_, v_prec_130_);
lean_dec(v_prec_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorIdx(uint8_t v_x_134_){
_start:
{
switch(v_x_134_)
{
case 0:
{
lean_object* v___x_135_; 
v___x_135_ = lean_unsigned_to_nat(0u);
return v___x_135_;
}
case 1:
{
lean_object* v___x_136_; 
v___x_136_ = lean_unsigned_to_nat(1u);
return v___x_136_;
}
case 2:
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(2u);
return v___x_137_;
}
default: 
{
lean_object* v___x_138_; 
v___x_138_ = lean_unsigned_to_nat(3u);
return v___x_138_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorIdx___boxed(lean_object* v_x_139_){
_start:
{
uint8_t v_x_boxed_140_; lean_object* v_res_141_; 
v_x_boxed_140_ = lean_unbox(v_x_139_);
v_res_141_ = lp_oak_x2dspec_Oak_Borrowing_Action_ctorIdx(v_x_boxed_140_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_toCtorIdx(uint8_t v_x_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lp_oak_x2dspec_Oak_Borrowing_Action_ctorIdx(v_x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_toCtorIdx___boxed(lean_object* v_x_144_){
_start:
{
uint8_t v_x_4__boxed_145_; lean_object* v_res_146_; 
v_x_4__boxed_145_ = lean_unbox(v_x_144_);
v_res_146_ = lp_oak_x2dspec_Oak_Borrowing_Action_toCtorIdx(v_x_4__boxed_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim___redArg(lean_object* v_k_147_){
_start:
{
lean_inc(v_k_147_);
return v_k_147_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim___redArg___boxed(lean_object* v_k_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim___redArg(v_k_148_);
lean_dec(v_k_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim(lean_object* v_motive_150_, lean_object* v_ctorIdx_151_, uint8_t v_t_152_, lean_object* v_h_153_, lean_object* v_k_154_){
_start:
{
lean_inc(v_k_154_);
return v_k_154_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim___boxed(lean_object* v_motive_155_, lean_object* v_ctorIdx_156_, lean_object* v_t_157_, lean_object* v_h_158_, lean_object* v_k_159_){
_start:
{
uint8_t v_t_boxed_160_; lean_object* v_res_161_; 
v_t_boxed_160_ = lean_unbox(v_t_157_);
v_res_161_ = lp_oak_x2dspec_Oak_Borrowing_Action_ctorElim(v_motive_155_, v_ctorIdx_156_, v_t_boxed_160_, v_h_158_, v_k_159_);
lean_dec(v_k_159_);
lean_dec(v_ctorIdx_156_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim___redArg(lean_object* v_acquireRead_162_){
_start:
{
lean_inc(v_acquireRead_162_);
return v_acquireRead_162_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim___redArg___boxed(lean_object* v_acquireRead_163_){
_start:
{
lean_object* v_res_164_; 
v_res_164_ = lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim___redArg(v_acquireRead_163_);
lean_dec(v_acquireRead_163_);
return v_res_164_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim(lean_object* v_motive_165_, uint8_t v_t_166_, lean_object* v_h_167_, lean_object* v_acquireRead_168_){
_start:
{
lean_inc(v_acquireRead_168_);
return v_acquireRead_168_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim___boxed(lean_object* v_motive_169_, lean_object* v_t_170_, lean_object* v_h_171_, lean_object* v_acquireRead_172_){
_start:
{
uint8_t v_t_boxed_173_; lean_object* v_res_174_; 
v_t_boxed_173_ = lean_unbox(v_t_170_);
v_res_174_ = lp_oak_x2dspec_Oak_Borrowing_Action_acquireRead_elim(v_motive_169_, v_t_boxed_173_, v_h_171_, v_acquireRead_172_);
lean_dec(v_acquireRead_172_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim___redArg(lean_object* v_acquireWrite_175_){
_start:
{
lean_inc(v_acquireWrite_175_);
return v_acquireWrite_175_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim___redArg___boxed(lean_object* v_acquireWrite_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim___redArg(v_acquireWrite_176_);
lean_dec(v_acquireWrite_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim(lean_object* v_motive_178_, uint8_t v_t_179_, lean_object* v_h_180_, lean_object* v_acquireWrite_181_){
_start:
{
lean_inc(v_acquireWrite_181_);
return v_acquireWrite_181_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim___boxed(lean_object* v_motive_182_, lean_object* v_t_183_, lean_object* v_h_184_, lean_object* v_acquireWrite_185_){
_start:
{
uint8_t v_t_boxed_186_; lean_object* v_res_187_; 
v_t_boxed_186_ = lean_unbox(v_t_183_);
v_res_187_ = lp_oak_x2dspec_Oak_Borrowing_Action_acquireWrite_elim(v_motive_182_, v_t_boxed_186_, v_h_184_, v_acquireWrite_185_);
lean_dec(v_acquireWrite_185_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim___redArg(lean_object* v_releaseRead_188_){
_start:
{
lean_inc(v_releaseRead_188_);
return v_releaseRead_188_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim___redArg___boxed(lean_object* v_releaseRead_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim___redArg(v_releaseRead_189_);
lean_dec(v_releaseRead_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim(lean_object* v_motive_191_, uint8_t v_t_192_, lean_object* v_h_193_, lean_object* v_releaseRead_194_){
_start:
{
lean_inc(v_releaseRead_194_);
return v_releaseRead_194_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim___boxed(lean_object* v_motive_195_, lean_object* v_t_196_, lean_object* v_h_197_, lean_object* v_releaseRead_198_){
_start:
{
uint8_t v_t_boxed_199_; lean_object* v_res_200_; 
v_t_boxed_199_ = lean_unbox(v_t_196_);
v_res_200_ = lp_oak_x2dspec_Oak_Borrowing_Action_releaseRead_elim(v_motive_195_, v_t_boxed_199_, v_h_197_, v_releaseRead_198_);
lean_dec(v_releaseRead_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim___redArg(lean_object* v_releaseWrite_201_){
_start:
{
lean_inc(v_releaseWrite_201_);
return v_releaseWrite_201_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim___redArg___boxed(lean_object* v_releaseWrite_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim___redArg(v_releaseWrite_202_);
lean_dec(v_releaseWrite_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim(lean_object* v_motive_204_, uint8_t v_t_205_, lean_object* v_h_206_, lean_object* v_releaseWrite_207_){
_start:
{
lean_inc(v_releaseWrite_207_);
return v_releaseWrite_207_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim___boxed(lean_object* v_motive_208_, lean_object* v_t_209_, lean_object* v_h_210_, lean_object* v_releaseWrite_211_){
_start:
{
uint8_t v_t_boxed_212_; lean_object* v_res_213_; 
v_t_boxed_212_ = lean_unbox(v_t_209_);
v_res_213_ = lp_oak_x2dspec_Oak_Borrowing_Action_releaseWrite_elim(v_motive_208_, v_t_boxed_212_, v_h_210_, v_releaseWrite_211_);
lean_dec(v_releaseWrite_211_);
return v_res_213_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Borrowing_Action_ofNat(lean_object* v_n_214_){
_start:
{
lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_215_ = lean_unsigned_to_nat(1u);
v___x_216_ = lean_nat_dec_le(v_n_214_, v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; uint8_t v___x_218_; 
v___x_217_ = lean_unsigned_to_nat(2u);
v___x_218_ = lean_nat_dec_le(v_n_214_, v___x_217_);
if (v___x_218_ == 0)
{
uint8_t v___x_219_; 
v___x_219_ = 3;
return v___x_219_;
}
else
{
uint8_t v___x_220_; 
v___x_220_ = 2;
return v___x_220_;
}
}
else
{
lean_object* v___x_221_; uint8_t v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_nat_dec_le(v_n_214_, v___x_221_);
if (v___x_222_ == 0)
{
uint8_t v___x_223_; 
v___x_223_ = 1;
return v___x_223_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = 0;
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_Action_ofNat___boxed(lean_object* v_n_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = lp_oak_x2dspec_Oak_Borrowing_Action_ofNat(v_n_225_);
lean_dec(v_n_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Borrowing_instDecidableEqAction(uint8_t v_x_228_, uint8_t v_y_229_){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; uint8_t v___x_232_; 
v___x_230_ = lp_oak_x2dspec_Oak_Borrowing_Action_ctorIdx(v_x_228_);
v___x_231_ = lp_oak_x2dspec_Oak_Borrowing_Action_ctorIdx(v_y_229_);
v___x_232_ = lean_nat_dec_eq(v___x_230_, v___x_231_);
lean_dec(v___x_231_);
lean_dec(v___x_230_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instDecidableEqAction___boxed(lean_object* v_x_233_, lean_object* v_y_234_){
_start:
{
uint8_t v_x_13__boxed_235_; uint8_t v_y_14__boxed_236_; uint8_t v_res_237_; lean_object* v_r_238_; 
v_x_13__boxed_235_ = lean_unbox(v_x_233_);
v_y_14__boxed_236_ = lean_unbox(v_y_234_);
v_res_237_ = lp_oak_x2dspec_Oak_Borrowing_instDecidableEqAction(v_x_13__boxed_235_, v_y_14__boxed_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr(uint8_t v_x_251_, lean_object* v_prec_252_){
_start:
{
lean_object* v___y_254_; lean_object* v___y_261_; lean_object* v___y_268_; lean_object* v___y_275_; 
switch(v_x_251_)
{
case 0:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(1024u);
v___x_282_ = lean_nat_dec_le(v___x_281_, v_prec_252_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; 
v___x_283_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4);
v___y_254_ = v___x_283_;
goto v___jp_253_;
}
else
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5);
v___y_254_ = v___x_284_;
goto v___jp_253_;
}
}
case 1:
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_unsigned_to_nat(1024u);
v___x_286_ = lean_nat_dec_le(v___x_285_, v_prec_252_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; 
v___x_287_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4);
v___y_261_ = v___x_287_;
goto v___jp_260_;
}
else
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5);
v___y_261_ = v___x_288_;
goto v___jp_260_;
}
}
case 2:
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1024u);
v___x_290_ = lean_nat_dec_le(v___x_289_, v_prec_252_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; 
v___x_291_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4);
v___y_268_ = v___x_291_;
goto v___jp_267_;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5);
v___y_268_ = v___x_292_;
goto v___jp_267_;
}
}
default: 
{
lean_object* v___x_293_; uint8_t v___x_294_; 
v___x_293_ = lean_unsigned_to_nat(1024u);
v___x_294_ = lean_nat_dec_le(v___x_293_, v_prec_252_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; 
v___x_295_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__4);
v___y_275_ = v___x_295_;
goto v___jp_274_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_obj_once(&lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5, &lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5_once, _init_lp_oak_x2dspec_Oak_Borrowing_instReprState_repr___closed__5);
v___y_275_ = v___x_296_;
goto v___jp_274_;
}
}
}
v___jp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_255_ = ((lean_object*)(lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__1));
lean_inc(v___y_254_);
v___x_256_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_256_, 0, v___y_254_);
lean_ctor_set(v___x_256_, 1, v___x_255_);
v___x_257_ = 0;
v___x_258_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set_uint8(v___x_258_, sizeof(void*)*1, v___x_257_);
v___x_259_ = l_Repr_addAppParen(v___x_258_, v_prec_252_);
return v___x_259_;
}
v___jp_260_:
{
lean_object* v___x_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_262_ = ((lean_object*)(lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__3));
lean_inc(v___y_261_);
v___x_263_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_263_, 0, v___y_261_);
lean_ctor_set(v___x_263_, 1, v___x_262_);
v___x_264_ = 0;
v___x_265_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set_uint8(v___x_265_, sizeof(void*)*1, v___x_264_);
v___x_266_ = l_Repr_addAppParen(v___x_265_, v_prec_252_);
return v___x_266_;
}
v___jp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; uint8_t v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_269_ = ((lean_object*)(lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__5));
lean_inc(v___y_268_);
v___x_270_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_270_, 0, v___y_268_);
lean_ctor_set(v___x_270_, 1, v___x_269_);
v___x_271_ = 0;
v___x_272_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set_uint8(v___x_272_, sizeof(void*)*1, v___x_271_);
v___x_273_ = l_Repr_addAppParen(v___x_272_, v_prec_252_);
return v___x_273_;
}
v___jp_274_:
{
lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_276_ = ((lean_object*)(lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___closed__7));
lean_inc(v___y_275_);
v___x_277_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_277_, 0, v___y_275_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = 0;
v___x_279_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_279_, 0, v___x_277_);
lean_ctor_set_uint8(v___x_279_, sizeof(void*)*1, v___x_278_);
v___x_280_ = l_Repr_addAppParen(v___x_279_, v_prec_252_);
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr___boxed(lean_object* v_x_297_, lean_object* v_prec_298_){
_start:
{
uint8_t v_x_229__boxed_299_; lean_object* v_res_300_; 
v_x_229__boxed_299_ = lean_unbox(v_x_297_);
v_res_300_ = lp_oak_x2dspec_Oak_Borrowing_instReprAction_repr(v_x_229__boxed_299_, v_prec_298_);
lean_dec(v_prec_298_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_instReprState_repr_match__1_splitter___redArg(lean_object* v_x_303_, lean_object* v_h__1_304_, lean_object* v_h__2_305_, lean_object* v_h__3_306_){
_start:
{
switch(lean_obj_tag(v_x_303_))
{
case 0:
{
lean_object* v___x_307_; lean_object* v___x_308_; 
lean_dec(v_h__3_306_);
lean_dec(v_h__2_305_);
v___x_307_ = lean_box(0);
v___x_308_ = lean_apply_1(v_h__1_304_, v___x_307_);
return v___x_308_;
}
case 1:
{
lean_object* v_a_309_; lean_object* v___x_310_; 
lean_dec(v_h__3_306_);
lean_dec(v_h__1_304_);
v_a_309_ = lean_ctor_get(v_x_303_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v_x_303_, 1);
v___x_310_ = lean_apply_1(v_h__2_305_, v_a_309_);
return v___x_310_;
}
default: 
{
lean_object* v___x_311_; lean_object* v___x_312_; 
lean_dec(v_h__2_305_);
lean_dec(v_h__1_304_);
v___x_311_ = lean_box(0);
v___x_312_ = lean_apply_1(v_h__3_306_, v___x_311_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_instReprState_repr_match__1_splitter(lean_object* v_motive_313_, lean_object* v_x_314_, lean_object* v_h__1_315_, lean_object* v_h__2_316_, lean_object* v_h__3_317_){
_start:
{
switch(lean_obj_tag(v_x_314_))
{
case 0:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec(v_h__3_317_);
lean_dec(v_h__2_316_);
v___x_318_ = lean_box(0);
v___x_319_ = lean_apply_1(v_h__1_315_, v___x_318_);
return v___x_319_;
}
case 1:
{
lean_object* v_a_320_; lean_object* v___x_321_; 
lean_dec(v_h__3_317_);
lean_dec(v_h__1_315_);
v_a_320_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v_x_314_, 1);
v___x_321_ = lean_apply_1(v_h__2_316_, v_a_320_);
return v___x_321_;
}
default: 
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v_h__2_316_);
lean_dec(v_h__1_315_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_apply_1(v_h__3_317_, v___x_322_);
return v___x_323_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_HasReaders_match__1_splitter___redArg(lean_object* v_x_324_, lean_object* v_h__1_325_, lean_object* v_h__2_326_){
_start:
{
if (lean_obj_tag(v_x_324_) == 1)
{
lean_object* v_a_327_; lean_object* v___x_328_; 
lean_dec(v_h__2_326_);
v_a_327_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v_x_324_, 1);
v___x_328_ = lean_apply_1(v_h__1_325_, v_a_327_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; 
lean_dec(v_h__1_325_);
v___x_329_ = lean_apply_2(v_h__2_326_, v_x_324_, lean_box(0));
return v___x_329_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_HasReaders_match__1_splitter(lean_object* v_motive_330_, lean_object* v_x_331_, lean_object* v_h__1_332_, lean_object* v_h__2_333_){
_start:
{
if (lean_obj_tag(v_x_331_) == 1)
{
lean_object* v_a_334_; lean_object* v___x_335_; 
lean_dec(v_h__2_333_);
v_a_334_ = lean_ctor_get(v_x_331_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v_x_331_, 1);
v___x_335_ = lean_apply_1(v_h__1_332_, v_a_334_);
return v___x_335_;
}
else
{
lean_object* v___x_336_; 
lean_dec(v_h__1_332_);
v___x_336_ = lean_apply_2(v_h__2_333_, v_x_331_, lean_box(0));
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_HasWriter_match__1_splitter___redArg(lean_object* v_x_337_, lean_object* v_h__1_338_, lean_object* v_h__2_339_){
_start:
{
if (lean_obj_tag(v_x_337_) == 2)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v_h__2_339_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_apply_1(v_h__1_338_, v___x_340_);
return v___x_341_;
}
else
{
lean_object* v___x_342_; 
lean_dec(v_h__1_338_);
v___x_342_ = lean_apply_2(v_h__2_339_, v_x_337_, lean_box(0));
return v___x_342_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Borrowing_0__Oak_Borrowing_HasWriter_match__1_splitter(lean_object* v_motive_343_, lean_object* v_x_344_, lean_object* v_h__1_345_, lean_object* v_h__2_346_){
_start:
{
if (lean_obj_tag(v_x_344_) == 2)
{
lean_object* v___x_347_; lean_object* v___x_348_; 
lean_dec(v_h__2_346_);
v___x_347_ = lean_box(0);
v___x_348_ = lean_apply_1(v_h__1_345_, v___x_347_);
return v___x_348_;
}
else
{
lean_object* v___x_349_; 
lean_dec(v_h__1_345_);
v___x_349_ = lean_apply_2(v_h__2_346_, v_x_344_, lean_box(0));
return v___x_349_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_Borrowing(uint8_t builtin) {
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
