// Lean compiler output
// Module: Oak.Slab
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
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Slab_instDecidableEqState_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instDecidableEqState_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Slab_instDecidableEqState(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instDecidableEqState___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "live"};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__3_value),((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__9_value;
static const lean_string_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "capacity"};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__11_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__12;
static const lean_string_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__13_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__14;
static lean_once_cell_t lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__15;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__16 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__16_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__13_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__17 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Slab_instReprState___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Slab_instReprState_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Slab_instReprState = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprState___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_allocate_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_allocate_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_allocate_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_allocate_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_free_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_free_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_free_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_free_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Slab_Action_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Slab_instDecidableEqAction(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instDecidableEqAction___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Oak.Slab.Action.allocate"};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Oak.Slab.Action.free"};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__3_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__4;
static lean_once_cell_t lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__5;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Slab_instReprAction___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Slab_instReprAction_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprAction___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction = (const lean_object*)&lp_oak_x2dspec_Oak_Slab_instReprAction___closed__0_value;
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Slab_instDecidableEqState_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_live_3_; lean_object* v_capacity_4_; lean_object* v_live_5_; lean_object* v_capacity_6_; uint8_t v___x_7_; 
v_live_3_ = lean_ctor_get(v_x_1_, 0);
v_capacity_4_ = lean_ctor_get(v_x_1_, 1);
v_live_5_ = lean_ctor_get(v_x_2_, 0);
v_capacity_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_nat_dec_eq(v_live_3_, v_live_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_eq(v_capacity_4_, v_capacity_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instDecidableEqState_decEq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_oak_x2dspec_Oak_Slab_instDecidableEqState_decEq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Slab_instDecidableEqState(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = lp_oak_x2dspec_Oak_Slab_instDecidableEqState_decEq(v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instDecidableEqState___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = lp_oak_x2dspec_Oak_Slab_instDecidableEqState(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(8u);
v___x_34_ = lean_nat_to_int(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(12u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = ((lean_object*)(lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__0));
v___x_45_ = lean_string_length(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_obj_once(&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__14, &lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__14_once, _init_lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__14);
v___x_47_ = lean_nat_to_int(v___x_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg(lean_object* v_x_52_){
_start:
{
lean_object* v_live_53_; lean_object* v_capacity_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_89_; 
v_live_53_ = lean_ctor_get(v_x_52_, 0);
v_capacity_54_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_89_ == 0)
{
v___x_56_ = v_x_52_;
v_isShared_57_ = v_isSharedCheck_89_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_capacity_54_);
lean_inc(v_live_53_);
lean_dec(v_x_52_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_89_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_58_ = ((lean_object*)(lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__5));
v___x_59_ = ((lean_object*)(lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__6));
v___x_60_ = lean_obj_once(&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__7);
v___x_61_ = l_Nat_reprFast(v_live_53_);
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
v___x_68_ = ((lean_object*)(lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__9));
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = lean_box(1);
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = ((lean_object*)(lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__11));
v___x_73_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_71_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set(v___x_74_, 1, v___x_58_);
v___x_75_ = lean_obj_once(&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__12, &lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__12_once, _init_lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__12);
v___x_76_ = l_Nat_reprFast(v_capacity_54_);
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
v___x_81_ = lean_obj_once(&lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__15);
v___x_82_ = ((lean_object*)(lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__16));
v___x_83_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_80_);
v___x_84_ = ((lean_object*)(lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg___closed__17));
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
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr(lean_object* v_x_90_, lean_object* v_prec_91_){
_start:
{
lean_object* v___x_92_; 
v___x_92_ = lp_oak_x2dspec_Oak_Slab_instReprState_repr___redArg(v_x_90_);
return v___x_92_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprState_repr___boxed(lean_object* v_x_93_, lean_object* v_prec_94_){
_start:
{
lean_object* v_res_95_; 
v_res_95_ = lp_oak_x2dspec_Oak_Slab_instReprState_repr(v_x_93_, v_prec_94_);
lean_dec(v_prec_94_);
return v_res_95_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorIdx(uint8_t v_x_98_){
_start:
{
if (v_x_98_ == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_unsigned_to_nat(0u);
return v___x_99_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_unsigned_to_nat(1u);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorIdx___boxed(lean_object* v_x_101_){
_start:
{
uint8_t v_x_boxed_102_; lean_object* v_res_103_; 
v_x_boxed_102_ = lean_unbox(v_x_101_);
v_res_103_ = lp_oak_x2dspec_Oak_Slab_Action_ctorIdx(v_x_boxed_102_);
return v_res_103_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_toCtorIdx(uint8_t v_x_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = lp_oak_x2dspec_Oak_Slab_Action_ctorIdx(v_x_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_toCtorIdx___boxed(lean_object* v_x_106_){
_start:
{
uint8_t v_x_4__boxed_107_; lean_object* v_res_108_; 
v_x_4__boxed_107_ = lean_unbox(v_x_106_);
v_res_108_ = lp_oak_x2dspec_Oak_Slab_Action_toCtorIdx(v_x_4__boxed_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorElim___redArg(lean_object* v_k_109_){
_start:
{
lean_inc(v_k_109_);
return v_k_109_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorElim___redArg___boxed(lean_object* v_k_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = lp_oak_x2dspec_Oak_Slab_Action_ctorElim___redArg(v_k_110_);
lean_dec(v_k_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorElim(lean_object* v_motive_112_, lean_object* v_ctorIdx_113_, uint8_t v_t_114_, lean_object* v_h_115_, lean_object* v_k_116_){
_start:
{
lean_inc(v_k_116_);
return v_k_116_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ctorElim___boxed(lean_object* v_motive_117_, lean_object* v_ctorIdx_118_, lean_object* v_t_119_, lean_object* v_h_120_, lean_object* v_k_121_){
_start:
{
uint8_t v_t_boxed_122_; lean_object* v_res_123_; 
v_t_boxed_122_ = lean_unbox(v_t_119_);
v_res_123_ = lp_oak_x2dspec_Oak_Slab_Action_ctorElim(v_motive_117_, v_ctorIdx_118_, v_t_boxed_122_, v_h_120_, v_k_121_);
lean_dec(v_k_121_);
lean_dec(v_ctorIdx_118_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_allocate_elim___redArg(lean_object* v_allocate_124_){
_start:
{
lean_inc(v_allocate_124_);
return v_allocate_124_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_allocate_elim___redArg___boxed(lean_object* v_allocate_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = lp_oak_x2dspec_Oak_Slab_Action_allocate_elim___redArg(v_allocate_125_);
lean_dec(v_allocate_125_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_allocate_elim(lean_object* v_motive_127_, uint8_t v_t_128_, lean_object* v_h_129_, lean_object* v_allocate_130_){
_start:
{
lean_inc(v_allocate_130_);
return v_allocate_130_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_allocate_elim___boxed(lean_object* v_motive_131_, lean_object* v_t_132_, lean_object* v_h_133_, lean_object* v_allocate_134_){
_start:
{
uint8_t v_t_boxed_135_; lean_object* v_res_136_; 
v_t_boxed_135_ = lean_unbox(v_t_132_);
v_res_136_ = lp_oak_x2dspec_Oak_Slab_Action_allocate_elim(v_motive_131_, v_t_boxed_135_, v_h_133_, v_allocate_134_);
lean_dec(v_allocate_134_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_free_elim___redArg(lean_object* v_free_137_){
_start:
{
lean_inc(v_free_137_);
return v_free_137_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_free_elim___redArg___boxed(lean_object* v_free_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = lp_oak_x2dspec_Oak_Slab_Action_free_elim___redArg(v_free_138_);
lean_dec(v_free_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_free_elim(lean_object* v_motive_140_, uint8_t v_t_141_, lean_object* v_h_142_, lean_object* v_free_143_){
_start:
{
lean_inc(v_free_143_);
return v_free_143_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_free_elim___boxed(lean_object* v_motive_144_, lean_object* v_t_145_, lean_object* v_h_146_, lean_object* v_free_147_){
_start:
{
uint8_t v_t_boxed_148_; lean_object* v_res_149_; 
v_t_boxed_148_ = lean_unbox(v_t_145_);
v_res_149_ = lp_oak_x2dspec_Oak_Slab_Action_free_elim(v_motive_144_, v_t_boxed_148_, v_h_146_, v_free_147_);
lean_dec(v_free_147_);
return v_res_149_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Slab_Action_ofNat(lean_object* v_n_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = lean_unsigned_to_nat(0u);
v___x_152_ = lean_nat_dec_le(v_n_150_, v___x_151_);
if (v___x_152_ == 0)
{
uint8_t v___x_153_; 
v___x_153_ = 1;
return v___x_153_;
}
else
{
uint8_t v___x_154_; 
v___x_154_ = 0;
return v___x_154_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_Action_ofNat___boxed(lean_object* v_n_155_){
_start:
{
uint8_t v_res_156_; lean_object* v_r_157_; 
v_res_156_ = lp_oak_x2dspec_Oak_Slab_Action_ofNat(v_n_155_);
lean_dec(v_n_155_);
v_r_157_ = lean_box(v_res_156_);
return v_r_157_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Slab_instDecidableEqAction(uint8_t v_x_158_, uint8_t v_y_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v___x_160_ = lp_oak_x2dspec_Oak_Slab_Action_ctorIdx(v_x_158_);
v___x_161_ = lp_oak_x2dspec_Oak_Slab_Action_ctorIdx(v_y_159_);
v___x_162_ = lean_nat_dec_eq(v___x_160_, v___x_161_);
lean_dec(v___x_161_);
lean_dec(v___x_160_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instDecidableEqAction___boxed(lean_object* v_x_163_, lean_object* v_y_164_){
_start:
{
uint8_t v_x_13__boxed_165_; uint8_t v_y_14__boxed_166_; uint8_t v_res_167_; lean_object* v_r_168_; 
v_x_13__boxed_165_ = lean_unbox(v_x_163_);
v_y_14__boxed_166_ = lean_unbox(v_y_164_);
v_res_167_ = lp_oak_x2dspec_Oak_Slab_instDecidableEqAction(v_x_13__boxed_165_, v_y_14__boxed_166_);
v_r_168_ = lean_box(v_res_167_);
return v_r_168_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__4(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = lean_unsigned_to_nat(2u);
v___x_176_ = lean_nat_to_int(v___x_175_);
return v___x_176_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__5(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = lean_unsigned_to_nat(1u);
v___x_178_ = lean_nat_to_int(v___x_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr(uint8_t v_x_179_, lean_object* v_prec_180_){
_start:
{
lean_object* v___y_182_; lean_object* v___y_189_; 
if (v_x_179_ == 0)
{
lean_object* v___x_195_; uint8_t v___x_196_; 
v___x_195_ = lean_unsigned_to_nat(1024u);
v___x_196_ = lean_nat_dec_le(v___x_195_, v_prec_180_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
v___x_197_ = lean_obj_once(&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__4, &lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__4);
v___y_182_ = v___x_197_;
goto v___jp_181_;
}
else
{
lean_object* v___x_198_; 
v___x_198_ = lean_obj_once(&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__5, &lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__5_once, _init_lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__5);
v___y_182_ = v___x_198_;
goto v___jp_181_;
}
}
else
{
lean_object* v___x_199_; uint8_t v___x_200_; 
v___x_199_ = lean_unsigned_to_nat(1024u);
v___x_200_ = lean_nat_dec_le(v___x_199_, v_prec_180_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_obj_once(&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__4, &lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__4);
v___y_189_ = v___x_201_;
goto v___jp_188_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_obj_once(&lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__5, &lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__5_once, _init_lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__5);
v___y_189_ = v___x_202_;
goto v___jp_188_;
}
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_183_ = ((lean_object*)(lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__1));
lean_inc(v___y_182_);
v___x_184_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_184_, 0, v___y_182_);
lean_ctor_set(v___x_184_, 1, v___x_183_);
v___x_185_ = 0;
v___x_186_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set_uint8(v___x_186_, sizeof(void*)*1, v___x_185_);
v___x_187_ = l_Repr_addAppParen(v___x_186_, v_prec_180_);
return v___x_187_;
}
v___jp_188_:
{
lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_190_ = ((lean_object*)(lp_oak_x2dspec_Oak_Slab_instReprAction_repr___closed__3));
lean_inc(v___y_189_);
v___x_191_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_191_, 0, v___y_189_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = 0;
v___x_193_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set_uint8(v___x_193_, sizeof(void*)*1, v___x_192_);
v___x_194_ = l_Repr_addAppParen(v___x_193_, v_prec_180_);
return v___x_194_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Slab_instReprAction_repr___boxed(lean_object* v_x_203_, lean_object* v_prec_204_){
_start:
{
uint8_t v_x_121__boxed_205_; lean_object* v_res_206_; 
v_x_121__boxed_205_ = lean_unbox(v_x_203_);
v_res_206_ = lp_oak_x2dspec_Oak_Slab_instReprAction_repr(v_x_121__boxed_205_, v_prec_204_);
lean_dec(v_prec_204_);
return v_res_206_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_Slab(uint8_t builtin) {
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
