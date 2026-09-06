// Lean compiler output
// Module: Oak.Layout
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
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_List_replicateTR___redArg(lean_object*, lean_object*);
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_source_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_source_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_push_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_push_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_pop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_pop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Oak.Layout.Event.push"};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Oak.Layout.Event.pop"};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Oak.Layout.Event.source"};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7;
static lean_once_cell_t lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Layout_instReprEvent___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprEvent___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_source_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_source_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_push_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_push_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_pop_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_pop_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Layout_instDecidableEqToken_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instDecidableEqToken_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Layout_instDecidableEqToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instDecidableEqToken___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Oak.Layout.Token.push"};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "Oak.Layout.Token.pop"};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Oak.Layout.Token.source"};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__5_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__6_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Layout_instReprToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Layout_instReprToken_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken = (const lean_object*)&lp_oak_x2dspec_Oak_Layout_instReprToken___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_sourceValues(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_sourceEvents(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_opens(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_opens___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_closes(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_closes___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_renderFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_finishTokens(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_sourceValues_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_sourceValues_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_opens_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_opens_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_closes_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_closes_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_renderFrom_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_renderFrom_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_renderFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_renderFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_sourceEvents_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_sourceEvents_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = lp_oak_x2dspec_Oak_Layout_Event_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 0)
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
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = lp_oak_x2dspec_Oak_Layout_Event_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = lp_oak_x2dspec_Oak_Layout_Event_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_source_elim___redArg(lean_object* v_t_23_, lean_object* v_source_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = lp_oak_x2dspec_Oak_Layout_Event_ctorElim___redArg(v_t_23_, v_source_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_source_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_source_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = lp_oak_x2dspec_Oak_Layout_Event_ctorElim___redArg(v_t_27_, v_source_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_push_elim___redArg(lean_object* v_t_31_, lean_object* v_push_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lp_oak_x2dspec_Oak_Layout_Event_ctorElim___redArg(v_t_31_, v_push_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_push_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_push_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = lp_oak_x2dspec_Oak_Layout_Event_ctorElim___redArg(v_t_35_, v_push_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_pop_elim___redArg(lean_object* v_t_39_, lean_object* v_pop_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = lp_oak_x2dspec_Oak_Layout_Event_ctorElim___redArg(v_t_39_, v_pop_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Event_pop_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_pop_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lp_oak_x2dspec_Oak_Layout_Event_ctorElim___redArg(v_t_43_, v_pop_45_);
return v___x_46_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent_decEq(lean_object* v_x_47_, lean_object* v_x_48_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 0:
{
lean_object* v_a_49_; uint8_t v___x_50_; 
v_a_49_ = lean_ctor_get(v_x_47_, 0);
v___x_50_ = 0;
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v_a_51_; uint8_t v___x_52_; 
v_a_51_ = lean_ctor_get(v_x_48_, 0);
v___x_52_ = lean_nat_dec_eq(v_a_49_, v_a_51_);
if (v___x_52_ == 0)
{
return v___x_50_;
}
else
{
return v___x_52_;
}
}
else
{
return v___x_50_;
}
}
case 1:
{
if (lean_obj_tag(v_x_48_) == 1)
{
uint8_t v___x_53_; 
v___x_53_ = 1;
return v___x_53_;
}
else
{
uint8_t v___x_54_; 
v___x_54_ = 0;
return v___x_54_;
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
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent_decEq___boxed(lean_object* v_x_57_, lean_object* v_x_58_){
_start:
{
uint8_t v_res_59_; lean_object* v_r_60_; 
v_res_59_ = lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent_decEq(v_x_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec(v_x_57_);
v_r_60_ = lean_box(v_res_59_);
return v_r_60_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent(lean_object* v_x_61_, lean_object* v_x_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent_decEq(v_x_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent___boxed(lean_object* v_x_64_, lean_object* v_x_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = lp_oak_x2dspec_Oak_Layout_instDecidableEqEvent(v_x_64_, v_x_65_);
lean_dec(v_x_65_);
lean_dec(v_x_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7(void){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = lean_unsigned_to_nat(2u);
v___x_81_ = lean_nat_to_int(v___x_80_);
return v___x_81_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_unsigned_to_nat(1u);
v___x_83_ = lean_nat_to_int(v___x_82_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr(lean_object* v_x_84_, lean_object* v_prec_85_){
_start:
{
lean_object* v___y_87_; lean_object* v___y_94_; 
switch(lean_obj_tag(v_x_84_))
{
case 0:
{
lean_object* v_a_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_120_; 
v_a_100_ = lean_ctor_get(v_x_84_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_120_ == 0)
{
v___x_102_ = v_x_84_;
v_isShared_103_ = v_isSharedCheck_120_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_a_100_);
lean_dec(v_x_84_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_120_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___y_105_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_116_ = lean_unsigned_to_nat(1024u);
v___x_117_ = lean_nat_dec_le(v___x_116_, v_prec_85_);
if (v___x_117_ == 0)
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7);
v___y_105_ = v___x_118_;
goto v___jp_104_;
}
else
{
lean_object* v___x_119_; 
v___x_119_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8);
v___y_105_ = v___x_119_;
goto v___jp_104_;
}
v___jp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_106_ = ((lean_object*)(lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__6));
v___x_107_ = l_Nat_reprFast(v_a_100_);
if (v_isShared_103_ == 0)
{
lean_ctor_set_tag(v___x_102_, 3);
lean_ctor_set(v___x_102_, 0, v___x_107_);
v___x_109_ = v___x_102_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_115_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_110_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_106_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
lean_inc(v___y_105_);
v___x_111_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_111_, 0, v___y_105_);
lean_ctor_set(v___x_111_, 1, v___x_110_);
v___x_112_ = 0;
v___x_113_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_113_, 0, v___x_111_);
lean_ctor_set_uint8(v___x_113_, sizeof(void*)*1, v___x_112_);
v___x_114_ = l_Repr_addAppParen(v___x_113_, v_prec_85_);
return v___x_114_;
}
}
}
}
case 1:
{
lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_121_ = lean_unsigned_to_nat(1024u);
v___x_122_ = lean_nat_dec_le(v___x_121_, v_prec_85_);
if (v___x_122_ == 0)
{
lean_object* v___x_123_; 
v___x_123_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7);
v___y_87_ = v___x_123_;
goto v___jp_86_;
}
else
{
lean_object* v___x_124_; 
v___x_124_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8);
v___y_87_ = v___x_124_;
goto v___jp_86_;
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
v___x_127_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7);
v___y_94_ = v___x_127_;
goto v___jp_93_;
}
else
{
lean_object* v___x_128_; 
v___x_128_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8);
v___y_94_ = v___x_128_;
goto v___jp_93_;
}
}
}
v___jp_86_:
{
lean_object* v___x_88_; lean_object* v___x_89_; uint8_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_88_ = ((lean_object*)(lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__1));
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
v___x_95_ = ((lean_object*)(lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__3));
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
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___boxed(lean_object* v_x_129_, lean_object* v_prec_130_){
_start:
{
lean_object* v_res_131_; 
v_res_131_ = lp_oak_x2dspec_Oak_Layout_instReprEvent_repr(v_x_129_, v_prec_130_);
lean_dec(v_prec_130_);
return v_res_131_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorIdx(lean_object* v_x_134_){
_start:
{
switch(lean_obj_tag(v_x_134_))
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
default: 
{
lean_object* v___x_137_; 
v___x_137_ = lean_unsigned_to_nat(2u);
return v___x_137_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorIdx___boxed(lean_object* v_x_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = lp_oak_x2dspec_Oak_Layout_Token_ctorIdx(v_x_138_);
lean_dec(v_x_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorElim___redArg(lean_object* v_t_140_, lean_object* v_k_141_){
_start:
{
if (lean_obj_tag(v_t_140_) == 0)
{
lean_object* v_a_142_; lean_object* v___x_143_; 
v_a_142_ = lean_ctor_get(v_t_140_, 0);
lean_inc(v_a_142_);
lean_dec_ref_known(v_t_140_, 1);
v___x_143_ = lean_apply_1(v_k_141_, v_a_142_);
return v___x_143_;
}
else
{
lean_dec(v_t_140_);
return v_k_141_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorElim(lean_object* v_motive_144_, lean_object* v_ctorIdx_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_k_148_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = lp_oak_x2dspec_Oak_Layout_Token_ctorElim___redArg(v_t_146_, v_k_148_);
return v___x_149_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_ctorElim___boxed(lean_object* v_motive_150_, lean_object* v_ctorIdx_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_k_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = lp_oak_x2dspec_Oak_Layout_Token_ctorElim(v_motive_150_, v_ctorIdx_151_, v_t_152_, v_h_153_, v_k_154_);
lean_dec(v_ctorIdx_151_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_source_elim___redArg(lean_object* v_t_156_, lean_object* v_source_157_){
_start:
{
lean_object* v___x_158_; 
v___x_158_ = lp_oak_x2dspec_Oak_Layout_Token_ctorElim___redArg(v_t_156_, v_source_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_source_elim(lean_object* v_motive_159_, lean_object* v_t_160_, lean_object* v_h_161_, lean_object* v_source_162_){
_start:
{
lean_object* v___x_163_; 
v___x_163_ = lp_oak_x2dspec_Oak_Layout_Token_ctorElim___redArg(v_t_160_, v_source_162_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_push_elim___redArg(lean_object* v_t_164_, lean_object* v_push_165_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = lp_oak_x2dspec_Oak_Layout_Token_ctorElim___redArg(v_t_164_, v_push_165_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_push_elim(lean_object* v_motive_167_, lean_object* v_t_168_, lean_object* v_h_169_, lean_object* v_push_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = lp_oak_x2dspec_Oak_Layout_Token_ctorElim___redArg(v_t_168_, v_push_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_pop_elim___redArg(lean_object* v_t_172_, lean_object* v_pop_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = lp_oak_x2dspec_Oak_Layout_Token_ctorElim___redArg(v_t_172_, v_pop_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_Token_pop_elim(lean_object* v_motive_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_pop_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = lp_oak_x2dspec_Oak_Layout_Token_ctorElim___redArg(v_t_176_, v_pop_178_);
return v___x_179_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Layout_instDecidableEqToken_decEq(lean_object* v_x_180_, lean_object* v_x_181_){
_start:
{
switch(lean_obj_tag(v_x_180_))
{
case 0:
{
lean_object* v_a_182_; uint8_t v___x_183_; 
v_a_182_ = lean_ctor_get(v_x_180_, 0);
v___x_183_ = 0;
if (lean_obj_tag(v_x_181_) == 0)
{
lean_object* v_a_184_; uint8_t v___x_185_; 
v_a_184_ = lean_ctor_get(v_x_181_, 0);
v___x_185_ = lean_nat_dec_eq(v_a_182_, v_a_184_);
if (v___x_185_ == 0)
{
return v___x_183_;
}
else
{
return v___x_185_;
}
}
else
{
return v___x_183_;
}
}
case 1:
{
if (lean_obj_tag(v_x_181_) == 1)
{
uint8_t v___x_186_; 
v___x_186_ = 1;
return v___x_186_;
}
else
{
uint8_t v___x_187_; 
v___x_187_ = 0;
return v___x_187_;
}
}
default: 
{
if (lean_obj_tag(v_x_181_) == 2)
{
uint8_t v___x_188_; 
v___x_188_ = 1;
return v___x_188_;
}
else
{
uint8_t v___x_189_; 
v___x_189_ = 0;
return v___x_189_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instDecidableEqToken_decEq___boxed(lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
uint8_t v_res_192_; lean_object* v_r_193_; 
v_res_192_ = lp_oak_x2dspec_Oak_Layout_instDecidableEqToken_decEq(v_x_190_, v_x_191_);
lean_dec(v_x_191_);
lean_dec(v_x_190_);
v_r_193_ = lean_box(v_res_192_);
return v_r_193_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Layout_instDecidableEqToken(lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = lp_oak_x2dspec_Oak_Layout_instDecidableEqToken_decEq(v_x_194_, v_x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instDecidableEqToken___boxed(lean_object* v_x_197_, lean_object* v_x_198_){
_start:
{
uint8_t v_res_199_; lean_object* v_r_200_; 
v_res_199_ = lp_oak_x2dspec_Oak_Layout_instDecidableEqToken(v_x_197_, v_x_198_);
lean_dec(v_x_198_);
lean_dec(v_x_197_);
v_r_200_ = lean_box(v_res_199_);
return v_r_200_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr(lean_object* v_x_213_, lean_object* v_prec_214_){
_start:
{
lean_object* v___y_216_; lean_object* v___y_223_; 
switch(lean_obj_tag(v_x_213_))
{
case 0:
{
lean_object* v_a_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_249_; 
v_a_229_ = lean_ctor_get(v_x_213_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v_x_213_);
if (v_isSharedCheck_249_ == 0)
{
v___x_231_ = v_x_213_;
v_isShared_232_ = v_isSharedCheck_249_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_a_229_);
lean_dec(v_x_213_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_249_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___y_234_; lean_object* v___x_245_; uint8_t v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(1024u);
v___x_246_ = lean_nat_dec_le(v___x_245_, v_prec_214_);
if (v___x_246_ == 0)
{
lean_object* v___x_247_; 
v___x_247_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7);
v___y_234_ = v___x_247_;
goto v___jp_233_;
}
else
{
lean_object* v___x_248_; 
v___x_248_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8);
v___y_234_ = v___x_248_;
goto v___jp_233_;
}
v___jp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_235_ = ((lean_object*)(lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__6));
v___x_236_ = l_Nat_reprFast(v_a_229_);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 3);
lean_ctor_set(v___x_231_, 0, v___x_236_);
v___x_238_ = v___x_231_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_244_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_240_; uint8_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_239_, 0, v___x_235_);
lean_ctor_set(v___x_239_, 1, v___x_238_);
lean_inc(v___y_234_);
v___x_240_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_240_, 0, v___y_234_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = 0;
v___x_242_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*1, v___x_241_);
v___x_243_ = l_Repr_addAppParen(v___x_242_, v_prec_214_);
return v___x_243_;
}
}
}
}
case 1:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = lean_unsigned_to_nat(1024u);
v___x_251_ = lean_nat_dec_le(v___x_250_, v_prec_214_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
v___x_252_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7);
v___y_216_ = v___x_252_;
goto v___jp_215_;
}
else
{
lean_object* v___x_253_; 
v___x_253_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8);
v___y_216_ = v___x_253_;
goto v___jp_215_;
}
}
default: 
{
lean_object* v___x_254_; uint8_t v___x_255_; 
v___x_254_ = lean_unsigned_to_nat(1024u);
v___x_255_ = lean_nat_dec_le(v___x_254_, v_prec_214_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
v___x_256_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__7);
v___y_223_ = v___x_256_;
goto v___jp_222_;
}
else
{
lean_object* v___x_257_; 
v___x_257_ = lean_obj_once(&lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8, &lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8_once, _init_lp_oak_x2dspec_Oak_Layout_instReprEvent_repr___closed__8);
v___y_223_ = v___x_257_;
goto v___jp_222_;
}
}
}
v___jp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_217_ = ((lean_object*)(lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__1));
lean_inc(v___y_216_);
v___x_218_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_218_, 0, v___y_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = 0;
v___x_220_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set_uint8(v___x_220_, sizeof(void*)*1, v___x_219_);
v___x_221_ = l_Repr_addAppParen(v___x_220_, v_prec_214_);
return v___x_221_;
}
v___jp_222_:
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_224_ = ((lean_object*)(lp_oak_x2dspec_Oak_Layout_instReprToken_repr___closed__3));
lean_inc(v___y_223_);
v___x_225_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_225_, 0, v___y_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = 0;
v___x_227_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_227_, 0, v___x_225_);
lean_ctor_set_uint8(v___x_227_, sizeof(void*)*1, v___x_226_);
v___x_228_ = l_Repr_addAppParen(v___x_227_, v_prec_214_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_instReprToken_repr___boxed(lean_object* v_x_258_, lean_object* v_prec_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = lp_oak_x2dspec_Oak_Layout_instReprToken_repr(v_x_258_, v_prec_259_);
lean_dec(v_prec_259_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_sourceValues(lean_object* v_x_263_){
_start:
{
if (lean_obj_tag(v_x_263_) == 0)
{
lean_object* v___x_264_; 
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v_head_265_; 
v_head_265_ = lean_ctor_get(v_x_263_, 0);
if (lean_obj_tag(v_head_265_) == 0)
{
lean_object* v_tail_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_275_; 
lean_inc_ref(v_head_265_);
v_tail_266_ = lean_ctor_get(v_x_263_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_x_263_);
if (v_isSharedCheck_275_ == 0)
{
lean_object* v_unused_276_; 
v_unused_276_ = lean_ctor_get(v_x_263_, 0);
lean_dec(v_unused_276_);
v___x_268_ = v_x_263_;
v_isShared_269_ = v_isSharedCheck_275_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_tail_266_);
lean_dec(v_x_263_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_275_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v_a_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
v_a_270_ = lean_ctor_get(v_head_265_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v_head_265_, 1);
v___x_271_ = lp_oak_x2dspec_Oak_Layout_sourceValues(v_tail_266_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 1, v___x_271_);
lean_ctor_set(v___x_268_, 0, v_a_270_);
v___x_273_ = v___x_268_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_270_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
}
else
{
lean_object* v_tail_277_; 
v_tail_277_ = lean_ctor_get(v_x_263_, 1);
lean_inc(v_tail_277_);
lean_dec_ref_known(v_x_263_, 2);
v_x_263_ = v_tail_277_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_sourceEvents(lean_object* v_x_279_){
_start:
{
if (lean_obj_tag(v_x_279_) == 0)
{
lean_object* v___x_280_; 
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v_head_281_; 
v_head_281_ = lean_ctor_get(v_x_279_, 0);
if (lean_obj_tag(v_head_281_) == 0)
{
lean_object* v_tail_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_291_; 
lean_inc_ref(v_head_281_);
v_tail_282_ = lean_ctor_get(v_x_279_, 1);
v_isSharedCheck_291_ = !lean_is_exclusive(v_x_279_);
if (v_isSharedCheck_291_ == 0)
{
lean_object* v_unused_292_; 
v_unused_292_ = lean_ctor_get(v_x_279_, 0);
lean_dec(v_unused_292_);
v___x_284_ = v_x_279_;
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_tail_282_);
lean_dec(v_x_279_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v_a_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v_a_286_ = lean_ctor_get(v_head_281_, 0);
lean_inc(v_a_286_);
lean_dec_ref_known(v_head_281_, 1);
v___x_287_ = lp_oak_x2dspec_Oak_Layout_sourceEvents(v_tail_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v___x_287_);
lean_ctor_set(v___x_284_, 0, v_a_286_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_a_286_);
lean_ctor_set(v_reuseFailAlloc_290_, 1, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
}
else
{
lean_object* v_tail_293_; 
v_tail_293_ = lean_ctor_get(v_x_279_, 1);
lean_inc(v_tail_293_);
lean_dec_ref_known(v_x_279_, 2);
v_x_279_ = v_tail_293_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_opens(lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v___x_296_; 
v___x_296_ = lean_unsigned_to_nat(0u);
return v___x_296_;
}
else
{
lean_object* v_head_297_; 
v_head_297_ = lean_ctor_get(v_x_295_, 0);
if (lean_obj_tag(v_head_297_) == 1)
{
lean_object* v_tail_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_tail_298_ = lean_ctor_get(v_x_295_, 1);
v___x_299_ = lean_unsigned_to_nat(1u);
v___x_300_ = lp_oak_x2dspec_Oak_Layout_opens(v_tail_298_);
v___x_301_ = lean_nat_add(v___x_299_, v___x_300_);
lean_dec(v___x_300_);
return v___x_301_;
}
else
{
lean_object* v_tail_302_; 
v_tail_302_ = lean_ctor_get(v_x_295_, 1);
v_x_295_ = v_tail_302_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_opens___boxed(lean_object* v_x_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = lp_oak_x2dspec_Oak_Layout_opens(v_x_304_);
lean_dec(v_x_304_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_closes(lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_306_) == 0)
{
lean_object* v___x_307_; 
v___x_307_ = lean_unsigned_to_nat(0u);
return v___x_307_;
}
else
{
lean_object* v_head_308_; 
v_head_308_ = lean_ctor_get(v_x_306_, 0);
if (lean_obj_tag(v_head_308_) == 2)
{
lean_object* v_tail_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v_tail_309_ = lean_ctor_get(v_x_306_, 1);
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = lp_oak_x2dspec_Oak_Layout_closes(v_tail_309_);
v___x_312_ = lean_nat_add(v___x_310_, v___x_311_);
lean_dec(v___x_311_);
return v___x_312_;
}
else
{
lean_object* v_tail_313_; 
v_tail_313_ = lean_ctor_get(v_x_306_, 1);
v_x_306_ = v_tail_313_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_closes___boxed(lean_object* v_x_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = lp_oak_x2dspec_Oak_Layout_closes(v_x_315_);
lean_dec(v_x_315_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_renderFrom(lean_object* v_x_317_, lean_object* v_x_318_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = lean_box(0);
v___x_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_320_, 0, v_x_317_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_321_, 0, v___x_320_);
return v___x_321_;
}
else
{
lean_object* v_head_322_; 
v_head_322_ = lean_ctor_get(v_x_318_, 0);
lean_inc(v_head_322_);
switch(lean_obj_tag(v_head_322_))
{
case 0:
{
lean_object* v_tail_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_356_; 
v_tail_323_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_356_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_356_ == 0)
{
lean_object* v_unused_357_; 
v_unused_357_ = lean_ctor_get(v_x_318_, 0);
lean_dec(v_unused_357_);
v___x_325_ = v_x_318_;
v_isShared_326_ = v_isSharedCheck_356_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_tail_323_);
lean_dec(v_x_318_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_356_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_355_; 
v_a_327_ = lean_ctor_get(v_head_322_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v_head_322_);
if (v_isSharedCheck_355_ == 0)
{
v___x_329_ = v_head_322_;
v_isShared_330_ = v_isSharedCheck_355_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v_head_322_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_355_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_331_; 
v___x_331_ = lp_oak_x2dspec_Oak_Layout_renderFrom(v_x_317_, v_tail_323_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_del_object(v___x_329_);
lean_dec(v_a_327_);
lean_del_object(v___x_325_);
return v___x_331_;
}
else
{
lean_object* v_val_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_354_; 
v_val_332_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_354_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_354_ == 0)
{
v___x_334_ = v___x_331_;
v_isShared_335_ = v_isSharedCheck_354_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_val_332_);
lean_dec(v___x_331_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_354_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_fst_336_; lean_object* v_snd_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_353_; 
v_fst_336_ = lean_ctor_get(v_val_332_, 0);
v_snd_337_ = lean_ctor_get(v_val_332_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_val_332_);
if (v_isSharedCheck_353_ == 0)
{
v___x_339_ = v_val_332_;
v_isShared_340_ = v_isSharedCheck_353_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snd_337_);
lean_inc(v_fst_336_);
lean_dec(v_val_332_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_353_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_342_; 
if (v_isShared_330_ == 0)
{
v___x_342_ = v___x_329_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_a_327_);
v___x_342_ = v_reuseFailAlloc_352_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
lean_object* v___x_344_; 
if (v_isShared_326_ == 0)
{
lean_ctor_set(v___x_325_, 1, v_snd_337_);
lean_ctor_set(v___x_325_, 0, v___x_342_);
v___x_344_ = v___x_325_;
goto v_reusejp_343_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v___x_342_);
lean_ctor_set(v_reuseFailAlloc_351_, 1, v_snd_337_);
v___x_344_ = v_reuseFailAlloc_351_;
goto v_reusejp_343_;
}
v_reusejp_343_:
{
lean_object* v___x_346_; 
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_344_);
v___x_346_ = v___x_339_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_fst_336_);
lean_ctor_set(v_reuseFailAlloc_350_, 1, v___x_344_);
v___x_346_ = v_reuseFailAlloc_350_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
lean_object* v___x_348_; 
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 0, v___x_346_);
v___x_348_ = v___x_334_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
}
}
}
}
}
}
}
case 1:
{
lean_object* v_tail_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_386_; 
v_tail_358_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_386_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_386_ == 0)
{
lean_object* v_unused_387_; 
v_unused_387_ = lean_ctor_get(v_x_318_, 0);
lean_dec(v_unused_387_);
v___x_360_ = v_x_318_;
v_isShared_361_ = v_isSharedCheck_386_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_tail_358_);
lean_dec(v_x_318_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_386_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_362_ = lean_unsigned_to_nat(1u);
v___x_363_ = lean_nat_add(v_x_317_, v___x_362_);
lean_dec(v_x_317_);
v___x_364_ = lp_oak_x2dspec_Oak_Layout_renderFrom(v___x_363_, v_tail_358_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_del_object(v___x_360_);
return v___x_364_;
}
else
{
lean_object* v_val_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_385_; 
v_val_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_385_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_385_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_val_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_385_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_fst_369_; lean_object* v_snd_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_384_; 
v_fst_369_ = lean_ctor_get(v_val_365_, 0);
v_snd_370_ = lean_ctor_get(v_val_365_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_val_365_);
if (v_isSharedCheck_384_ == 0)
{
v___x_372_ = v_val_365_;
v_isShared_373_ = v_isSharedCheck_384_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_snd_370_);
lean_inc(v_fst_369_);
lean_dec(v_val_365_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_384_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_374_ = lean_box(1);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 1, v_snd_370_);
lean_ctor_set(v___x_360_, 0, v___x_374_);
v___x_376_ = v___x_360_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v_snd_370_);
v___x_376_ = v_reuseFailAlloc_383_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
lean_object* v___x_378_; 
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 1, v___x_376_);
v___x_378_ = v___x_372_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_fst_369_);
lean_ctor_set(v_reuseFailAlloc_382_, 1, v___x_376_);
v___x_378_ = v_reuseFailAlloc_382_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
lean_object* v___x_380_; 
if (v_isShared_368_ == 0)
{
lean_ctor_set(v___x_367_, 0, v___x_378_);
v___x_380_ = v___x_367_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
}
}
}
}
}
default: 
{
lean_object* v_tail_388_; lean_object* v___x_390_; uint8_t v_isShared_391_; uint8_t v_isSharedCheck_419_; 
v_tail_388_ = lean_ctor_get(v_x_318_, 1);
v_isSharedCheck_419_ = !lean_is_exclusive(v_x_318_);
if (v_isSharedCheck_419_ == 0)
{
lean_object* v_unused_420_; 
v_unused_420_ = lean_ctor_get(v_x_318_, 0);
lean_dec(v_unused_420_);
v___x_390_ = v_x_318_;
v_isShared_391_ = v_isSharedCheck_419_;
goto v_resetjp_389_;
}
else
{
lean_inc(v_tail_388_);
lean_dec(v_x_318_);
v___x_390_ = lean_box(0);
v_isShared_391_ = v_isSharedCheck_419_;
goto v_resetjp_389_;
}
v_resetjp_389_:
{
lean_object* v_zero_392_; uint8_t v_isZero_393_; 
v_zero_392_ = lean_unsigned_to_nat(0u);
v_isZero_393_ = lean_nat_dec_eq(v_x_317_, v_zero_392_);
if (v_isZero_393_ == 1)
{
lean_object* v___x_394_; 
lean_del_object(v___x_390_);
lean_dec(v_tail_388_);
lean_dec(v_x_317_);
v___x_394_ = lean_box(0);
return v___x_394_;
}
else
{
lean_object* v_one_395_; lean_object* v_n_396_; lean_object* v___x_397_; 
v_one_395_ = lean_unsigned_to_nat(1u);
v_n_396_ = lean_nat_sub(v_x_317_, v_one_395_);
lean_dec(v_x_317_);
v___x_397_ = lp_oak_x2dspec_Oak_Layout_renderFrom(v_n_396_, v_tail_388_);
if (lean_obj_tag(v___x_397_) == 0)
{
lean_del_object(v___x_390_);
return v___x_397_;
}
else
{
lean_object* v_val_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_418_; 
v_val_398_ = lean_ctor_get(v___x_397_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_397_);
if (v_isSharedCheck_418_ == 0)
{
v___x_400_ = v___x_397_;
v_isShared_401_ = v_isSharedCheck_418_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_val_398_);
lean_dec(v___x_397_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_418_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v_fst_402_; lean_object* v_snd_403_; lean_object* v___x_405_; uint8_t v_isShared_406_; uint8_t v_isSharedCheck_417_; 
v_fst_402_ = lean_ctor_get(v_val_398_, 0);
v_snd_403_ = lean_ctor_get(v_val_398_, 1);
v_isSharedCheck_417_ = !lean_is_exclusive(v_val_398_);
if (v_isSharedCheck_417_ == 0)
{
v___x_405_ = v_val_398_;
v_isShared_406_ = v_isSharedCheck_417_;
goto v_resetjp_404_;
}
else
{
lean_inc(v_snd_403_);
lean_inc(v_fst_402_);
lean_dec(v_val_398_);
v___x_405_ = lean_box(0);
v_isShared_406_ = v_isSharedCheck_417_;
goto v_resetjp_404_;
}
v_resetjp_404_:
{
lean_object* v___x_407_; lean_object* v___x_409_; 
v___x_407_ = lean_box(2);
if (v_isShared_391_ == 0)
{
lean_ctor_set(v___x_390_, 1, v_snd_403_);
lean_ctor_set(v___x_390_, 0, v___x_407_);
v___x_409_ = v___x_390_;
goto v_reusejp_408_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v___x_407_);
lean_ctor_set(v_reuseFailAlloc_416_, 1, v_snd_403_);
v___x_409_ = v_reuseFailAlloc_416_;
goto v_reusejp_408_;
}
v_reusejp_408_:
{
lean_object* v___x_411_; 
if (v_isShared_406_ == 0)
{
lean_ctor_set(v___x_405_, 1, v___x_409_);
v___x_411_ = v___x_405_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_fst_402_);
lean_ctor_set(v_reuseFailAlloc_415_, 1, v___x_409_);
v___x_411_ = v_reuseFailAlloc_415_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
lean_object* v___x_413_; 
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 0, v___x_411_);
v___x_413_ = v___x_400_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_411_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Layout_finishTokens(lean_object* v_depth_421_, lean_object* v_output_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
v___x_423_ = lean_box(2);
v___x_424_ = l_List_replicateTR___redArg(v_depth_421_, v___x_423_);
v___x_425_ = l_List_appendTR___redArg(v_output_422_, v___x_424_);
return v___x_425_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_sourceValues_match__1_splitter___redArg(lean_object* v_x_426_, lean_object* v_h__1_427_, lean_object* v_h__2_428_, lean_object* v_h__3_429_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; 
lean_dec(v_h__3_429_);
lean_dec(v_h__2_428_);
v___x_430_ = lean_box(0);
v___x_431_ = lean_apply_1(v_h__1_427_, v___x_430_);
return v___x_431_;
}
else
{
lean_object* v_head_432_; 
lean_dec(v_h__1_427_);
v_head_432_ = lean_ctor_get(v_x_426_, 0);
lean_inc(v_head_432_);
if (lean_obj_tag(v_head_432_) == 0)
{
lean_object* v_tail_433_; lean_object* v_a_434_; lean_object* v___x_435_; 
lean_dec(v_h__3_429_);
v_tail_433_ = lean_ctor_get(v_x_426_, 1);
lean_inc(v_tail_433_);
lean_dec_ref_known(v_x_426_, 2);
v_a_434_ = lean_ctor_get(v_head_432_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v_head_432_, 1);
v___x_435_ = lean_apply_2(v_h__2_428_, v_a_434_, v_tail_433_);
return v___x_435_;
}
else
{
lean_object* v_tail_436_; lean_object* v___x_437_; 
lean_dec(v_h__2_428_);
v_tail_436_ = lean_ctor_get(v_x_426_, 1);
lean_inc(v_tail_436_);
lean_dec_ref_known(v_x_426_, 2);
v___x_437_ = lean_apply_3(v_h__3_429_, v_head_432_, v_tail_436_, lean_box(0));
return v___x_437_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_sourceValues_match__1_splitter(lean_object* v_motive_438_, lean_object* v_x_439_, lean_object* v_h__1_440_, lean_object* v_h__2_441_, lean_object* v_h__3_442_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v_h__3_442_);
lean_dec(v_h__2_441_);
v___x_443_ = lean_box(0);
v___x_444_ = lean_apply_1(v_h__1_440_, v___x_443_);
return v___x_444_;
}
else
{
lean_object* v_head_445_; 
lean_dec(v_h__1_440_);
v_head_445_ = lean_ctor_get(v_x_439_, 0);
lean_inc(v_head_445_);
if (lean_obj_tag(v_head_445_) == 0)
{
lean_object* v_tail_446_; lean_object* v_a_447_; lean_object* v___x_448_; 
lean_dec(v_h__3_442_);
v_tail_446_ = lean_ctor_get(v_x_439_, 1);
lean_inc(v_tail_446_);
lean_dec_ref_known(v_x_439_, 2);
v_a_447_ = lean_ctor_get(v_head_445_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v_head_445_, 1);
v___x_448_ = lean_apply_2(v_h__2_441_, v_a_447_, v_tail_446_);
return v___x_448_;
}
else
{
lean_object* v_tail_449_; lean_object* v___x_450_; 
lean_dec(v_h__2_441_);
v_tail_449_ = lean_ctor_get(v_x_439_, 1);
lean_inc(v_tail_449_);
lean_dec_ref_known(v_x_439_, 2);
v___x_450_ = lean_apply_3(v_h__3_442_, v_head_445_, v_tail_449_, lean_box(0));
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_opens_match__1_splitter___redArg(lean_object* v_x_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_, lean_object* v_h__3_454_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec(v_h__3_454_);
lean_dec(v_h__2_453_);
v___x_455_ = lean_box(0);
v___x_456_ = lean_apply_1(v_h__1_452_, v___x_455_);
return v___x_456_;
}
else
{
lean_object* v_head_457_; 
lean_dec(v_h__1_452_);
v_head_457_ = lean_ctor_get(v_x_451_, 0);
if (lean_obj_tag(v_head_457_) == 1)
{
lean_object* v_tail_458_; lean_object* v___x_459_; 
lean_dec(v_h__3_454_);
v_tail_458_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_tail_458_);
lean_dec_ref_known(v_x_451_, 2);
v___x_459_ = lean_apply_1(v_h__2_453_, v_tail_458_);
return v___x_459_;
}
else
{
lean_object* v_tail_460_; lean_object* v___x_461_; 
lean_inc(v_head_457_);
lean_dec(v_h__2_453_);
v_tail_460_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_tail_460_);
lean_dec_ref_known(v_x_451_, 2);
v___x_461_ = lean_apply_3(v_h__3_454_, v_head_457_, v_tail_460_, lean_box(0));
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_opens_match__1_splitter(lean_object* v_motive_462_, lean_object* v_x_463_, lean_object* v_h__1_464_, lean_object* v_h__2_465_, lean_object* v_h__3_466_){
_start:
{
if (lean_obj_tag(v_x_463_) == 0)
{
lean_object* v___x_467_; lean_object* v___x_468_; 
lean_dec(v_h__3_466_);
lean_dec(v_h__2_465_);
v___x_467_ = lean_box(0);
v___x_468_ = lean_apply_1(v_h__1_464_, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v_head_469_; 
lean_dec(v_h__1_464_);
v_head_469_ = lean_ctor_get(v_x_463_, 0);
if (lean_obj_tag(v_head_469_) == 1)
{
lean_object* v_tail_470_; lean_object* v___x_471_; 
lean_dec(v_h__3_466_);
v_tail_470_ = lean_ctor_get(v_x_463_, 1);
lean_inc(v_tail_470_);
lean_dec_ref_known(v_x_463_, 2);
v___x_471_ = lean_apply_1(v_h__2_465_, v_tail_470_);
return v___x_471_;
}
else
{
lean_object* v_tail_472_; lean_object* v___x_473_; 
lean_inc(v_head_469_);
lean_dec(v_h__2_465_);
v_tail_472_ = lean_ctor_get(v_x_463_, 1);
lean_inc(v_tail_472_);
lean_dec_ref_known(v_x_463_, 2);
v___x_473_ = lean_apply_3(v_h__3_466_, v_head_469_, v_tail_472_, lean_box(0));
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_closes_match__1_splitter___redArg(lean_object* v_x_474_, lean_object* v_h__1_475_, lean_object* v_h__2_476_, lean_object* v_h__3_477_){
_start:
{
if (lean_obj_tag(v_x_474_) == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
lean_dec(v_h__3_477_);
lean_dec(v_h__2_476_);
v___x_478_ = lean_box(0);
v___x_479_ = lean_apply_1(v_h__1_475_, v___x_478_);
return v___x_479_;
}
else
{
lean_object* v_head_480_; 
lean_dec(v_h__1_475_);
v_head_480_ = lean_ctor_get(v_x_474_, 0);
if (lean_obj_tag(v_head_480_) == 2)
{
lean_object* v_tail_481_; lean_object* v___x_482_; 
lean_dec(v_h__3_477_);
v_tail_481_ = lean_ctor_get(v_x_474_, 1);
lean_inc(v_tail_481_);
lean_dec_ref_known(v_x_474_, 2);
v___x_482_ = lean_apply_1(v_h__2_476_, v_tail_481_);
return v___x_482_;
}
else
{
lean_object* v_tail_483_; lean_object* v___x_484_; 
lean_inc(v_head_480_);
lean_dec(v_h__2_476_);
v_tail_483_ = lean_ctor_get(v_x_474_, 1);
lean_inc(v_tail_483_);
lean_dec_ref_known(v_x_474_, 2);
v___x_484_ = lean_apply_3(v_h__3_477_, v_head_480_, v_tail_483_, lean_box(0));
return v___x_484_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_closes_match__1_splitter(lean_object* v_motive_485_, lean_object* v_x_486_, lean_object* v_h__1_487_, lean_object* v_h__2_488_, lean_object* v_h__3_489_){
_start:
{
if (lean_obj_tag(v_x_486_) == 0)
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec(v_h__3_489_);
lean_dec(v_h__2_488_);
v___x_490_ = lean_box(0);
v___x_491_ = lean_apply_1(v_h__1_487_, v___x_490_);
return v___x_491_;
}
else
{
lean_object* v_head_492_; 
lean_dec(v_h__1_487_);
v_head_492_ = lean_ctor_get(v_x_486_, 0);
if (lean_obj_tag(v_head_492_) == 2)
{
lean_object* v_tail_493_; lean_object* v___x_494_; 
lean_dec(v_h__3_489_);
v_tail_493_ = lean_ctor_get(v_x_486_, 1);
lean_inc(v_tail_493_);
lean_dec_ref_known(v_x_486_, 2);
v___x_494_ = lean_apply_1(v_h__2_488_, v_tail_493_);
return v___x_494_;
}
else
{
lean_object* v_tail_495_; lean_object* v___x_496_; 
lean_inc(v_head_492_);
lean_dec(v_h__2_488_);
v_tail_495_ = lean_ctor_get(v_x_486_, 1);
lean_inc(v_tail_495_);
lean_dec_ref_known(v_x_486_, 2);
v___x_496_ = lean_apply_3(v_h__3_489_, v_head_492_, v_tail_495_, lean_box(0));
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_renderFrom_match__3_splitter___redArg(lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_, lean_object* v_h__3_501_, lean_object* v_h__4_502_, lean_object* v_h__5_503_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v___x_504_; 
lean_dec(v_h__5_503_);
lean_dec(v_h__4_502_);
lean_dec(v_h__3_501_);
lean_dec(v_h__2_500_);
v___x_504_ = lean_apply_1(v_h__1_499_, v_x_497_);
return v___x_504_;
}
else
{
lean_object* v_head_505_; 
lean_dec(v_h__1_499_);
v_head_505_ = lean_ctor_get(v_x_498_, 0);
switch(lean_obj_tag(v_head_505_))
{
case 0:
{
lean_object* v_tail_506_; lean_object* v_a_507_; lean_object* v___x_508_; 
lean_inc_ref(v_head_505_);
lean_dec(v_h__5_503_);
lean_dec(v_h__4_502_);
lean_dec(v_h__3_501_);
v_tail_506_ = lean_ctor_get(v_x_498_, 1);
lean_inc(v_tail_506_);
lean_dec_ref_known(v_x_498_, 2);
v_a_507_ = lean_ctor_get(v_head_505_, 0);
lean_inc(v_a_507_);
lean_dec_ref_known(v_head_505_, 1);
v___x_508_ = lean_apply_3(v_h__2_500_, v_x_497_, v_a_507_, v_tail_506_);
return v___x_508_;
}
case 1:
{
lean_object* v_tail_509_; lean_object* v___x_510_; 
lean_dec(v_h__5_503_);
lean_dec(v_h__4_502_);
lean_dec(v_h__2_500_);
v_tail_509_ = lean_ctor_get(v_x_498_, 1);
lean_inc(v_tail_509_);
lean_dec_ref_known(v_x_498_, 2);
v___x_510_ = lean_apply_2(v_h__3_501_, v_x_497_, v_tail_509_);
return v___x_510_;
}
default: 
{
lean_object* v_tail_511_; lean_object* v_zero_512_; uint8_t v_isZero_513_; 
lean_dec(v_h__3_501_);
lean_dec(v_h__2_500_);
v_tail_511_ = lean_ctor_get(v_x_498_, 1);
lean_inc(v_tail_511_);
lean_dec_ref_known(v_x_498_, 2);
v_zero_512_ = lean_unsigned_to_nat(0u);
v_isZero_513_ = lean_nat_dec_eq(v_x_497_, v_zero_512_);
if (v_isZero_513_ == 1)
{
lean_object* v___x_514_; 
lean_dec(v_h__5_503_);
lean_dec(v_x_497_);
v___x_514_ = lean_apply_1(v_h__4_502_, v_tail_511_);
return v___x_514_;
}
else
{
lean_object* v_one_515_; lean_object* v_n_516_; lean_object* v___x_517_; 
lean_dec(v_h__4_502_);
v_one_515_ = lean_unsigned_to_nat(1u);
v_n_516_ = lean_nat_sub(v_x_497_, v_one_515_);
lean_dec(v_x_497_);
v___x_517_ = lean_apply_2(v_h__5_503_, v_n_516_, v_tail_511_);
return v___x_517_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_renderFrom_match__3_splitter(lean_object* v_motive_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_h__1_521_, lean_object* v_h__2_522_, lean_object* v_h__3_523_, lean_object* v_h__4_524_, lean_object* v_h__5_525_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v___x_526_; 
lean_dec(v_h__5_525_);
lean_dec(v_h__4_524_);
lean_dec(v_h__3_523_);
lean_dec(v_h__2_522_);
v___x_526_ = lean_apply_1(v_h__1_521_, v_x_519_);
return v___x_526_;
}
else
{
lean_object* v_head_527_; 
lean_dec(v_h__1_521_);
v_head_527_ = lean_ctor_get(v_x_520_, 0);
switch(lean_obj_tag(v_head_527_))
{
case 0:
{
lean_object* v_tail_528_; lean_object* v_a_529_; lean_object* v___x_530_; 
lean_inc_ref(v_head_527_);
lean_dec(v_h__5_525_);
lean_dec(v_h__4_524_);
lean_dec(v_h__3_523_);
v_tail_528_ = lean_ctor_get(v_x_520_, 1);
lean_inc(v_tail_528_);
lean_dec_ref_known(v_x_520_, 2);
v_a_529_ = lean_ctor_get(v_head_527_, 0);
lean_inc(v_a_529_);
lean_dec_ref_known(v_head_527_, 1);
v___x_530_ = lean_apply_3(v_h__2_522_, v_x_519_, v_a_529_, v_tail_528_);
return v___x_530_;
}
case 1:
{
lean_object* v_tail_531_; lean_object* v___x_532_; 
lean_dec(v_h__5_525_);
lean_dec(v_h__4_524_);
lean_dec(v_h__2_522_);
v_tail_531_ = lean_ctor_get(v_x_520_, 1);
lean_inc(v_tail_531_);
lean_dec_ref_known(v_x_520_, 2);
v___x_532_ = lean_apply_2(v_h__3_523_, v_x_519_, v_tail_531_);
return v___x_532_;
}
default: 
{
lean_object* v_tail_533_; lean_object* v_zero_534_; uint8_t v_isZero_535_; 
lean_dec(v_h__3_523_);
lean_dec(v_h__2_522_);
v_tail_533_ = lean_ctor_get(v_x_520_, 1);
lean_inc(v_tail_533_);
lean_dec_ref_known(v_x_520_, 2);
v_zero_534_ = lean_unsigned_to_nat(0u);
v_isZero_535_ = lean_nat_dec_eq(v_x_519_, v_zero_534_);
if (v_isZero_535_ == 1)
{
lean_object* v___x_536_; 
lean_dec(v_h__5_525_);
lean_dec(v_x_519_);
v___x_536_ = lean_apply_1(v_h__4_524_, v_tail_533_);
return v___x_536_;
}
else
{
lean_object* v_one_537_; lean_object* v_n_538_; lean_object* v___x_539_; 
lean_dec(v_h__4_524_);
v_one_537_ = lean_unsigned_to_nat(1u);
v_n_538_ = lean_nat_sub(v_x_519_, v_one_537_);
lean_dec(v_x_519_);
v___x_539_ = lean_apply_2(v_h__5_525_, v_n_538_, v_tail_533_);
return v___x_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_renderFrom_match__1_splitter___redArg(lean_object* v_x_540_, lean_object* v_h__1_541_, lean_object* v_h__2_542_){
_start:
{
if (lean_obj_tag(v_x_540_) == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
lean_dec(v_h__2_542_);
v___x_543_ = lean_box(0);
v___x_544_ = lean_apply_1(v_h__1_541_, v___x_543_);
return v___x_544_;
}
else
{
lean_object* v_val_545_; lean_object* v_fst_546_; lean_object* v_snd_547_; lean_object* v___x_548_; 
lean_dec(v_h__1_541_);
v_val_545_ = lean_ctor_get(v_x_540_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v_x_540_, 1);
v_fst_546_ = lean_ctor_get(v_val_545_, 0);
lean_inc(v_fst_546_);
v_snd_547_ = lean_ctor_get(v_val_545_, 1);
lean_inc(v_snd_547_);
lean_dec(v_val_545_);
v___x_548_ = lean_apply_2(v_h__2_542_, v_fst_546_, v_snd_547_);
return v___x_548_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_renderFrom_match__1_splitter(lean_object* v_motive_549_, lean_object* v_x_550_, lean_object* v_h__1_551_, lean_object* v_h__2_552_){
_start:
{
if (lean_obj_tag(v_x_550_) == 0)
{
lean_object* v___x_553_; lean_object* v___x_554_; 
lean_dec(v_h__2_552_);
v___x_553_ = lean_box(0);
v___x_554_ = lean_apply_1(v_h__1_551_, v___x_553_);
return v___x_554_;
}
else
{
lean_object* v_val_555_; lean_object* v_fst_556_; lean_object* v_snd_557_; lean_object* v___x_558_; 
lean_dec(v_h__1_551_);
v_val_555_ = lean_ctor_get(v_x_550_, 0);
lean_inc(v_val_555_);
lean_dec_ref_known(v_x_550_, 1);
v_fst_556_ = lean_ctor_get(v_val_555_, 0);
lean_inc(v_fst_556_);
v_snd_557_ = lean_ctor_get(v_val_555_, 1);
lean_inc(v_snd_557_);
lean_dec(v_val_555_);
v___x_558_ = lean_apply_2(v_h__2_552_, v_fst_556_, v_snd_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_sourceEvents_match__1_splitter___redArg(lean_object* v_x_559_, lean_object* v_h__1_560_, lean_object* v_h__2_561_, lean_object* v_h__3_562_){
_start:
{
if (lean_obj_tag(v_x_559_) == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v_h__3_562_);
lean_dec(v_h__2_561_);
v___x_563_ = lean_box(0);
v___x_564_ = lean_apply_1(v_h__1_560_, v___x_563_);
return v___x_564_;
}
else
{
lean_object* v_head_565_; 
lean_dec(v_h__1_560_);
v_head_565_ = lean_ctor_get(v_x_559_, 0);
lean_inc(v_head_565_);
if (lean_obj_tag(v_head_565_) == 0)
{
lean_object* v_tail_566_; lean_object* v_a_567_; lean_object* v___x_568_; 
lean_dec(v_h__3_562_);
v_tail_566_ = lean_ctor_get(v_x_559_, 1);
lean_inc(v_tail_566_);
lean_dec_ref_known(v_x_559_, 2);
v_a_567_ = lean_ctor_get(v_head_565_, 0);
lean_inc(v_a_567_);
lean_dec_ref_known(v_head_565_, 1);
v___x_568_ = lean_apply_2(v_h__2_561_, v_a_567_, v_tail_566_);
return v___x_568_;
}
else
{
lean_object* v_tail_569_; lean_object* v___x_570_; 
lean_dec(v_h__2_561_);
v_tail_569_ = lean_ctor_get(v_x_559_, 1);
lean_inc(v_tail_569_);
lean_dec_ref_known(v_x_559_, 2);
v___x_570_ = lean_apply_3(v_h__3_562_, v_head_565_, v_tail_569_, lean_box(0));
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Layout_0__Oak_Layout_sourceEvents_match__1_splitter(lean_object* v_motive_571_, lean_object* v_x_572_, lean_object* v_h__1_573_, lean_object* v_h__2_574_, lean_object* v_h__3_575_){
_start:
{
if (lean_obj_tag(v_x_572_) == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec(v_h__3_575_);
lean_dec(v_h__2_574_);
v___x_576_ = lean_box(0);
v___x_577_ = lean_apply_1(v_h__1_573_, v___x_576_);
return v___x_577_;
}
else
{
lean_object* v_head_578_; 
lean_dec(v_h__1_573_);
v_head_578_ = lean_ctor_get(v_x_572_, 0);
lean_inc(v_head_578_);
if (lean_obj_tag(v_head_578_) == 0)
{
lean_object* v_tail_579_; lean_object* v_a_580_; lean_object* v___x_581_; 
lean_dec(v_h__3_575_);
v_tail_579_ = lean_ctor_get(v_x_572_, 1);
lean_inc(v_tail_579_);
lean_dec_ref_known(v_x_572_, 2);
v_a_580_ = lean_ctor_get(v_head_578_, 0);
lean_inc(v_a_580_);
lean_dec_ref_known(v_head_578_, 1);
v___x_581_ = lean_apply_2(v_h__2_574_, v_a_580_, v_tail_579_);
return v___x_581_;
}
else
{
lean_object* v_tail_582_; lean_object* v___x_583_; 
lean_dec(v_h__2_574_);
v_tail_582_ = lean_ctor_get(v_x_572_, 1);
lean_inc(v_tail_582_);
lean_dec_ref_known(v_x_572_, 2);
v___x_583_ = lean_apply_3(v_h__3_575_, v_head_578_, v_tail_582_, lean_box(0));
return v___x_583_;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_Layout(uint8_t builtin) {
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
