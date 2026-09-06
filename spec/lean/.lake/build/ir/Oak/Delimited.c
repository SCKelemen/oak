// Lean compiler output
// Module: Oak.Delimited
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
lean_object* l_List_appendTR___redArg(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_open_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_open_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_close_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_close_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_separator_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_separator_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_item_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_item_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Oak.Delimited.Token.separator"};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__1_value;
static const lean_string_object lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Oak.Delimited.Token.close"};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Oak.Delimited.Token.open"};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__5_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6;
static lean_once_cell_t lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Oak.Delimited.Token.item"};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__9_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__10_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_Delimited_instReprToken___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_instReprToken___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_Delimited_body___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_body___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_body___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_body(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_body___boxed(lean_object*, lean_object*);
static const lean_ctor_object lp_oak_x2dspec_Oak_Delimited_encode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_Delimited_encode___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_Delimited_encode___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_encode(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_encode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_closeOffset(lean_object*, uint8_t);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_closeOffset___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_itemValues(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_itemValues_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_itemValues_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorIdx(lean_object* v_x_1_){
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
default: 
{
lean_object* v___x_5_; 
v___x_5_ = lean_unsigned_to_nat(3u);
return v___x_5_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorIdx(v_x_6_);
lean_dec(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
if (lean_obj_tag(v_t_8_) == 3)
{
lean_object* v_a_10_; lean_object* v___x_11_; 
v_a_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_a_10_);
lean_dec_ref_known(v_t_8_, 1);
v___x_11_ = lean_apply_1(v_k_9_, v_a_10_);
return v___x_11_;
}
else
{
lean_dec(v_t_8_);
return v_k_9_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_open_elim___redArg(lean_object* v_t_24_, lean_object* v_open_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(v_t_24_, v_open_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_open_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_open_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(v_t_28_, v_open_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_close_elim___redArg(lean_object* v_t_32_, lean_object* v_close_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(v_t_32_, v_close_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_close_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_close_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(v_t_36_, v_close_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_separator_elim___redArg(lean_object* v_t_40_, lean_object* v_separator_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(v_t_40_, v_separator_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_separator_elim(lean_object* v_motive_43_, lean_object* v_t_44_, lean_object* v_h_45_, lean_object* v_separator_46_){
_start:
{
lean_object* v___x_47_; 
v___x_47_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(v_t_44_, v_separator_46_);
return v___x_47_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_item_elim___redArg(lean_object* v_t_48_, lean_object* v_item_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(v_t_48_, v_item_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_Token_item_elim(lean_object* v_motive_51_, lean_object* v_t_52_, lean_object* v_h_53_, lean_object* v_item_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lp_oak_x2dspec_Oak_Delimited_Token_ctorElim___redArg(v_t_52_, v_item_54_);
return v___x_55_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken_decEq(lean_object* v_x_56_, lean_object* v_x_57_){
_start:
{
switch(lean_obj_tag(v_x_56_))
{
case 0:
{
switch(lean_obj_tag(v_x_57_))
{
case 0:
{
uint8_t v___x_58_; 
v___x_58_ = 1;
return v___x_58_;
}
case 3:
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
default: 
{
uint8_t v___x_60_; 
v___x_60_ = 0;
return v___x_60_;
}
}
}
case 1:
{
switch(lean_obj_tag(v_x_57_))
{
case 1:
{
uint8_t v___x_61_; 
v___x_61_ = 1;
return v___x_61_;
}
case 3:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
default: 
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
}
case 2:
{
switch(lean_obj_tag(v_x_57_))
{
case 2:
{
uint8_t v___x_64_; 
v___x_64_ = 1;
return v___x_64_;
}
case 3:
{
uint8_t v___x_65_; 
v___x_65_ = 0;
return v___x_65_;
}
default: 
{
uint8_t v___x_66_; 
v___x_66_ = 0;
return v___x_66_;
}
}
}
default: 
{
lean_object* v_a_67_; uint8_t v___x_68_; 
v_a_67_ = lean_ctor_get(v_x_56_, 0);
v___x_68_ = 0;
if (lean_obj_tag(v_x_57_) == 3)
{
lean_object* v_a_69_; uint8_t v___x_70_; 
v_a_69_ = lean_ctor_get(v_x_57_, 0);
v___x_70_ = lean_nat_dec_eq(v_a_67_, v_a_69_);
if (v___x_70_ == 0)
{
return v___x_68_;
}
else
{
return v___x_70_;
}
}
else
{
return v___x_68_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken_decEq___boxed(lean_object* v_x_71_, lean_object* v_x_72_){
_start:
{
uint8_t v_res_73_; lean_object* v_r_74_; 
v_res_73_ = lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken_decEq(v_x_71_, v_x_72_);
lean_dec(v_x_72_);
lean_dec(v_x_71_);
v_r_74_ = lean_box(v_res_73_);
return v_r_74_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken(lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
uint8_t v___x_77_; 
v___x_77_ = lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken_decEq(v_x_75_, v_x_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken___boxed(lean_object* v_x_78_, lean_object* v_x_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = lp_oak_x2dspec_Oak_Delimited_instDecidableEqToken(v_x_78_, v_x_79_);
lean_dec(v_x_79_);
lean_dec(v_x_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = lean_unsigned_to_nat(2u);
v___x_92_ = lean_nat_to_int(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = lean_unsigned_to_nat(1u);
v___x_94_ = lean_nat_to_int(v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr(lean_object* v_x_101_, lean_object* v_prec_102_){
_start:
{
lean_object* v___y_104_; lean_object* v___y_111_; lean_object* v___y_118_; 
switch(lean_obj_tag(v_x_101_))
{
case 0:
{
lean_object* v___x_124_; uint8_t v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(1024u);
v___x_125_ = lean_nat_dec_le(v___x_124_, v_prec_102_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
v___x_126_ = lean_obj_once(&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6, &lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6_once, _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6);
v___y_118_ = v___x_126_;
goto v___jp_117_;
}
else
{
lean_object* v___x_127_; 
v___x_127_ = lean_obj_once(&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7, &lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7);
v___y_118_ = v___x_127_;
goto v___jp_117_;
}
}
case 1:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(1024u);
v___x_129_ = lean_nat_dec_le(v___x_128_, v_prec_102_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
v___x_130_ = lean_obj_once(&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6, &lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6_once, _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6);
v___y_111_ = v___x_130_;
goto v___jp_110_;
}
else
{
lean_object* v___x_131_; 
v___x_131_ = lean_obj_once(&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7, &lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7);
v___y_111_ = v___x_131_;
goto v___jp_110_;
}
}
case 2:
{
lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1024u);
v___x_133_ = lean_nat_dec_le(v___x_132_, v_prec_102_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; 
v___x_134_ = lean_obj_once(&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6, &lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6_once, _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6);
v___y_104_ = v___x_134_;
goto v___jp_103_;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_obj_once(&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7, &lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7);
v___y_104_ = v___x_135_;
goto v___jp_103_;
}
}
default: 
{
lean_object* v_a_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_156_; 
v_a_136_ = lean_ctor_get(v_x_101_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v_x_101_);
if (v_isSharedCheck_156_ == 0)
{
v___x_138_ = v_x_101_;
v_isShared_139_ = v_isSharedCheck_156_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_a_136_);
lean_dec(v_x_101_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_156_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___y_141_; lean_object* v___x_152_; uint8_t v___x_153_; 
v___x_152_ = lean_unsigned_to_nat(1024u);
v___x_153_ = lean_nat_dec_le(v___x_152_, v_prec_102_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; 
v___x_154_ = lean_obj_once(&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6, &lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6_once, _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__6);
v___y_141_ = v___x_154_;
goto v___jp_140_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7, &lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7_once, _init_lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__7);
v___y_141_ = v___x_155_;
goto v___jp_140_;
}
v___jp_140_:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_145_; 
v___x_142_ = ((lean_object*)(lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__10));
v___x_143_ = l_Nat_reprFast(v_a_136_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 0, v___x_143_);
v___x_145_ = v___x_138_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v___x_143_);
v___x_145_ = v_reuseFailAlloc_151_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
lean_object* v___x_146_; lean_object* v___x_147_; uint8_t v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_146_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_146_, 0, v___x_142_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
lean_inc(v___y_141_);
v___x_147_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_147_, 0, v___y_141_);
lean_ctor_set(v___x_147_, 1, v___x_146_);
v___x_148_ = 0;
v___x_149_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_149_, 0, v___x_147_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*1, v___x_148_);
v___x_150_ = l_Repr_addAppParen(v___x_149_, v_prec_102_);
return v___x_150_;
}
}
}
}
}
v___jp_103_:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_105_ = ((lean_object*)(lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__1));
lean_inc(v___y_104_);
v___x_106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_106_, 0, v___y_104_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = 0;
v___x_108_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_108_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_108_, sizeof(void*)*1, v___x_107_);
v___x_109_ = l_Repr_addAppParen(v___x_108_, v_prec_102_);
return v___x_109_;
}
v___jp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v___x_112_ = ((lean_object*)(lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__3));
lean_inc(v___y_111_);
v___x_113_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_113_, 0, v___y_111_);
lean_ctor_set(v___x_113_, 1, v___x_112_);
v___x_114_ = 0;
v___x_115_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*1, v___x_114_);
v___x_116_ = l_Repr_addAppParen(v___x_115_, v_prec_102_);
return v___x_116_;
}
v___jp_117_:
{
lean_object* v___x_119_; lean_object* v___x_120_; uint8_t v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_119_ = ((lean_object*)(lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___closed__5));
lean_inc(v___y_118_);
v___x_120_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_120_, 0, v___y_118_);
lean_ctor_set(v___x_120_, 1, v___x_119_);
v___x_121_ = 0;
v___x_122_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_122_, 0, v___x_120_);
lean_ctor_set_uint8(v___x_122_, sizeof(void*)*1, v___x_121_);
v___x_123_ = l_Repr_addAppParen(v___x_122_, v_prec_102_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_instReprToken_repr___boxed(lean_object* v_x_157_, lean_object* v_prec_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = lp_oak_x2dspec_Oak_Delimited_instReprToken_repr(v_x_157_, v_prec_158_);
lean_dec(v_prec_158_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_body(lean_object* v_x_165_, uint8_t v_x_166_){
_start:
{
if (lean_obj_tag(v_x_165_) == 0)
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
else
{
lean_object* v_tail_168_; 
v_tail_168_ = lean_ctor_get(v_x_165_, 1);
if (lean_obj_tag(v_tail_168_) == 0)
{
if (v_x_166_ == 0)
{
lean_object* v_head_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_178_; 
v_head_169_ = lean_ctor_get(v_x_165_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_178_ == 0)
{
lean_object* v_unused_179_; 
v_unused_179_ = lean_ctor_get(v_x_165_, 1);
lean_dec(v_unused_179_);
v___x_171_ = v_x_165_;
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_head_169_);
lean_dec(v_x_165_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_178_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_173_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_173_, 0, v_head_169_);
v___x_174_ = lean_box(0);
if (v_isShared_172_ == 0)
{
lean_ctor_set(v___x_171_, 1, v___x_174_);
lean_ctor_set(v___x_171_, 0, v___x_173_);
v___x_176_ = v___x_171_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_173_);
lean_ctor_set(v_reuseFailAlloc_177_, 1, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
else
{
lean_object* v_head_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_189_; 
v_head_180_ = lean_ctor_get(v_x_165_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_189_ == 0)
{
lean_object* v_unused_190_; 
v_unused_190_ = lean_ctor_get(v_x_165_, 1);
lean_dec(v_unused_190_);
v___x_182_ = v_x_165_;
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_head_180_);
lean_dec(v_x_165_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_184_, 0, v_head_180_);
v___x_185_ = ((lean_object*)(lp_oak_x2dspec_Oak_Delimited_body___closed__0));
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v___x_185_);
lean_ctor_set(v___x_182_, 0, v___x_184_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_188_, 1, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
else
{
lean_object* v_head_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_202_; 
lean_inc_ref(v_tail_168_);
v_head_191_ = lean_ctor_get(v_x_165_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v_x_165_);
if (v_isSharedCheck_202_ == 0)
{
lean_object* v_unused_203_; 
v_unused_203_ = lean_ctor_get(v_x_165_, 1);
lean_dec(v_unused_203_);
v___x_193_ = v_x_165_;
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_head_191_);
lean_dec(v_x_165_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_202_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_199_; 
v___x_195_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_195_, 0, v_head_191_);
v___x_196_ = lean_box(2);
v___x_197_ = lp_oak_x2dspec_Oak_Delimited_body(v_tail_168_, v_x_166_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 1, v___x_197_);
lean_ctor_set(v___x_193_, 0, v___x_196_);
v___x_199_ = v___x_193_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_197_);
v___x_199_ = v_reuseFailAlloc_201_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
lean_object* v___x_200_; 
v___x_200_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_195_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
return v___x_200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_body___boxed(lean_object* v_x_204_, lean_object* v_x_205_){
_start:
{
uint8_t v_x_61__boxed_206_; lean_object* v_res_207_; 
v_x_61__boxed_206_ = lean_unbox(v_x_205_);
v_res_207_ = lp_oak_x2dspec_Oak_Delimited_body(v_x_204_, v_x_61__boxed_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_encode(lean_object* v_items_211_, uint8_t v_trailing_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_213_ = lean_box(0);
v___x_214_ = lp_oak_x2dspec_Oak_Delimited_body(v_items_211_, v_trailing_212_);
v___x_215_ = ((lean_object*)(lp_oak_x2dspec_Oak_Delimited_encode___closed__0));
v___x_216_ = l_List_appendTR___redArg(v___x_214_, v___x_215_);
v___x_217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_217_, 0, v___x_213_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_encode___boxed(lean_object* v_items_218_, lean_object* v_trailing_219_){
_start:
{
uint8_t v_trailing_boxed_220_; lean_object* v_res_221_; 
v_trailing_boxed_220_ = lean_unbox(v_trailing_219_);
v_res_221_ = lp_oak_x2dspec_Oak_Delimited_encode(v_items_218_, v_trailing_boxed_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_closeOffset(lean_object* v_items_222_, uint8_t v_trailing_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_224_ = lean_unsigned_to_nat(1u);
v___x_225_ = lp_oak_x2dspec_Oak_Delimited_body(v_items_222_, v_trailing_223_);
v___x_226_ = l_List_lengthTR___redArg(v___x_225_);
lean_dec(v___x_225_);
v___x_227_ = lean_nat_add(v___x_224_, v___x_226_);
lean_dec(v___x_226_);
return v___x_227_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_closeOffset___boxed(lean_object* v_items_228_, lean_object* v_trailing_229_){
_start:
{
uint8_t v_trailing_boxed_230_; lean_object* v_res_231_; 
v_trailing_boxed_230_ = lean_unbox(v_trailing_229_);
v_res_231_ = lp_oak_x2dspec_Oak_Delimited_closeOffset(v_items_228_, v_trailing_boxed_230_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_Delimited_itemValues(lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v___x_233_; 
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v_head_234_; 
v_head_234_ = lean_ctor_get(v_x_232_, 0);
if (lean_obj_tag(v_head_234_) == 3)
{
lean_object* v_tail_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_244_; 
lean_inc_ref(v_head_234_);
v_tail_235_ = lean_ctor_get(v_x_232_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_244_ == 0)
{
lean_object* v_unused_245_; 
v_unused_245_ = lean_ctor_get(v_x_232_, 0);
lean_dec(v_unused_245_);
v___x_237_ = v_x_232_;
v_isShared_238_ = v_isSharedCheck_244_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_tail_235_);
lean_dec(v_x_232_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_244_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_a_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v_a_239_ = lean_ctor_get(v_head_234_, 0);
lean_inc(v_a_239_);
lean_dec_ref_known(v_head_234_, 1);
v___x_240_ = lp_oak_x2dspec_Oak_Delimited_itemValues(v_tail_235_);
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v___x_240_);
lean_ctor_set(v___x_237_, 0, v_a_239_);
v___x_242_ = v___x_237_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_a_239_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
lean_object* v_tail_246_; 
v_tail_246_ = lean_ctor_get(v_x_232_, 1);
lean_inc(v_tail_246_);
lean_dec_ref_known(v_x_232_, 2);
v_x_232_ = v_tail_246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_itemValues_match__1_splitter___redArg(lean_object* v_x_248_, lean_object* v_h__1_249_, lean_object* v_h__2_250_, lean_object* v_h__3_251_){
_start:
{
if (lean_obj_tag(v_x_248_) == 0)
{
lean_object* v___x_252_; lean_object* v___x_253_; 
lean_dec(v_h__3_251_);
lean_dec(v_h__2_250_);
v___x_252_ = lean_box(0);
v___x_253_ = lean_apply_1(v_h__1_249_, v___x_252_);
return v___x_253_;
}
else
{
lean_object* v_head_254_; 
lean_dec(v_h__1_249_);
v_head_254_ = lean_ctor_get(v_x_248_, 0);
lean_inc(v_head_254_);
if (lean_obj_tag(v_head_254_) == 3)
{
lean_object* v_tail_255_; lean_object* v_a_256_; lean_object* v___x_257_; 
lean_dec(v_h__3_251_);
v_tail_255_ = lean_ctor_get(v_x_248_, 1);
lean_inc(v_tail_255_);
lean_dec_ref_known(v_x_248_, 2);
v_a_256_ = lean_ctor_get(v_head_254_, 0);
lean_inc(v_a_256_);
lean_dec_ref_known(v_head_254_, 1);
v___x_257_ = lean_apply_2(v_h__2_250_, v_a_256_, v_tail_255_);
return v___x_257_;
}
else
{
lean_object* v_tail_258_; lean_object* v___x_259_; 
lean_dec(v_h__2_250_);
v_tail_258_ = lean_ctor_get(v_x_248_, 1);
lean_inc(v_tail_258_);
lean_dec_ref_known(v_x_248_, 2);
v___x_259_ = lean_apply_3(v_h__3_251_, v_head_254_, v_tail_258_, lean_box(0));
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_itemValues_match__1_splitter(lean_object* v_motive_260_, lean_object* v_x_261_, lean_object* v_h__1_262_, lean_object* v_h__2_263_, lean_object* v_h__3_264_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec(v_h__3_264_);
lean_dec(v_h__2_263_);
v___x_265_ = lean_box(0);
v___x_266_ = lean_apply_1(v_h__1_262_, v___x_265_);
return v___x_266_;
}
else
{
lean_object* v_head_267_; 
lean_dec(v_h__1_262_);
v_head_267_ = lean_ctor_get(v_x_261_, 0);
lean_inc(v_head_267_);
if (lean_obj_tag(v_head_267_) == 3)
{
lean_object* v_tail_268_; lean_object* v_a_269_; lean_object* v___x_270_; 
lean_dec(v_h__3_264_);
v_tail_268_ = lean_ctor_get(v_x_261_, 1);
lean_inc(v_tail_268_);
lean_dec_ref_known(v_x_261_, 2);
v_a_269_ = lean_ctor_get(v_head_267_, 0);
lean_inc(v_a_269_);
lean_dec_ref_known(v_head_267_, 1);
v___x_270_ = lean_apply_2(v_h__2_263_, v_a_269_, v_tail_268_);
return v___x_270_;
}
else
{
lean_object* v_tail_271_; lean_object* v___x_272_; 
lean_dec(v_h__2_263_);
v_tail_271_ = lean_ctor_get(v_x_261_, 1);
lean_inc(v_tail_271_);
lean_dec_ref_known(v_x_261_, 2);
v___x_272_ = lean_apply_3(v_h__3_264_, v_head_267_, v_tail_271_, lean_box(0));
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter___redArg(lean_object* v_x_273_, uint8_t v_x_274_, lean_object* v_h__1_275_, lean_object* v_h__2_276_, lean_object* v_h__3_277_, lean_object* v_h__4_278_){
_start:
{
if (lean_obj_tag(v_x_273_) == 0)
{
lean_object* v___x_279_; lean_object* v___x_280_; 
lean_dec(v_h__4_278_);
lean_dec(v_h__3_277_);
lean_dec(v_h__2_276_);
v___x_279_ = lean_box(v_x_274_);
v___x_280_ = lean_apply_1(v_h__1_275_, v___x_279_);
return v___x_280_;
}
else
{
lean_object* v_tail_281_; 
lean_dec(v_h__1_275_);
v_tail_281_ = lean_ctor_get(v_x_273_, 1);
if (lean_obj_tag(v_tail_281_) == 0)
{
lean_dec(v_h__4_278_);
if (v_x_274_ == 0)
{
lean_object* v_head_282_; lean_object* v___x_283_; 
lean_dec(v_h__3_277_);
v_head_282_ = lean_ctor_get(v_x_273_, 0);
lean_inc(v_head_282_);
lean_dec_ref_known(v_x_273_, 2);
v___x_283_ = lean_apply_1(v_h__2_276_, v_head_282_);
return v___x_283_;
}
else
{
lean_object* v_head_284_; lean_object* v___x_285_; 
lean_dec(v_h__2_276_);
v_head_284_ = lean_ctor_get(v_x_273_, 0);
lean_inc(v_head_284_);
lean_dec_ref_known(v_x_273_, 2);
v___x_285_ = lean_apply_1(v_h__3_277_, v_head_284_);
return v___x_285_;
}
}
else
{
lean_object* v_head_286_; lean_object* v_head_287_; lean_object* v_tail_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
lean_inc_ref(v_tail_281_);
lean_dec(v_h__3_277_);
lean_dec(v_h__2_276_);
v_head_286_ = lean_ctor_get(v_x_273_, 0);
lean_inc(v_head_286_);
lean_dec_ref_known(v_x_273_, 2);
v_head_287_ = lean_ctor_get(v_tail_281_, 0);
lean_inc(v_head_287_);
v_tail_288_ = lean_ctor_get(v_tail_281_, 1);
lean_inc(v_tail_288_);
lean_dec_ref_known(v_tail_281_, 2);
v___x_289_ = lean_box(v_x_274_);
v___x_290_ = lean_apply_4(v_h__4_278_, v_head_286_, v_head_287_, v_tail_288_, v___x_289_);
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter___redArg___boxed(lean_object* v_x_291_, lean_object* v_x_292_, lean_object* v_h__1_293_, lean_object* v_h__2_294_, lean_object* v_h__3_295_, lean_object* v_h__4_296_){
_start:
{
uint8_t v_x_44__boxed_297_; lean_object* v_res_298_; 
v_x_44__boxed_297_ = lean_unbox(v_x_292_);
v_res_298_ = lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter___redArg(v_x_291_, v_x_44__boxed_297_, v_h__1_293_, v_h__2_294_, v_h__3_295_, v_h__4_296_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter(lean_object* v_motive_299_, lean_object* v_x_300_, uint8_t v_x_301_, lean_object* v_h__1_302_, lean_object* v_h__2_303_, lean_object* v_h__3_304_, lean_object* v_h__4_305_){
_start:
{
if (lean_obj_tag(v_x_300_) == 0)
{
lean_object* v___x_306_; lean_object* v___x_307_; 
lean_dec(v_h__4_305_);
lean_dec(v_h__3_304_);
lean_dec(v_h__2_303_);
v___x_306_ = lean_box(v_x_301_);
v___x_307_ = lean_apply_1(v_h__1_302_, v___x_306_);
return v___x_307_;
}
else
{
lean_object* v_tail_308_; 
lean_dec(v_h__1_302_);
v_tail_308_ = lean_ctor_get(v_x_300_, 1);
if (lean_obj_tag(v_tail_308_) == 0)
{
lean_dec(v_h__4_305_);
if (v_x_301_ == 0)
{
lean_object* v_head_309_; lean_object* v___x_310_; 
lean_dec(v_h__3_304_);
v_head_309_ = lean_ctor_get(v_x_300_, 0);
lean_inc(v_head_309_);
lean_dec_ref_known(v_x_300_, 2);
v___x_310_ = lean_apply_1(v_h__2_303_, v_head_309_);
return v___x_310_;
}
else
{
lean_object* v_head_311_; lean_object* v___x_312_; 
lean_dec(v_h__2_303_);
v_head_311_ = lean_ctor_get(v_x_300_, 0);
lean_inc(v_head_311_);
lean_dec_ref_known(v_x_300_, 2);
v___x_312_ = lean_apply_1(v_h__3_304_, v_head_311_);
return v___x_312_;
}
}
else
{
lean_object* v_head_313_; lean_object* v_head_314_; lean_object* v_tail_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
lean_inc_ref(v_tail_308_);
lean_dec(v_h__3_304_);
lean_dec(v_h__2_303_);
v_head_313_ = lean_ctor_get(v_x_300_, 0);
lean_inc(v_head_313_);
lean_dec_ref_known(v_x_300_, 2);
v_head_314_ = lean_ctor_get(v_tail_308_, 0);
lean_inc(v_head_314_);
v_tail_315_ = lean_ctor_get(v_tail_308_, 1);
lean_inc(v_tail_315_);
lean_dec_ref_known(v_tail_308_, 2);
v___x_316_ = lean_box(v_x_301_);
v___x_317_ = lean_apply_4(v_h__4_305_, v_head_313_, v_head_314_, v_tail_315_, v___x_316_);
return v___x_317_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter___boxed(lean_object* v_motive_318_, lean_object* v_x_319_, lean_object* v_x_320_, lean_object* v_h__1_321_, lean_object* v_h__2_322_, lean_object* v_h__3_323_, lean_object* v_h__4_324_){
_start:
{
uint8_t v_x_74__boxed_325_; lean_object* v_res_326_; 
v_x_74__boxed_325_ = lean_unbox(v_x_320_);
v_res_326_ = lp_oak_x2dspec___private_Oak_Delimited_0__Oak_Delimited_body_match__1_splitter(v_motive_318_, v_x_319_, v_x_74__boxed_325_, v_h__1_321_, v_h__2_322_, v_h__3_323_, v_h__4_324_);
return v_res_326_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_Delimited(uint8_t builtin) {
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
