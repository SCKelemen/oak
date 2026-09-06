// Lean compiler output
// Module: Oak.GenericConstraintRefinement
// Imports: public import Init public meta import Init public import Oak.RecordShapeRefinement
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
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableEqList___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lp_oak_x2dspec_List_all___at___00Oak_RecordShapeRefinement_SatisfiesBool_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_var_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_var_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_atom_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_atom_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_record_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_record_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_unary_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_unary_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Oak.GenericConstraintRefinement.Ty.var"};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__2_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3;
static lean_once_cell_t lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4;
static const lean_string_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Oak.GenericConstraintRefinement.Ty.atom"};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__6_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__7 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__7_value;
static const lean_string_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "Oak.GenericConstraintRefinement.Ty.record"};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__9_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__10_value;
static const lean_string_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "Oak.GenericConstraintRefinement.Ty.unary"};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__11_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__11_value)}};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__12 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__12_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__12_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__13_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy = (const lean_object*)&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Substitute(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Substitute___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Infer(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Infer___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GenericConstraintRefinement_Discharge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Discharge___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Invoke(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Invoke___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_Infer_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_Infer_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_instReprTy_repr_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_instReprTy_repr_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_Discharge_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_Discharge_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorIdx___boxed(lean_object* v_x_6_){
_start:
{
lean_object* v_res_7_; 
v_res_7_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorIdx(v_x_6_);
lean_dec_ref(v_x_6_);
return v_res_7_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(lean_object* v_t_8_, lean_object* v_k_9_){
_start:
{
if (lean_obj_tag(v_t_8_) == 3)
{
lean_object* v_a_10_; lean_object* v_a_11_; lean_object* v___x_12_; 
v_a_10_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_a_10_);
v_a_11_ = lean_ctor_get(v_t_8_, 1);
lean_inc_ref(v_a_11_);
lean_dec_ref_known(v_t_8_, 2);
v___x_12_ = lean_apply_2(v_k_9_, v_a_10_, v_a_11_);
return v___x_12_;
}
else
{
lean_object* v_a_13_; lean_object* v___x_14_; 
v_a_13_ = lean_ctor_get(v_t_8_, 0);
lean_inc(v_a_13_);
lean_dec_ref(v_t_8_);
v___x_14_ = lean_apply_1(v_k_9_, v_a_13_);
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v___x_20_; 
v___x_20_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(v_t_17_, v_k_19_);
return v___x_20_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___boxed(lean_object* v_motive_21_, lean_object* v_ctorIdx_22_, lean_object* v_t_23_, lean_object* v_h_24_, lean_object* v_k_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim(v_motive_21_, v_ctorIdx_22_, v_t_23_, v_h_24_, v_k_25_);
lean_dec(v_ctorIdx_22_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_var_elim___redArg(lean_object* v_t_27_, lean_object* v_var_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(v_t_27_, v_var_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_var_elim(lean_object* v_motive_30_, lean_object* v_t_31_, lean_object* v_h_32_, lean_object* v_var_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(v_t_31_, v_var_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_atom_elim___redArg(lean_object* v_t_35_, lean_object* v_atom_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(v_t_35_, v_atom_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_atom_elim(lean_object* v_motive_38_, lean_object* v_t_39_, lean_object* v_h_40_, lean_object* v_atom_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(v_t_39_, v_atom_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_record_elim___redArg(lean_object* v_t_43_, lean_object* v_record_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(v_t_43_, v_record_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_record_elim(lean_object* v_motive_46_, lean_object* v_t_47_, lean_object* v_h_48_, lean_object* v_record_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(v_t_47_, v_record_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_unary_elim___redArg(lean_object* v_t_51_, lean_object* v_unary_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(v_t_51_, v_unary_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_unary_elim(lean_object* v_motive_54_, lean_object* v_t_55_, lean_object* v_h_56_, lean_object* v_unary_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Ty_ctorElim___redArg(v_t_55_, v_unary_57_);
return v___x_58_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy_decEq(lean_object* v_x_59_, lean_object* v_x_60_){
_start:
{
switch(lean_obj_tag(v_x_59_))
{
case 0:
{
if (lean_obj_tag(v_x_60_) == 0)
{
lean_object* v_a_61_; lean_object* v_a_62_; uint8_t v___x_63_; 
v_a_61_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_a_61_);
lean_dec_ref_known(v_x_59_, 1);
v_a_62_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_a_62_);
lean_dec_ref_known(v_x_60_, 1);
v___x_63_ = lean_nat_dec_eq(v_a_61_, v_a_62_);
lean_dec(v_a_62_);
lean_dec(v_a_61_);
return v___x_63_;
}
else
{
uint8_t v___x_64_; 
lean_dec_ref_known(v_x_59_, 1);
lean_dec_ref(v_x_60_);
v___x_64_ = 0;
return v___x_64_;
}
}
case 1:
{
if (lean_obj_tag(v_x_60_) == 1)
{
lean_object* v_a_65_; lean_object* v_a_66_; uint8_t v___x_67_; 
v_a_65_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_a_65_);
lean_dec_ref_known(v_x_59_, 1);
v_a_66_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_a_66_);
lean_dec_ref_known(v_x_60_, 1);
v___x_67_ = lean_nat_dec_eq(v_a_65_, v_a_66_);
lean_dec(v_a_66_);
lean_dec(v_a_65_);
return v___x_67_;
}
else
{
uint8_t v___x_68_; 
lean_dec_ref_known(v_x_59_, 1);
lean_dec_ref(v_x_60_);
v___x_68_ = 0;
return v___x_68_;
}
}
case 2:
{
if (lean_obj_tag(v_x_60_) == 2)
{
lean_object* v_a_69_; lean_object* v_a_70_; lean_object* v___x_71_; uint8_t v___x_72_; 
v_a_69_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_a_69_);
lean_dec_ref_known(v_x_59_, 1);
v_a_70_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_a_70_);
lean_dec_ref_known(v_x_60_, 1);
v___x_71_ = lean_alloc_closure((void*)(lp_oak_x2dspec_Oak_RecordShape_instDecidableEqField___boxed), 2, 0);
v___x_72_ = l_instDecidableEqList___redArg(v___x_71_, v_a_69_, v_a_70_);
return v___x_72_;
}
else
{
uint8_t v___x_73_; 
lean_dec_ref_known(v_x_59_, 1);
lean_dec_ref(v_x_60_);
v___x_73_ = 0;
return v___x_73_;
}
}
default: 
{
if (lean_obj_tag(v_x_60_) == 3)
{
lean_object* v_a_74_; lean_object* v_a_75_; lean_object* v_a_76_; lean_object* v_a_77_; uint8_t v___x_78_; 
v_a_74_ = lean_ctor_get(v_x_59_, 0);
lean_inc(v_a_74_);
v_a_75_ = lean_ctor_get(v_x_59_, 1);
lean_inc_ref(v_a_75_);
lean_dec_ref_known(v_x_59_, 2);
v_a_76_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_a_76_);
v_a_77_ = lean_ctor_get(v_x_60_, 1);
lean_inc_ref(v_a_77_);
lean_dec_ref_known(v_x_60_, 2);
v___x_78_ = lean_nat_dec_eq(v_a_74_, v_a_76_);
lean_dec(v_a_76_);
lean_dec(v_a_74_);
if (v___x_78_ == 0)
{
lean_dec_ref(v_a_77_);
lean_dec_ref(v_a_75_);
return v___x_78_;
}
else
{
v_x_59_ = v_a_75_;
v_x_60_ = v_a_77_;
goto _start;
}
}
else
{
uint8_t v___x_80_; 
lean_dec_ref_known(v_x_59_, 2);
lean_dec_ref(v_x_60_);
v___x_80_ = 0;
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy_decEq___boxed(lean_object* v_x_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy_decEq(v_x_81_, v_x_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
uint8_t v___x_87_; 
v___x_87_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy_decEq(v_x_85_, v_x_86_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy___boxed(lean_object* v_x_88_, lean_object* v_x_89_){
_start:
{
uint8_t v_res_90_; lean_object* v_r_91_; 
v_res_90_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_instDecidableEqTy(v_x_88_, v_x_89_);
v_r_91_ = lean_box(v_res_90_);
return v_r_91_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3(void){
_start:
{
lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_98_ = lean_unsigned_to_nat(2u);
v___x_99_ = lean_nat_to_int(v___x_98_);
return v___x_99_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4(void){
_start:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_unsigned_to_nat(1u);
v___x_101_ = lean_nat_to_int(v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr(lean_object* v_x_120_, lean_object* v_prec_121_){
_start:
{
switch(lean_obj_tag(v_x_120_))
{
case 0:
{
lean_object* v_a_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_142_; 
v_a_122_ = lean_ctor_get(v_x_120_, 0);
v_isSharedCheck_142_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_142_ == 0)
{
v___x_124_ = v_x_120_;
v_isShared_125_ = v_isSharedCheck_142_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_a_122_);
lean_dec(v_x_120_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_142_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___y_127_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = lean_unsigned_to_nat(1024u);
v___x_139_ = lean_nat_dec_le(v___x_138_, v_prec_121_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; 
v___x_140_ = lean_obj_once(&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3, &lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3_once, _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3);
v___y_127_ = v___x_140_;
goto v___jp_126_;
}
else
{
lean_object* v___x_141_; 
v___x_141_ = lean_obj_once(&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4, &lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4);
v___y_127_ = v___x_141_;
goto v___jp_126_;
}
v___jp_126_:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_131_; 
v___x_128_ = ((lean_object*)(lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__2));
v___x_129_ = l_Nat_reprFast(v_a_122_);
if (v_isShared_125_ == 0)
{
lean_ctor_set_tag(v___x_124_, 3);
lean_ctor_set(v___x_124_, 0, v___x_129_);
v___x_131_ = v___x_124_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_129_);
v___x_131_ = v_reuseFailAlloc_137_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_132_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_128_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
lean_inc(v___y_127_);
v___x_133_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_133_, 0, v___y_127_);
lean_ctor_set(v___x_133_, 1, v___x_132_);
v___x_134_ = 0;
v___x_135_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_135_, 0, v___x_133_);
lean_ctor_set_uint8(v___x_135_, sizeof(void*)*1, v___x_134_);
v___x_136_ = l_Repr_addAppParen(v___x_135_, v_prec_121_);
return v___x_136_;
}
}
}
}
case 1:
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_163_; 
v_a_143_ = lean_ctor_get(v_x_120_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_163_ == 0)
{
v___x_145_ = v_x_120_;
v_isShared_146_ = v_isSharedCheck_163_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v_x_120_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_163_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___y_148_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_159_ = lean_unsigned_to_nat(1024u);
v___x_160_ = lean_nat_dec_le(v___x_159_, v_prec_121_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
v___x_161_ = lean_obj_once(&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3, &lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3_once, _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3);
v___y_148_ = v___x_161_;
goto v___jp_147_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = lean_obj_once(&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4, &lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4);
v___y_148_ = v___x_162_;
goto v___jp_147_;
}
v___jp_147_:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_149_ = ((lean_object*)(lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__7));
v___x_150_ = l_Nat_reprFast(v_a_143_);
if (v_isShared_146_ == 0)
{
lean_ctor_set_tag(v___x_145_, 3);
lean_ctor_set(v___x_145_, 0, v___x_150_);
v___x_152_ = v___x_145_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_158_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; uint8_t v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_153_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_149_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
lean_inc(v___y_148_);
v___x_154_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_154_, 0, v___y_148_);
lean_ctor_set(v___x_154_, 1, v___x_153_);
v___x_155_ = 0;
v___x_156_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_156_, 0, v___x_154_);
lean_ctor_set_uint8(v___x_156_, sizeof(void*)*1, v___x_155_);
v___x_157_ = l_Repr_addAppParen(v___x_156_, v_prec_121_);
return v___x_157_;
}
}
}
}
case 2:
{
lean_object* v_a_164_; lean_object* v___y_166_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_a_164_ = lean_ctor_get(v_x_120_, 0);
lean_inc(v_a_164_);
lean_dec_ref_known(v_x_120_, 1);
v___x_174_ = lean_unsigned_to_nat(1024u);
v___x_175_ = lean_nat_dec_le(v___x_174_, v_prec_121_);
if (v___x_175_ == 0)
{
lean_object* v___x_176_; 
v___x_176_ = lean_obj_once(&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3, &lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3_once, _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3);
v___y_166_ = v___x_176_;
goto v___jp_165_;
}
else
{
lean_object* v___x_177_; 
v___x_177_ = lean_obj_once(&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4, &lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4);
v___y_166_ = v___x_177_;
goto v___jp_165_;
}
v___jp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; uint8_t v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_167_ = ((lean_object*)(lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__10));
v___x_168_ = lp_oak_x2dspec_List_repr___at___00Oak_RecordShape_instReprSemanticRecord_repr_spec__0___redArg(v_a_164_);
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_167_);
lean_ctor_set(v___x_169_, 1, v___x_168_);
lean_inc(v___y_166_);
v___x_170_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_170_, 0, v___y_166_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = 0;
v___x_172_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set_uint8(v___x_172_, sizeof(void*)*1, v___x_171_);
v___x_173_ = l_Repr_addAppParen(v___x_172_, v_prec_121_);
return v___x_173_;
}
}
default: 
{
lean_object* v_a_178_; lean_object* v_a_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_203_; 
v_a_178_ = lean_ctor_get(v_x_120_, 0);
v_a_179_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_203_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_203_ == 0)
{
v___x_181_ = v_x_120_;
v_isShared_182_ = v_isSharedCheck_203_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_a_179_);
lean_inc(v_a_178_);
lean_dec(v_x_120_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_203_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___y_185_; uint8_t v___x_200_; 
v___x_183_ = lean_unsigned_to_nat(1024u);
v___x_200_ = lean_nat_dec_le(v___x_183_, v_prec_121_);
if (v___x_200_ == 0)
{
lean_object* v___x_201_; 
v___x_201_ = lean_obj_once(&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3, &lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3_once, _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__3);
v___y_185_ = v___x_201_;
goto v___jp_184_;
}
else
{
lean_object* v___x_202_; 
v___x_202_ = lean_obj_once(&lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4, &lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4_once, _init_lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__4);
v___y_185_ = v___x_202_;
goto v___jp_184_;
}
v___jp_184_:
{
lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_186_ = lean_box(1);
v___x_187_ = ((lean_object*)(lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___closed__13));
v___x_188_ = l_Nat_reprFast(v_a_178_);
v___x_189_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
if (v_isShared_182_ == 0)
{
lean_ctor_set_tag(v___x_181_, 5);
lean_ctor_set(v___x_181_, 1, v___x_189_);
lean_ctor_set(v___x_181_, 0, v___x_187_);
v___x_191_ = v___x_181_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v___x_187_);
lean_ctor_set(v_reuseFailAlloc_199_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_199_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_192_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_186_);
v___x_193_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr(v_a_179_, v___x_183_);
v___x_194_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_192_);
lean_ctor_set(v___x_194_, 1, v___x_193_);
lean_inc(v___y_185_);
v___x_195_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_195_, 0, v___y_185_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = 0;
v___x_197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_196_);
v___x_198_ = l_Repr_addAppParen(v___x_197_, v_prec_121_);
return v___x_198_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr___boxed(lean_object* v_x_204_, lean_object* v_prec_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_instReprTy_repr(v_x_204_, v_prec_205_);
lean_dec(v_prec_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Substitute(lean_object* v_v_209_, lean_object* v_replacement_210_, lean_object* v_x_211_){
_start:
{
switch(lean_obj_tag(v_x_211_))
{
case 0:
{
lean_object* v_a_212_; uint8_t v___x_213_; 
v_a_212_ = lean_ctor_get(v_x_211_, 0);
v___x_213_ = lean_nat_dec_eq(v_a_212_, v_v_209_);
if (v___x_213_ == 0)
{
return v_x_211_;
}
else
{
lean_dec_ref_known(v_x_211_, 1);
lean_inc_ref(v_replacement_210_);
return v_replacement_210_;
}
}
case 3:
{
lean_object* v_a_214_; lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_223_; 
v_a_214_ = lean_ctor_get(v_x_211_, 0);
v_a_215_ = lean_ctor_get(v_x_211_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_x_211_);
if (v_isSharedCheck_223_ == 0)
{
v___x_217_ = v_x_211_;
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_inc(v_a_214_);
lean_dec(v_x_211_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_223_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_219_; lean_object* v___x_221_; 
v___x_219_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Substitute(v_v_209_, v_replacement_210_, v_a_215_);
if (v_isShared_218_ == 0)
{
lean_ctor_set(v___x_217_, 1, v___x_219_);
v___x_221_ = v___x_217_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_214_);
lean_ctor_set(v_reuseFailAlloc_222_, 1, v___x_219_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
default: 
{
return v_x_211_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Substitute___boxed(lean_object* v_v_224_, lean_object* v_replacement_225_, lean_object* v_x_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Substitute(v_v_224_, v_replacement_225_, v_x_226_);
lean_dec_ref(v_replacement_225_);
lean_dec(v_v_224_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Infer(lean_object* v_v_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
switch(lean_obj_tag(v_x_229_))
{
case 0:
{
lean_object* v_a_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_240_; 
v_a_231_ = lean_ctor_get(v_x_229_, 0);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_240_ == 0)
{
v___x_233_ = v_x_229_;
v_isShared_234_ = v_isSharedCheck_240_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_a_231_);
lean_dec(v_x_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_240_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
uint8_t v___x_235_; 
v___x_235_ = lean_nat_dec_eq(v_a_231_, v_v_228_);
lean_dec(v_a_231_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_del_object(v___x_233_);
lean_dec_ref(v_x_230_);
v___x_236_ = lean_box(0);
return v___x_236_;
}
else
{
lean_object* v___x_238_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set_tag(v___x_233_, 1);
lean_ctor_set(v___x_233_, 0, v_x_230_);
v___x_238_ = v___x_233_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_x_230_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
}
case 1:
{
lean_dec_ref_known(v_x_229_, 1);
if (lean_obj_tag(v_x_230_) == 1)
{
lean_object* v___x_241_; 
lean_dec_ref_known(v_x_230_, 1);
v___x_241_ = lean_box(0);
return v___x_241_;
}
else
{
lean_object* v___x_242_; 
lean_dec_ref(v_x_230_);
v___x_242_ = lean_box(0);
return v___x_242_;
}
}
case 2:
{
lean_dec_ref_known(v_x_229_, 1);
if (lean_obj_tag(v_x_230_) == 2)
{
lean_object* v___x_243_; 
lean_dec_ref_known(v_x_230_, 1);
v___x_243_ = lean_box(0);
return v___x_243_;
}
else
{
lean_object* v___x_244_; 
lean_dec_ref(v_x_230_);
v___x_244_ = lean_box(0);
return v___x_244_;
}
}
default: 
{
if (lean_obj_tag(v_x_230_) == 3)
{
lean_object* v_a_245_; lean_object* v_a_246_; lean_object* v_a_247_; lean_object* v_a_248_; uint8_t v___x_249_; 
v_a_245_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_a_245_);
v_a_246_ = lean_ctor_get(v_x_229_, 1);
lean_inc_ref(v_a_246_);
lean_dec_ref_known(v_x_229_, 2);
v_a_247_ = lean_ctor_get(v_x_230_, 0);
lean_inc(v_a_247_);
v_a_248_ = lean_ctor_get(v_x_230_, 1);
lean_inc_ref(v_a_248_);
lean_dec_ref_known(v_x_230_, 2);
v___x_249_ = lean_nat_dec_eq(v_a_245_, v_a_247_);
lean_dec(v_a_247_);
lean_dec(v_a_245_);
if (v___x_249_ == 0)
{
lean_object* v___x_250_; 
lean_dec_ref(v_a_248_);
lean_dec_ref(v_a_246_);
v___x_250_ = lean_box(0);
return v___x_250_;
}
else
{
v_x_229_ = v_a_246_;
v_x_230_ = v_a_248_;
goto _start;
}
}
else
{
lean_object* v___x_252_; 
lean_dec_ref_known(v_x_229_, 2);
lean_dec_ref(v_x_230_);
v___x_252_ = lean_box(0);
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Infer___boxed(lean_object* v_v_253_, lean_object* v_x_254_, lean_object* v_x_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Infer(v_v_253_, v_x_254_, v_x_255_);
lean_dec(v_v_253_);
return v_res_256_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_GenericConstraintRefinement_Discharge(lean_object* v_inferred_257_, lean_object* v_required_258_){
_start:
{
if (lean_obj_tag(v_inferred_257_) == 2)
{
lean_object* v_a_259_; uint8_t v___x_260_; 
v_a_259_ = lean_ctor_get(v_inferred_257_, 0);
v___x_260_ = lp_oak_x2dspec_List_all___at___00Oak_RecordShapeRefinement_SatisfiesBool_spec__0(v_a_259_, v_required_258_);
return v___x_260_;
}
else
{
uint8_t v___x_261_; 
v___x_261_ = 0;
return v___x_261_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Discharge___boxed(lean_object* v_inferred_262_, lean_object* v_required_263_){
_start:
{
uint8_t v_res_264_; lean_object* v_r_265_; 
v_res_264_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Discharge(v_inferred_262_, v_required_263_);
lean_dec(v_required_263_);
lean_dec_ref(v_inferred_262_);
v_r_265_ = lean_box(v_res_264_);
return v_r_265_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Invoke(lean_object* v_v_266_, lean_object* v_parameter_267_, lean_object* v_actual_268_, lean_object* v_result_269_, lean_object* v_required_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Infer(v_v_266_, v_parameter_267_, v_actual_268_);
if (lean_obj_tag(v___x_271_) == 0)
{
lean_dec_ref(v_result_269_);
return v___x_271_;
}
else
{
lean_object* v_val_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_282_; 
v_val_272_ = lean_ctor_get(v___x_271_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_271_);
if (v_isSharedCheck_282_ == 0)
{
v___x_274_ = v___x_271_;
v_isShared_275_ = v_isSharedCheck_282_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_val_272_);
lean_dec(v___x_271_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_282_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
uint8_t v___x_276_; 
v___x_276_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Discharge(v_val_272_, v_required_270_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; 
lean_del_object(v___x_274_);
lean_dec(v_val_272_);
lean_dec_ref(v_result_269_);
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
lean_object* v___x_278_; lean_object* v___x_280_; 
v___x_278_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Substitute(v_v_266_, v_val_272_, v_result_269_);
lean_dec(v_val_272_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_278_);
v___x_280_ = v___x_274_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v___x_278_);
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
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_GenericConstraintRefinement_Invoke___boxed(lean_object* v_v_283_, lean_object* v_parameter_284_, lean_object* v_actual_285_, lean_object* v_result_286_, lean_object* v_required_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = lp_oak_x2dspec_Oak_GenericConstraintRefinement_Invoke(v_v_283_, v_parameter_284_, v_actual_285_, v_result_286_, v_required_287_);
lean_dec(v_required_287_);
lean_dec(v_v_283_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_Infer_match__1_splitter___redArg(lean_object* v_x_289_, lean_object* v_x_290_, lean_object* v_h__1_291_, lean_object* v_h__2_292_, lean_object* v_h__3_293_, lean_object* v_h__4_294_, lean_object* v_h__5_295_){
_start:
{
switch(lean_obj_tag(v_x_289_))
{
case 0:
{
lean_object* v_a_296_; lean_object* v___x_297_; 
lean_dec(v_h__5_295_);
lean_dec(v_h__4_294_);
lean_dec(v_h__3_293_);
lean_dec(v_h__2_292_);
v_a_296_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_a_296_);
lean_dec_ref_known(v_x_289_, 1);
v___x_297_ = lean_apply_2(v_h__1_291_, v_a_296_, v_x_290_);
return v___x_297_;
}
case 1:
{
lean_dec(v_h__4_294_);
lean_dec(v_h__3_293_);
lean_dec(v_h__1_291_);
if (lean_obj_tag(v_x_290_) == 1)
{
lean_object* v_a_298_; lean_object* v_a_299_; lean_object* v___x_300_; 
lean_dec(v_h__5_295_);
v_a_298_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_a_298_);
lean_dec_ref_known(v_x_289_, 1);
v_a_299_ = lean_ctor_get(v_x_290_, 0);
lean_inc(v_a_299_);
lean_dec_ref_known(v_x_290_, 1);
v___x_300_ = lean_apply_2(v_h__2_292_, v_a_298_, v_a_299_);
return v___x_300_;
}
else
{
lean_object* v___x_301_; 
lean_dec(v_h__2_292_);
v___x_301_ = lean_apply_6(v_h__5_295_, v_x_289_, v_x_290_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_301_;
}
}
case 2:
{
lean_dec(v_h__4_294_);
lean_dec(v_h__2_292_);
lean_dec(v_h__1_291_);
if (lean_obj_tag(v_x_290_) == 2)
{
lean_object* v_a_302_; lean_object* v_a_303_; lean_object* v___x_304_; 
lean_dec(v_h__5_295_);
v_a_302_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_a_302_);
lean_dec_ref_known(v_x_289_, 1);
v_a_303_ = lean_ctor_get(v_x_290_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v_x_290_, 1);
v___x_304_ = lean_apply_2(v_h__3_293_, v_a_302_, v_a_303_);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
lean_dec(v_h__3_293_);
v___x_305_ = lean_apply_6(v_h__5_295_, v_x_289_, v_x_290_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_305_;
}
}
default: 
{
lean_dec(v_h__3_293_);
lean_dec(v_h__2_292_);
lean_dec(v_h__1_291_);
if (lean_obj_tag(v_x_290_) == 3)
{
lean_object* v_a_306_; lean_object* v_a_307_; lean_object* v_a_308_; lean_object* v_a_309_; lean_object* v___x_310_; 
lean_dec(v_h__5_295_);
v_a_306_ = lean_ctor_get(v_x_289_, 0);
lean_inc(v_a_306_);
v_a_307_ = lean_ctor_get(v_x_289_, 1);
lean_inc_ref(v_a_307_);
lean_dec_ref_known(v_x_289_, 2);
v_a_308_ = lean_ctor_get(v_x_290_, 0);
lean_inc(v_a_308_);
v_a_309_ = lean_ctor_get(v_x_290_, 1);
lean_inc_ref(v_a_309_);
lean_dec_ref_known(v_x_290_, 2);
v___x_310_ = lean_apply_4(v_h__4_294_, v_a_306_, v_a_307_, v_a_308_, v_a_309_);
return v___x_310_;
}
else
{
lean_object* v___x_311_; 
lean_dec(v_h__4_294_);
v___x_311_ = lean_apply_6(v_h__5_295_, v_x_289_, v_x_290_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_311_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_Infer_match__1_splitter(lean_object* v_motive_312_, lean_object* v_x_313_, lean_object* v_x_314_, lean_object* v_h__1_315_, lean_object* v_h__2_316_, lean_object* v_h__3_317_, lean_object* v_h__4_318_, lean_object* v_h__5_319_){
_start:
{
switch(lean_obj_tag(v_x_313_))
{
case 0:
{
lean_object* v_a_320_; lean_object* v___x_321_; 
lean_dec(v_h__5_319_);
lean_dec(v_h__4_318_);
lean_dec(v_h__3_317_);
lean_dec(v_h__2_316_);
v_a_320_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_a_320_);
lean_dec_ref_known(v_x_313_, 1);
v___x_321_ = lean_apply_2(v_h__1_315_, v_a_320_, v_x_314_);
return v___x_321_;
}
case 1:
{
lean_dec(v_h__4_318_);
lean_dec(v_h__3_317_);
lean_dec(v_h__1_315_);
if (lean_obj_tag(v_x_314_) == 1)
{
lean_object* v_a_322_; lean_object* v_a_323_; lean_object* v___x_324_; 
lean_dec(v_h__5_319_);
v_a_322_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_a_322_);
lean_dec_ref_known(v_x_313_, 1);
v_a_323_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_a_323_);
lean_dec_ref_known(v_x_314_, 1);
v___x_324_ = lean_apply_2(v_h__2_316_, v_a_322_, v_a_323_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; 
lean_dec(v_h__2_316_);
v___x_325_ = lean_apply_6(v_h__5_319_, v_x_313_, v_x_314_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_325_;
}
}
case 2:
{
lean_dec(v_h__4_318_);
lean_dec(v_h__2_316_);
lean_dec(v_h__1_315_);
if (lean_obj_tag(v_x_314_) == 2)
{
lean_object* v_a_326_; lean_object* v_a_327_; lean_object* v___x_328_; 
lean_dec(v_h__5_319_);
v_a_326_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_a_326_);
lean_dec_ref_known(v_x_313_, 1);
v_a_327_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_a_327_);
lean_dec_ref_known(v_x_314_, 1);
v___x_328_ = lean_apply_2(v_h__3_317_, v_a_326_, v_a_327_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; 
lean_dec(v_h__3_317_);
v___x_329_ = lean_apply_6(v_h__5_319_, v_x_313_, v_x_314_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_329_;
}
}
default: 
{
lean_dec(v_h__3_317_);
lean_dec(v_h__2_316_);
lean_dec(v_h__1_315_);
if (lean_obj_tag(v_x_314_) == 3)
{
lean_object* v_a_330_; lean_object* v_a_331_; lean_object* v_a_332_; lean_object* v_a_333_; lean_object* v___x_334_; 
lean_dec(v_h__5_319_);
v_a_330_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_a_330_);
v_a_331_ = lean_ctor_get(v_x_313_, 1);
lean_inc_ref(v_a_331_);
lean_dec_ref_known(v_x_313_, 2);
v_a_332_ = lean_ctor_get(v_x_314_, 0);
lean_inc(v_a_332_);
v_a_333_ = lean_ctor_get(v_x_314_, 1);
lean_inc_ref(v_a_333_);
lean_dec_ref_known(v_x_314_, 2);
v___x_334_ = lean_apply_4(v_h__4_318_, v_a_330_, v_a_331_, v_a_332_, v_a_333_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; 
lean_dec(v_h__4_318_);
v___x_335_ = lean_apply_6(v_h__5_319_, v_x_313_, v_x_314_, lean_box(0), lean_box(0), lean_box(0), lean_box(0));
return v___x_335_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_instReprTy_repr_match__1_splitter___redArg(lean_object* v_x_336_, lean_object* v_h__1_337_, lean_object* v_h__2_338_, lean_object* v_h__3_339_, lean_object* v_h__4_340_){
_start:
{
switch(lean_obj_tag(v_x_336_))
{
case 0:
{
lean_object* v_a_341_; lean_object* v___x_342_; 
lean_dec(v_h__4_340_);
lean_dec(v_h__3_339_);
lean_dec(v_h__2_338_);
v_a_341_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v_x_336_, 1);
v___x_342_ = lean_apply_1(v_h__1_337_, v_a_341_);
return v___x_342_;
}
case 1:
{
lean_object* v_a_343_; lean_object* v___x_344_; 
lean_dec(v_h__4_340_);
lean_dec(v_h__3_339_);
lean_dec(v_h__1_337_);
v_a_343_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v_x_336_, 1);
v___x_344_ = lean_apply_1(v_h__2_338_, v_a_343_);
return v___x_344_;
}
case 2:
{
lean_object* v_a_345_; lean_object* v___x_346_; 
lean_dec(v_h__4_340_);
lean_dec(v_h__2_338_);
lean_dec(v_h__1_337_);
v_a_345_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_a_345_);
lean_dec_ref_known(v_x_336_, 1);
v___x_346_ = lean_apply_1(v_h__3_339_, v_a_345_);
return v___x_346_;
}
default: 
{
lean_object* v_a_347_; lean_object* v_a_348_; lean_object* v___x_349_; 
lean_dec(v_h__3_339_);
lean_dec(v_h__2_338_);
lean_dec(v_h__1_337_);
v_a_347_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_a_347_);
v_a_348_ = lean_ctor_get(v_x_336_, 1);
lean_inc_ref(v_a_348_);
lean_dec_ref_known(v_x_336_, 2);
v___x_349_ = lean_apply_2(v_h__4_340_, v_a_347_, v_a_348_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_instReprTy_repr_match__1_splitter(lean_object* v_motive_350_, lean_object* v_x_351_, lean_object* v_h__1_352_, lean_object* v_h__2_353_, lean_object* v_h__3_354_, lean_object* v_h__4_355_){
_start:
{
switch(lean_obj_tag(v_x_351_))
{
case 0:
{
lean_object* v_a_356_; lean_object* v___x_357_; 
lean_dec(v_h__4_355_);
lean_dec(v_h__3_354_);
lean_dec(v_h__2_353_);
v_a_356_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_a_356_);
lean_dec_ref_known(v_x_351_, 1);
v___x_357_ = lean_apply_1(v_h__1_352_, v_a_356_);
return v___x_357_;
}
case 1:
{
lean_object* v_a_358_; lean_object* v___x_359_; 
lean_dec(v_h__4_355_);
lean_dec(v_h__3_354_);
lean_dec(v_h__1_352_);
v_a_358_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_a_358_);
lean_dec_ref_known(v_x_351_, 1);
v___x_359_ = lean_apply_1(v_h__2_353_, v_a_358_);
return v___x_359_;
}
case 2:
{
lean_object* v_a_360_; lean_object* v___x_361_; 
lean_dec(v_h__4_355_);
lean_dec(v_h__2_353_);
lean_dec(v_h__1_352_);
v_a_360_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_a_360_);
lean_dec_ref_known(v_x_351_, 1);
v___x_361_ = lean_apply_1(v_h__3_354_, v_a_360_);
return v___x_361_;
}
default: 
{
lean_object* v_a_362_; lean_object* v_a_363_; lean_object* v___x_364_; 
lean_dec(v_h__3_354_);
lean_dec(v_h__2_353_);
lean_dec(v_h__1_352_);
v_a_362_ = lean_ctor_get(v_x_351_, 0);
lean_inc(v_a_362_);
v_a_363_ = lean_ctor_get(v_x_351_, 1);
lean_inc_ref(v_a_363_);
lean_dec_ref_known(v_x_351_, 2);
v___x_364_ = lean_apply_2(v_h__4_355_, v_a_362_, v_a_363_);
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_Discharge_match__1_splitter___redArg(lean_object* v_inferred_365_, lean_object* v_h__1_366_, lean_object* v_h__2_367_){
_start:
{
if (lean_obj_tag(v_inferred_365_) == 2)
{
lean_object* v_a_368_; lean_object* v___x_369_; 
lean_dec(v_h__2_367_);
v_a_368_ = lean_ctor_get(v_inferred_365_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v_inferred_365_, 1);
v___x_369_ = lean_apply_1(v_h__1_366_, v_a_368_);
return v___x_369_;
}
else
{
lean_object* v___x_370_; 
lean_dec(v_h__1_366_);
v___x_370_ = lean_apply_2(v_h__2_367_, v_inferred_365_, lean_box(0));
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_GenericConstraintRefinement_0__Oak_GenericConstraintRefinement_Discharge_match__1_splitter(lean_object* v_motive_371_, lean_object* v_inferred_372_, lean_object* v_h__1_373_, lean_object* v_h__2_374_){
_start:
{
if (lean_obj_tag(v_inferred_372_) == 2)
{
lean_object* v_a_375_; lean_object* v___x_376_; 
lean_dec(v_h__2_374_);
v_a_375_ = lean_ctor_get(v_inferred_372_, 0);
lean_inc(v_a_375_);
lean_dec_ref_known(v_inferred_372_, 1);
v___x_376_ = lean_apply_1(v_h__1_373_, v_a_375_);
return v___x_376_;
}
else
{
lean_object* v___x_377_; 
lean_dec(v_h__1_373_);
v___x_377_ = lean_apply_2(v_h__2_374_, v_inferred_372_, lean_box(0));
return v___x_377_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_RecordShapeRefinement(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_GenericConstraintRefinement(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_RecordShapeRefinement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
