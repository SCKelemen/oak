// Lean compiler output
// Module: Oak.RecordShapeRefinement
// Imports: public import Init public meta import Init public import Oak.RecordShape
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
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShapeRefinement_Lookup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShapeRefinement_Lookup___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_List_all___at___00Oak_RecordShapeRefinement_SatisfiesBool_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_all___at___00Oak_RecordShapeRefinement_SatisfiesBool_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShapeRefinement_SatisfiesBool(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShapeRefinement_SatisfiesBool___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordShapeRefinement_0__Oak_RecordShapeRefinement_Lookup_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordShapeRefinement_0__Oak_RecordShapeRefinement_Lookup_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordShapeRefinement_0__List_any_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordShapeRefinement_0__List_any_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShapeRefinement_Lookup(lean_object* v_name_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_head_4_; lean_object* v_tail_5_; lean_object* v_name_6_; lean_object* v_ty_7_; uint8_t v___x_8_; 
v_head_4_ = lean_ctor_get(v_x_2_, 0);
v_tail_5_ = lean_ctor_get(v_x_2_, 1);
v_name_6_ = lean_ctor_get(v_head_4_, 0);
v_ty_7_ = lean_ctor_get(v_head_4_, 1);
v___x_8_ = lean_nat_dec_eq(v_name_6_, v_name_1_);
if (v___x_8_ == 0)
{
v_x_2_ = v_tail_5_;
goto _start;
}
else
{
lean_object* v___x_10_; 
lean_inc(v_ty_7_);
v___x_10_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_10_, 0, v_ty_7_);
return v___x_10_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShapeRefinement_Lookup___boxed(lean_object* v_name_11_, lean_object* v_x_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_oak_x2dspec_Oak_RecordShapeRefinement_Lookup(v_name_11_, v_x_12_);
lean_dec(v_x_12_);
lean_dec(v_name_11_);
return v_res_13_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_List_all___at___00Oak_RecordShapeRefinement_SatisfiesBool_spec__0(lean_object* v_candidate_14_, lean_object* v_x_15_){
_start:
{
if (lean_obj_tag(v_x_15_) == 0)
{
uint8_t v___x_16_; 
v___x_16_ = 1;
return v___x_16_;
}
else
{
lean_object* v_head_17_; lean_object* v_tail_18_; lean_object* v_name_19_; lean_object* v_ty_20_; lean_object* v___x_21_; 
v_head_17_ = lean_ctor_get(v_x_15_, 0);
v_tail_18_ = lean_ctor_get(v_x_15_, 1);
v_name_19_ = lean_ctor_get(v_head_17_, 0);
v_ty_20_ = lean_ctor_get(v_head_17_, 1);
v___x_21_ = lp_oak_x2dspec_Oak_RecordShapeRefinement_Lookup(v_name_19_, v_candidate_14_);
if (lean_obj_tag(v___x_21_) == 0)
{
uint8_t v___x_22_; 
v___x_22_ = 0;
return v___x_22_;
}
else
{
lean_object* v_val_23_; uint8_t v___x_24_; 
v_val_23_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_val_23_);
lean_dec_ref_known(v___x_21_, 1);
v___x_24_ = lean_nat_dec_eq(v_val_23_, v_ty_20_);
lean_dec(v_val_23_);
if (v___x_24_ == 0)
{
return v___x_24_;
}
else
{
v_x_15_ = v_tail_18_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_List_all___at___00Oak_RecordShapeRefinement_SatisfiesBool_spec__0___boxed(lean_object* v_candidate_26_, lean_object* v_x_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = lp_oak_x2dspec_List_all___at___00Oak_RecordShapeRefinement_SatisfiesBool_spec__0(v_candidate_26_, v_x_27_);
lean_dec(v_x_27_);
lean_dec(v_candidate_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordShapeRefinement_SatisfiesBool(lean_object* v_candidate_30_, lean_object* v_required_31_){
_start:
{
uint8_t v___x_32_; 
v___x_32_ = lp_oak_x2dspec_List_all___at___00Oak_RecordShapeRefinement_SatisfiesBool_spec__0(v_candidate_30_, v_required_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordShapeRefinement_SatisfiesBool___boxed(lean_object* v_candidate_33_, lean_object* v_required_34_){
_start:
{
uint8_t v_res_35_; lean_object* v_r_36_; 
v_res_35_ = lp_oak_x2dspec_Oak_RecordShapeRefinement_SatisfiesBool(v_candidate_33_, v_required_34_);
lean_dec(v_required_34_);
lean_dec(v_candidate_33_);
v_r_36_ = lean_box(v_res_35_);
return v_r_36_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordShapeRefinement_0__Oak_RecordShapeRefinement_Lookup_match__1_splitter___redArg(lean_object* v_x_37_, lean_object* v_h__1_38_, lean_object* v_h__2_39_){
_start:
{
if (lean_obj_tag(v_x_37_) == 0)
{
lean_object* v___x_40_; lean_object* v___x_41_; 
lean_dec(v_h__2_39_);
v___x_40_ = lean_box(0);
v___x_41_ = lean_apply_1(v_h__1_38_, v___x_40_);
return v___x_41_;
}
else
{
lean_object* v_head_42_; lean_object* v_tail_43_; lean_object* v___x_44_; 
lean_dec(v_h__1_38_);
v_head_42_ = lean_ctor_get(v_x_37_, 0);
lean_inc(v_head_42_);
v_tail_43_ = lean_ctor_get(v_x_37_, 1);
lean_inc(v_tail_43_);
lean_dec_ref_known(v_x_37_, 2);
v___x_44_ = lean_apply_2(v_h__2_39_, v_head_42_, v_tail_43_);
return v___x_44_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordShapeRefinement_0__Oak_RecordShapeRefinement_Lookup_match__1_splitter(lean_object* v_motive_45_, lean_object* v_x_46_, lean_object* v_h__1_47_, lean_object* v_h__2_48_){
_start:
{
if (lean_obj_tag(v_x_46_) == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_h__2_48_);
v___x_49_ = lean_box(0);
v___x_50_ = lean_apply_1(v_h__1_47_, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_head_51_; lean_object* v_tail_52_; lean_object* v___x_53_; 
lean_dec(v_h__1_47_);
v_head_51_ = lean_ctor_get(v_x_46_, 0);
lean_inc(v_head_51_);
v_tail_52_ = lean_ctor_get(v_x_46_, 1);
lean_inc(v_tail_52_);
lean_dec_ref_known(v_x_46_, 2);
v___x_53_ = lean_apply_2(v_h__2_48_, v_head_51_, v_tail_52_);
return v___x_53_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordShapeRefinement_0__List_any_match__1_splitter___redArg(lean_object* v_x_54_, lean_object* v_x_55_, lean_object* v_h__1_56_, lean_object* v_h__2_57_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_object* v___x_58_; 
lean_dec(v_h__2_57_);
v___x_58_ = lean_apply_1(v_h__1_56_, v_x_55_);
return v___x_58_;
}
else
{
lean_object* v_head_59_; lean_object* v_tail_60_; lean_object* v___x_61_; 
lean_dec(v_h__1_56_);
v_head_59_ = lean_ctor_get(v_x_54_, 0);
lean_inc(v_head_59_);
v_tail_60_ = lean_ctor_get(v_x_54_, 1);
lean_inc(v_tail_60_);
lean_dec_ref_known(v_x_54_, 2);
v___x_61_ = lean_apply_3(v_h__2_57_, v_head_59_, v_tail_60_, v_x_55_);
return v___x_61_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordShapeRefinement_0__List_any_match__1_splitter(lean_object* v_00_u03b1_62_, lean_object* v_motive_63_, lean_object* v_x_64_, lean_object* v_x_65_, lean_object* v_h__1_66_, lean_object* v_h__2_67_){
_start:
{
if (lean_obj_tag(v_x_64_) == 0)
{
lean_object* v___x_68_; 
lean_dec(v_h__2_67_);
v___x_68_ = lean_apply_1(v_h__1_66_, v_x_65_);
return v___x_68_;
}
else
{
lean_object* v_head_69_; lean_object* v_tail_70_; lean_object* v___x_71_; 
lean_dec(v_h__1_66_);
v_head_69_ = lean_ctor_get(v_x_64_, 0);
lean_inc(v_head_69_);
v_tail_70_ = lean_ctor_get(v_x_64_, 1);
lean_inc(v_tail_70_);
lean_dec_ref_known(v_x_64_, 2);
v___x_71_ = lean_apply_3(v_h__2_67_, v_head_69_, v_tail_70_, v_x_65_);
return v___x_71_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_RecordShape(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_RecordShapeRefinement(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_RecordShape(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
