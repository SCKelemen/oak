// Lean compiler output
// Module: Oak.BorrowRegions
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
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "offset"};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__3_value),((lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__9_value;
static const lean_string_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "length"};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__11_value;
static const lean_string_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__12 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__12_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__13;
static lean_once_cell_t lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__14;
static const lean_ctor_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__15 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__15_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__12_value)}};
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__16 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__16_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion = (const lean_object*)&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_Region_finish(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_Region_finish___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_offset_3_; lean_object* v_length_4_; lean_object* v_offset_5_; lean_object* v_length_6_; uint8_t v___x_7_; 
v_offset_3_ = lean_ctor_get(v_x_1_, 0);
v_length_4_ = lean_ctor_get(v_x_1_, 1);
v_offset_5_ = lean_ctor_get(v_x_2_, 0);
v_length_6_ = lean_ctor_get(v_x_2_, 1);
v___x_7_ = lean_nat_dec_eq(v_offset_3_, v_offset_5_);
if (v___x_7_ == 0)
{
return v___x_7_;
}
else
{
uint8_t v___x_8_; 
v___x_8_ = lean_nat_dec_eq(v_length_4_, v_length_6_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion_decEq___boxed(lean_object* v_x_9_, lean_object* v_x_10_){
_start:
{
uint8_t v_res_11_; lean_object* v_r_12_; 
v_res_11_ = lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion_decEq(v_x_9_, v_x_10_);
lean_dec_ref(v_x_10_);
lean_dec_ref(v_x_9_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion(lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
uint8_t v___x_15_; 
v___x_15_ = lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion_decEq(v_x_13_, v_x_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion___boxed(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = lp_oak_x2dspec_Oak_BorrowRegions_instDecidableEqRegion(v_x_16_, v_x_17_);
lean_dec_ref(v_x_17_);
lean_dec_ref(v_x_16_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(10u);
v___x_34_ = lean_nat_to_int(v___x_33_);
return v___x_34_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__13(void){
_start:
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = ((lean_object*)(lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__0));
v___x_43_ = lean_string_length(v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_obj_once(&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__13, &lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__13_once, _init_lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__13);
v___x_45_ = lean_nat_to_int(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg(lean_object* v_x_50_){
_start:
{
lean_object* v_offset_51_; lean_object* v_length_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_86_; 
v_offset_51_ = lean_ctor_get(v_x_50_, 0);
v_length_52_ = lean_ctor_get(v_x_50_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_86_ == 0)
{
v___x_54_ = v_x_50_;
v_isShared_55_ = v_isSharedCheck_86_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_length_52_);
lean_inc(v_offset_51_);
lean_dec(v_x_50_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_86_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_56_ = ((lean_object*)(lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__5));
v___x_57_ = ((lean_object*)(lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__6));
v___x_58_ = lean_obj_once(&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__7);
v___x_59_ = l_Nat_reprFast(v_offset_51_);
v___x_60_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_60_, 0, v___x_59_);
if (v_isShared_55_ == 0)
{
lean_ctor_set_tag(v___x_54_, 4);
lean_ctor_set(v___x_54_, 1, v___x_60_);
lean_ctor_set(v___x_54_, 0, v___x_58_);
v___x_62_ = v___x_54_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v___x_58_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v___x_60_);
v___x_62_ = v_reuseFailAlloc_85_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
uint8_t v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_63_ = 0;
v___x_64_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set_uint8(v___x_64_, sizeof(void*)*1, v___x_63_);
v___x_65_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_57_);
lean_ctor_set(v___x_65_, 1, v___x_64_);
v___x_66_ = ((lean_object*)(lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__9));
v___x_67_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_65_);
lean_ctor_set(v___x_67_, 1, v___x_66_);
v___x_68_ = lean_box(1);
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_67_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = ((lean_object*)(lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__11));
v___x_71_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set(v___x_71_, 1, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
lean_ctor_set(v___x_72_, 1, v___x_56_);
v___x_73_ = l_Nat_reprFast(v_length_52_);
v___x_74_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_74_, 0, v___x_73_);
v___x_75_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_58_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*1, v___x_63_);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_72_);
lean_ctor_set(v___x_77_, 1, v___x_76_);
v___x_78_ = lean_obj_once(&lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__14, &lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__14_once, _init_lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__14);
v___x_79_ = ((lean_object*)(lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__15));
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_77_);
v___x_81_ = ((lean_object*)(lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg___closed__16));
v___x_82_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_80_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_78_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_63_);
return v___x_84_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr(lean_object* v_x_87_, lean_object* v_prec_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___redArg(v_x_87_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr___boxed(lean_object* v_x_90_, lean_object* v_prec_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = lp_oak_x2dspec_Oak_BorrowRegions_instReprRegion_repr(v_x_90_, v_prec_91_);
lean_dec(v_prec_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_Region_finish(lean_object* v_r_95_){
_start:
{
lean_object* v_offset_96_; lean_object* v_length_97_; lean_object* v___x_98_; 
v_offset_96_ = lean_ctor_get(v_r_95_, 0);
v_length_97_ = lean_ctor_get(v_r_95_, 1);
v___x_98_ = lean_nat_add(v_offset_96_, v_length_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_BorrowRegions_Region_finish___boxed(lean_object* v_r_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = lp_oak_x2dspec_Oak_BorrowRegions_Region_finish(v_r_99_);
lean_dec_ref(v_r_99_);
return v_res_100_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_BorrowRegions(uint8_t builtin) {
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
