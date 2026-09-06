// Lean compiler output
// Module: Oak.SourcePosition
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf8Width(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf8Width___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf16Width(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf16Width___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "byteOffset"};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__3_value),((lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__9_value;
static const lean_string_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "utf16Column"};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__11_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__12;
static const lean_string_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__13_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__14;
static lean_once_cell_t lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__15;
static const lean_ctor_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__16 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__16_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__13_value)}};
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__17 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_SourcePosition_instReprPosition___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition = (const lean_object*)&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_advance(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_advance___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_advanceText(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_advanceText___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf8Bytes(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf8Bytes___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf16Units(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf16Units___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_SourcePosition_0__Oak_SourcePosition_advanceText_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_SourcePosition_0__Oak_SourcePosition_advanceText_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_SourcePosition_0__Oak_SourcePosition_utf8Bytes_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_SourcePosition_0__Oak_SourcePosition_utf8Bytes_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf8Width(lean_object* v_scalar_1_){
_start:
{
lean_object* v___x_2_; uint8_t v___x_3_; 
v___x_2_ = lean_unsigned_to_nat(127u);
v___x_3_ = lean_nat_dec_le(v_scalar_1_, v___x_2_);
if (v___x_3_ == 0)
{
lean_object* v___x_4_; uint8_t v___x_5_; 
v___x_4_ = lean_unsigned_to_nat(2047u);
v___x_5_ = lean_nat_dec_le(v_scalar_1_, v___x_4_);
if (v___x_5_ == 0)
{
lean_object* v___x_6_; uint8_t v___x_7_; 
v___x_6_ = lean_unsigned_to_nat(65535u);
v___x_7_ = lean_nat_dec_le(v_scalar_1_, v___x_6_);
if (v___x_7_ == 0)
{
lean_object* v___x_8_; 
v___x_8_ = lean_unsigned_to_nat(4u);
return v___x_8_;
}
else
{
lean_object* v___x_9_; 
v___x_9_ = lean_unsigned_to_nat(3u);
return v___x_9_;
}
}
else
{
lean_object* v___x_10_; 
v___x_10_ = lean_unsigned_to_nat(2u);
return v___x_10_;
}
}
else
{
lean_object* v___x_11_; 
v___x_11_ = lean_unsigned_to_nat(1u);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf8Width___boxed(lean_object* v_scalar_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = lp_oak_x2dspec_Oak_SourcePosition_utf8Width(v_scalar_12_);
lean_dec(v_scalar_12_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf16Width(lean_object* v_scalar_14_){
_start:
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_unsigned_to_nat(65535u);
v___x_16_ = lean_nat_dec_le(v_scalar_14_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; 
v___x_17_ = lean_unsigned_to_nat(2u);
return v___x_17_;
}
else
{
lean_object* v___x_18_; 
v___x_18_ = lean_unsigned_to_nat(1u);
return v___x_18_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf16Width___boxed(lean_object* v_scalar_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = lp_oak_x2dspec_Oak_SourcePosition_utf16Width(v_scalar_19_);
lean_dec(v_scalar_19_);
return v_res_20_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition_decEq(lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
lean_object* v_byteOffset_23_; lean_object* v_utf16Column_24_; lean_object* v_byteOffset_25_; lean_object* v_utf16Column_26_; uint8_t v___x_27_; 
v_byteOffset_23_ = lean_ctor_get(v_x_21_, 0);
v_utf16Column_24_ = lean_ctor_get(v_x_21_, 1);
v_byteOffset_25_ = lean_ctor_get(v_x_22_, 0);
v_utf16Column_26_ = lean_ctor_get(v_x_22_, 1);
v___x_27_ = lean_nat_dec_eq(v_byteOffset_23_, v_byteOffset_25_);
if (v___x_27_ == 0)
{
return v___x_27_;
}
else
{
uint8_t v___x_28_; 
v___x_28_ = lean_nat_dec_eq(v_utf16Column_24_, v_utf16Column_26_);
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition_decEq___boxed(lean_object* v_x_29_, lean_object* v_x_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition_decEq(v_x_29_, v_x_30_);
lean_dec_ref(v_x_30_);
lean_dec_ref(v_x_29_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition(lean_object* v_x_33_, lean_object* v_x_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition_decEq(v_x_33_, v_x_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition___boxed(lean_object* v_x_36_, lean_object* v_x_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = lp_oak_x2dspec_Oak_SourcePosition_instDecidableEqPosition(v_x_36_, v_x_37_);
lean_dec_ref(v_x_37_);
lean_dec_ref(v_x_36_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; 
v___x_53_ = lean_unsigned_to_nat(14u);
v___x_54_ = lean_nat_to_int(v___x_53_);
return v___x_54_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(15u);
v___x_62_ = lean_nat_to_int(v___x_61_);
return v___x_62_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__0));
v___x_65_ = lean_string_length(v___x_64_);
return v___x_65_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_66_ = lean_obj_once(&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__14, &lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__14_once, _init_lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__14);
v___x_67_ = lean_nat_to_int(v___x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg(lean_object* v_x_72_){
_start:
{
lean_object* v_byteOffset_73_; lean_object* v_utf16Column_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_109_; 
v_byteOffset_73_ = lean_ctor_get(v_x_72_, 0);
v_utf16Column_74_ = lean_ctor_get(v_x_72_, 1);
v_isSharedCheck_109_ = !lean_is_exclusive(v_x_72_);
if (v_isSharedCheck_109_ == 0)
{
v___x_76_ = v_x_72_;
v_isShared_77_ = v_isSharedCheck_109_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_utf16Column_74_);
lean_inc(v_byteOffset_73_);
lean_dec(v_x_72_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_109_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_84_; 
v___x_78_ = ((lean_object*)(lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__5));
v___x_79_ = ((lean_object*)(lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__6));
v___x_80_ = lean_obj_once(&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__7);
v___x_81_ = l_Nat_reprFast(v_byteOffset_73_);
v___x_82_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
if (v_isShared_77_ == 0)
{
lean_ctor_set_tag(v___x_76_, 4);
lean_ctor_set(v___x_76_, 1, v___x_82_);
lean_ctor_set(v___x_76_, 0, v___x_80_);
v___x_84_ = v___x_76_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_108_; 
v_reuseFailAlloc_108_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_108_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_108_, 1, v___x_82_);
v___x_84_ = v_reuseFailAlloc_108_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_85_ = 0;
v___x_86_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_86_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*1, v___x_85_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_79_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = ((lean_object*)(lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__9));
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_box(1);
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_89_);
lean_ctor_set(v___x_91_, 1, v___x_90_);
v___x_92_ = ((lean_object*)(lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__11));
v___x_93_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_91_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set(v___x_94_, 1, v___x_78_);
v___x_95_ = lean_obj_once(&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__12, &lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__12_once, _init_lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__12);
v___x_96_ = l_Nat_reprFast(v_utf16Column_74_);
v___x_97_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
v___x_98_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_95_);
lean_ctor_set(v___x_98_, 1, v___x_97_);
v___x_99_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set_uint8(v___x_99_, sizeof(void*)*1, v___x_85_);
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_94_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_obj_once(&lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__15);
v___x_102_ = ((lean_object*)(lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__16));
v___x_103_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set(v___x_103_, 1, v___x_100_);
v___x_104_ = ((lean_object*)(lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg___closed__17));
v___x_105_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v___x_104_);
v___x_106_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_106_, 0, v___x_101_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set_uint8(v___x_107_, sizeof(void*)*1, v___x_85_);
return v___x_107_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr(lean_object* v_x_110_, lean_object* v_prec_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___redArg(v_x_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr___boxed(lean_object* v_x_113_, lean_object* v_prec_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = lp_oak_x2dspec_Oak_SourcePosition_instReprPosition_repr(v_x_113_, v_prec_114_);
lean_dec(v_prec_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_advance(lean_object* v_p_118_, lean_object* v_scalar_119_){
_start:
{
lean_object* v_byteOffset_120_; lean_object* v_utf16Column_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_132_; 
v_byteOffset_120_ = lean_ctor_get(v_p_118_, 0);
v_utf16Column_121_ = lean_ctor_get(v_p_118_, 1);
v_isSharedCheck_132_ = !lean_is_exclusive(v_p_118_);
if (v_isSharedCheck_132_ == 0)
{
v___x_123_ = v_p_118_;
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_utf16Column_121_);
lean_inc(v_byteOffset_120_);
lean_dec(v_p_118_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_132_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_130_; 
v___x_125_ = lp_oak_x2dspec_Oak_SourcePosition_utf8Width(v_scalar_119_);
v___x_126_ = lean_nat_add(v_byteOffset_120_, v___x_125_);
lean_dec(v___x_125_);
lean_dec(v_byteOffset_120_);
v___x_127_ = lp_oak_x2dspec_Oak_SourcePosition_utf16Width(v_scalar_119_);
v___x_128_ = lean_nat_add(v_utf16Column_121_, v___x_127_);
lean_dec(v___x_127_);
lean_dec(v_utf16Column_121_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v___x_128_);
lean_ctor_set(v___x_123_, 0, v___x_126_);
v___x_130_ = v___x_123_;
goto v_reusejp_129_;
}
else
{
lean_object* v_reuseFailAlloc_131_; 
v_reuseFailAlloc_131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_131_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_131_, 1, v___x_128_);
v___x_130_ = v_reuseFailAlloc_131_;
goto v_reusejp_129_;
}
v_reusejp_129_:
{
return v___x_130_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_advance___boxed(lean_object* v_p_133_, lean_object* v_scalar_134_){
_start:
{
lean_object* v_res_135_; 
v_res_135_ = lp_oak_x2dspec_Oak_SourcePosition_advance(v_p_133_, v_scalar_134_);
lean_dec(v_scalar_134_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_advanceText(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
return v_x_136_;
}
else
{
lean_object* v_head_138_; lean_object* v_tail_139_; lean_object* v___x_140_; 
v_head_138_ = lean_ctor_get(v_x_137_, 0);
v_tail_139_ = lean_ctor_get(v_x_137_, 1);
v___x_140_ = lp_oak_x2dspec_Oak_SourcePosition_advance(v_x_136_, v_head_138_);
v_x_136_ = v___x_140_;
v_x_137_ = v_tail_139_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_advanceText___boxed(lean_object* v_x_142_, lean_object* v_x_143_){
_start:
{
lean_object* v_res_144_; 
v_res_144_ = lp_oak_x2dspec_Oak_SourcePosition_advanceText(v_x_142_, v_x_143_);
lean_dec(v_x_143_);
return v_res_144_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf8Bytes(lean_object* v_x_145_){
_start:
{
if (lean_obj_tag(v_x_145_) == 0)
{
lean_object* v___x_146_; 
v___x_146_ = lean_unsigned_to_nat(0u);
return v___x_146_;
}
else
{
lean_object* v_head_147_; lean_object* v_tail_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_head_147_ = lean_ctor_get(v_x_145_, 0);
v_tail_148_ = lean_ctor_get(v_x_145_, 1);
v___x_149_ = lp_oak_x2dspec_Oak_SourcePosition_utf8Width(v_head_147_);
v___x_150_ = lp_oak_x2dspec_Oak_SourcePosition_utf8Bytes(v_tail_148_);
v___x_151_ = lean_nat_add(v___x_149_, v___x_150_);
lean_dec(v___x_150_);
lean_dec(v___x_149_);
return v___x_151_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf8Bytes___boxed(lean_object* v_x_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = lp_oak_x2dspec_Oak_SourcePosition_utf8Bytes(v_x_152_);
lean_dec(v_x_152_);
return v_res_153_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf16Units(lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v___x_155_; 
v___x_155_ = lean_unsigned_to_nat(0u);
return v___x_155_;
}
else
{
lean_object* v_head_156_; lean_object* v_tail_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_head_156_ = lean_ctor_get(v_x_154_, 0);
v_tail_157_ = lean_ctor_get(v_x_154_, 1);
v___x_158_ = lp_oak_x2dspec_Oak_SourcePosition_utf16Width(v_head_156_);
v___x_159_ = lp_oak_x2dspec_Oak_SourcePosition_utf16Units(v_tail_157_);
v___x_160_ = lean_nat_add(v___x_158_, v___x_159_);
lean_dec(v___x_159_);
lean_dec(v___x_158_);
return v___x_160_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_SourcePosition_utf16Units___boxed(lean_object* v_x_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = lp_oak_x2dspec_Oak_SourcePosition_utf16Units(v_x_161_);
lean_dec(v_x_161_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_SourcePosition_0__Oak_SourcePosition_advanceText_match__1_splitter___redArg(lean_object* v_x_163_, lean_object* v_x_164_, lean_object* v_h__1_165_, lean_object* v_h__2_166_){
_start:
{
if (lean_obj_tag(v_x_164_) == 0)
{
lean_object* v___x_167_; 
lean_dec(v_h__2_166_);
v___x_167_ = lean_apply_1(v_h__1_165_, v_x_163_);
return v___x_167_;
}
else
{
lean_object* v_head_168_; lean_object* v_tail_169_; lean_object* v___x_170_; 
lean_dec(v_h__1_165_);
v_head_168_ = lean_ctor_get(v_x_164_, 0);
lean_inc(v_head_168_);
v_tail_169_ = lean_ctor_get(v_x_164_, 1);
lean_inc(v_tail_169_);
lean_dec_ref_known(v_x_164_, 2);
v___x_170_ = lean_apply_3(v_h__2_166_, v_x_163_, v_head_168_, v_tail_169_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_SourcePosition_0__Oak_SourcePosition_advanceText_match__1_splitter(lean_object* v_motive_171_, lean_object* v_x_172_, lean_object* v_x_173_, lean_object* v_h__1_174_, lean_object* v_h__2_175_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_object* v___x_176_; 
lean_dec(v_h__2_175_);
v___x_176_ = lean_apply_1(v_h__1_174_, v_x_172_);
return v___x_176_;
}
else
{
lean_object* v_head_177_; lean_object* v_tail_178_; lean_object* v___x_179_; 
lean_dec(v_h__1_174_);
v_head_177_ = lean_ctor_get(v_x_173_, 0);
lean_inc(v_head_177_);
v_tail_178_ = lean_ctor_get(v_x_173_, 1);
lean_inc(v_tail_178_);
lean_dec_ref_known(v_x_173_, 2);
v___x_179_ = lean_apply_3(v_h__2_175_, v_x_172_, v_head_177_, v_tail_178_);
return v___x_179_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_SourcePosition_0__Oak_SourcePosition_utf8Bytes_match__1_splitter___redArg(lean_object* v_x_180_, lean_object* v_h__1_181_, lean_object* v_h__2_182_){
_start:
{
if (lean_obj_tag(v_x_180_) == 0)
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v_h__2_182_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_apply_1(v_h__1_181_, v___x_183_);
return v___x_184_;
}
else
{
lean_object* v_head_185_; lean_object* v_tail_186_; lean_object* v___x_187_; 
lean_dec(v_h__1_181_);
v_head_185_ = lean_ctor_get(v_x_180_, 0);
lean_inc(v_head_185_);
v_tail_186_ = lean_ctor_get(v_x_180_, 1);
lean_inc(v_tail_186_);
lean_dec_ref_known(v_x_180_, 2);
v___x_187_ = lean_apply_2(v_h__2_182_, v_head_185_, v_tail_186_);
return v___x_187_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_SourcePosition_0__Oak_SourcePosition_utf8Bytes_match__1_splitter(lean_object* v_motive_188_, lean_object* v_x_189_, lean_object* v_h__1_190_, lean_object* v_h__2_191_){
_start:
{
if (lean_obj_tag(v_x_189_) == 0)
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec(v_h__2_191_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_apply_1(v_h__1_190_, v___x_192_);
return v___x_193_;
}
else
{
lean_object* v_head_194_; lean_object* v_tail_195_; lean_object* v___x_196_; 
lean_dec(v_h__1_190_);
v_head_194_ = lean_ctor_get(v_x_189_, 0);
lean_inc(v_head_194_);
v_tail_195_ = lean_ctor_get(v_x_189_, 1);
lean_inc(v_tail_195_);
lean_dec_ref_known(v_x_189_, 2);
v___x_196_ = lean_apply_2(v_h__2_191_, v_head_194_, v_tail_195_);
return v___x_196_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_SourcePosition(uint8_t builtin) {
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
