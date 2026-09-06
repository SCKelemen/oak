// Lean compiler output
// Module: Oak.RecordLayout
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
lean_object* lean_nat_mod(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__0_value;
static const lean_string_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "identity"};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__1_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__1_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__2 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__2_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__2_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__3 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__3_value;
static const lean_string_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__4 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__4_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__4_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__5 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__5_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__3_value),((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__5_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__6 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__6_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__7;
static const lean_string_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__8 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__8_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__8_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__9 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__9_value;
static const lean_string_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "size"};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__10 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__10_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__10_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__11 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__11_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__12;
static const lean_string_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "alignment"};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__13 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__13_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__13_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__14 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__14_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__15;
static const lean_string_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__16 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__16_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__17;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__18;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__19 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__19_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__16_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__20 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__20_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec___closed__0_value;
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField_decEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField_decEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField___boxed(lean_object*, lean_object*);
static const lean_string_object lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "offset"};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__0_value;
static const lean_ctor_object lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__0_value)}};
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__1 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__1_value;
static lean_once_cell_t lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__2;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField___closed__0 = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField___closed__0_value;
LEAN_EXPORT const lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField = (const lean_object*)&lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField___closed__0_value;
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_alignUp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_alignUp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_placeFrom(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_placeFrom___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_cursorAfter(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_cursorAfter___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_maxAlignment(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_maxAlignment___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_finalSize(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_finalSize___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_placeFrom_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_placeFrom_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_AllAligned_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_AllAligned_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_NonOverlapping_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_NonOverlapping_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_maxAlignment_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_maxAlignment_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec_decEq(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
lean_object* v_identity_3_; lean_object* v_size_4_; lean_object* v_alignment_5_; lean_object* v_identity_6_; lean_object* v_size_7_; lean_object* v_alignment_8_; uint8_t v___x_9_; 
v_identity_3_ = lean_ctor_get(v_x_1_, 0);
v_size_4_ = lean_ctor_get(v_x_1_, 1);
v_alignment_5_ = lean_ctor_get(v_x_1_, 2);
v_identity_6_ = lean_ctor_get(v_x_2_, 0);
v_size_7_ = lean_ctor_get(v_x_2_, 1);
v_alignment_8_ = lean_ctor_get(v_x_2_, 2);
v___x_9_ = lean_nat_dec_eq(v_identity_3_, v_identity_6_);
if (v___x_9_ == 0)
{
return v___x_9_;
}
else
{
uint8_t v___x_10_; 
v___x_10_ = lean_nat_dec_eq(v_size_4_, v_size_7_);
if (v___x_10_ == 0)
{
return v___x_10_;
}
else
{
uint8_t v___x_11_; 
v___x_11_ = lean_nat_dec_eq(v_alignment_5_, v_alignment_8_);
return v___x_11_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec_decEq___boxed(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec_decEq(v_x_12_, v_x_13_);
lean_dec_ref(v_x_13_);
lean_dec_ref(v_x_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec(lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v___x_18_; 
v___x_18_ = lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec_decEq(v_x_16_, v_x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec___boxed(lean_object* v_x_19_, lean_object* v_x_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqFieldSpec(v_x_19_, v_x_20_);
lean_dec_ref(v_x_20_);
lean_dec_ref(v_x_19_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(12u);
v___x_37_ = lean_nat_to_int(v___x_36_);
return v___x_37_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(8u);
v___x_45_ = lean_nat_to_int(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(13u);
v___x_50_ = lean_nat_to_int(v___x_49_);
return v___x_50_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__17(void){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__0));
v___x_53_ = lean_string_length(v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__18(void){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__17, &lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__17_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__17);
v___x_55_ = lean_nat_to_int(v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg(lean_object* v_x_60_){
_start:
{
lean_object* v_identity_61_; lean_object* v_size_62_; lean_object* v_alignment_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; uint8_t v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_identity_61_ = lean_ctor_get(v_x_60_, 0);
lean_inc(v_identity_61_);
v_size_62_ = lean_ctor_get(v_x_60_, 1);
lean_inc(v_size_62_);
v_alignment_63_ = lean_ctor_get(v_x_60_, 2);
lean_inc(v_alignment_63_);
lean_dec_ref(v_x_60_);
v___x_64_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__5));
v___x_65_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__6));
v___x_66_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__7);
v___x_67_ = l_Nat_reprFast(v_identity_61_);
v___x_68_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_67_);
v___x_69_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_66_);
lean_ctor_set(v___x_69_, 1, v___x_68_);
v___x_70_ = 0;
v___x_71_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_71_, 0, v___x_69_);
lean_ctor_set_uint8(v___x_71_, sizeof(void*)*1, v___x_70_);
v___x_72_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_72_, 0, v___x_65_);
lean_ctor_set(v___x_72_, 1, v___x_71_);
v___x_73_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__9));
v___x_74_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_74_, 0, v___x_72_);
lean_ctor_set(v___x_74_, 1, v___x_73_);
v___x_75_ = lean_box(1);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_74_);
lean_ctor_set(v___x_76_, 1, v___x_75_);
v___x_77_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__11));
v___x_78_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_76_);
lean_ctor_set(v___x_78_, 1, v___x_77_);
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_64_);
v___x_80_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__12, &lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__12_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__12);
v___x_81_ = l_Nat_reprFast(v_size_62_);
v___x_82_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
v___x_83_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_80_);
lean_ctor_set(v___x_83_, 1, v___x_82_);
v___x_84_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_84_, 0, v___x_83_);
lean_ctor_set_uint8(v___x_84_, sizeof(void*)*1, v___x_70_);
v___x_85_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_79_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_85_);
lean_ctor_set(v___x_86_, 1, v___x_73_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_75_);
v___x_88_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__14));
v___x_89_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_64_);
v___x_91_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__15);
v___x_92_ = l_Nat_reprFast(v_alignment_63_);
v___x_93_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
v___x_94_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_94_, 0, v___x_91_);
lean_ctor_set(v___x_94_, 1, v___x_93_);
v___x_95_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_95_, 0, v___x_94_);
lean_ctor_set_uint8(v___x_95_, sizeof(void*)*1, v___x_70_);
v___x_96_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_96_, 0, v___x_90_);
lean_ctor_set(v___x_96_, 1, v___x_95_);
v___x_97_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__18, &lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__18_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__18);
v___x_98_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__19));
v___x_99_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_99_, 0, v___x_98_);
lean_ctor_set(v___x_99_, 1, v___x_96_);
v___x_100_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__20));
v___x_101_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_99_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_102_, 0, v___x_97_);
lean_ctor_set(v___x_102_, 1, v___x_101_);
v___x_103_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_103_, 0, v___x_102_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*1, v___x_70_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr(lean_object* v_x_104_, lean_object* v_prec_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg(v_x_104_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___boxed(lean_object* v_x_107_, lean_object* v_prec_108_){
_start:
{
lean_object* v_res_109_; 
v_res_109_ = lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr(v_x_107_, v_prec_108_);
lean_dec(v_prec_108_);
return v_res_109_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField_decEq(lean_object* v_x_112_, lean_object* v_x_113_){
_start:
{
lean_object* v_identity_114_; lean_object* v_size_115_; lean_object* v_alignment_116_; lean_object* v_offset_117_; lean_object* v_identity_118_; lean_object* v_size_119_; lean_object* v_alignment_120_; lean_object* v_offset_121_; uint8_t v___x_122_; 
v_identity_114_ = lean_ctor_get(v_x_112_, 0);
v_size_115_ = lean_ctor_get(v_x_112_, 1);
v_alignment_116_ = lean_ctor_get(v_x_112_, 2);
v_offset_117_ = lean_ctor_get(v_x_112_, 3);
v_identity_118_ = lean_ctor_get(v_x_113_, 0);
v_size_119_ = lean_ctor_get(v_x_113_, 1);
v_alignment_120_ = lean_ctor_get(v_x_113_, 2);
v_offset_121_ = lean_ctor_get(v_x_113_, 3);
v___x_122_ = lean_nat_dec_eq(v_identity_114_, v_identity_118_);
if (v___x_122_ == 0)
{
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = lean_nat_dec_eq(v_size_115_, v_size_119_);
if (v___x_123_ == 0)
{
return v___x_123_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = lean_nat_dec_eq(v_alignment_116_, v_alignment_120_);
if (v___x_124_ == 0)
{
return v___x_124_;
}
else
{
uint8_t v___x_125_; 
v___x_125_ = lean_nat_dec_eq(v_offset_117_, v_offset_121_);
return v___x_125_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField_decEq___boxed(lean_object* v_x_126_, lean_object* v_x_127_){
_start:
{
uint8_t v_res_128_; lean_object* v_r_129_; 
v_res_128_ = lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField_decEq(v_x_126_, v_x_127_);
lean_dec_ref(v_x_127_);
lean_dec_ref(v_x_126_);
v_r_129_ = lean_box(v_res_128_);
return v_r_129_;
}
}
LEAN_EXPORT uint8_t lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField(lean_object* v_x_130_, lean_object* v_x_131_){
_start:
{
uint8_t v___x_132_; 
v___x_132_ = lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField_decEq(v_x_130_, v_x_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField___boxed(lean_object* v_x_133_, lean_object* v_x_134_){
_start:
{
uint8_t v_res_135_; lean_object* v_r_136_; 
v_res_135_ = lp_oak_x2dspec_Oak_RecordLayout_instDecidableEqPlacedField(v_x_133_, v_x_134_);
lean_dec_ref(v_x_134_);
lean_dec_ref(v_x_133_);
v_r_136_ = lean_box(v_res_135_);
return v_r_136_;
}
}
static lean_object* _init_lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__2(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(10u);
v___x_141_ = lean_nat_to_int(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg(lean_object* v_x_142_){
_start:
{
lean_object* v_identity_143_; lean_object* v_size_144_; lean_object* v_alignment_145_; lean_object* v_offset_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; uint8_t v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_identity_143_ = lean_ctor_get(v_x_142_, 0);
lean_inc(v_identity_143_);
v_size_144_ = lean_ctor_get(v_x_142_, 1);
lean_inc(v_size_144_);
v_alignment_145_ = lean_ctor_get(v_x_142_, 2);
lean_inc(v_alignment_145_);
v_offset_146_ = lean_ctor_get(v_x_142_, 3);
lean_inc(v_offset_146_);
lean_dec_ref(v_x_142_);
v___x_147_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__5));
v___x_148_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__6));
v___x_149_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__7, &lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__7_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__7);
v___x_150_ = l_Nat_reprFast(v_identity_143_);
v___x_151_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
v___x_152_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_152_, 0, v___x_149_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = 0;
v___x_154_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_154_, 0, v___x_152_);
lean_ctor_set_uint8(v___x_154_, sizeof(void*)*1, v___x_153_);
v___x_155_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_148_);
lean_ctor_set(v___x_155_, 1, v___x_154_);
v___x_156_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__9));
v___x_157_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_157_, 0, v___x_155_);
lean_ctor_set(v___x_157_, 1, v___x_156_);
v___x_158_ = lean_box(1);
v___x_159_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_159_, 0, v___x_157_);
lean_ctor_set(v___x_159_, 1, v___x_158_);
v___x_160_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__11));
v___x_161_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_161_, 0, v___x_159_);
lean_ctor_set(v___x_161_, 1, v___x_160_);
v___x_162_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
lean_ctor_set(v___x_162_, 1, v___x_147_);
v___x_163_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__12, &lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__12_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__12);
v___x_164_ = l_Nat_reprFast(v_size_144_);
v___x_165_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
v___x_166_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_163_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set_uint8(v___x_167_, sizeof(void*)*1, v___x_153_);
v___x_168_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_162_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___x_156_);
v___x_170_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_158_);
v___x_171_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__14));
v___x_172_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_170_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
v___x_173_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_147_);
v___x_174_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__15, &lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__15_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__15);
v___x_175_ = l_Nat_reprFast(v_alignment_145_);
v___x_176_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
v___x_177_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_177_, 0, v___x_174_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
v___x_178_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set_uint8(v___x_178_, sizeof(void*)*1, v___x_153_);
v___x_179_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_173_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_156_);
v___x_181_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___x_158_);
v___x_182_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__1));
v___x_183_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_183_, 0, v___x_181_);
lean_ctor_set(v___x_183_, 1, v___x_182_);
v___x_184_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
lean_ctor_set(v___x_184_, 1, v___x_147_);
v___x_185_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__2, &lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__2_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg___closed__2);
v___x_186_ = l_Nat_reprFast(v_offset_146_);
v___x_187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
v___x_188_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_185_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_189_, sizeof(void*)*1, v___x_153_);
v___x_190_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_184_);
lean_ctor_set(v___x_190_, 1, v___x_189_);
v___x_191_ = lean_obj_once(&lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__18, &lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__18_once, _init_lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__18);
v___x_192_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__19));
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v___x_190_);
v___x_194_ = ((lean_object*)(lp_oak_x2dspec_Oak_RecordLayout_instReprFieldSpec_repr___redArg___closed__20));
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_191_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
v___x_197_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_197_, 0, v___x_196_);
lean_ctor_set_uint8(v___x_197_, sizeof(void*)*1, v___x_153_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr(lean_object* v_x_198_, lean_object* v_prec_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___redArg(v_x_198_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr___boxed(lean_object* v_x_201_, lean_object* v_prec_202_){
_start:
{
lean_object* v_res_203_; 
v_res_203_ = lp_oak_x2dspec_Oak_RecordLayout_instReprPlacedField_repr(v_x_201_, v_prec_202_);
lean_dec(v_prec_202_);
return v_res_203_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_alignUp(lean_object* v_value_206_, lean_object* v_alignment_207_){
_start:
{
lean_object* v___x_208_; uint8_t v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_nat_dec_eq(v_alignment_207_, v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; uint8_t v___x_211_; 
v___x_210_ = lean_nat_mod(v_value_206_, v_alignment_207_);
v___x_211_ = lean_nat_dec_eq(v___x_210_, v___x_208_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_212_ = lean_nat_sub(v_alignment_207_, v___x_210_);
lean_dec(v___x_210_);
v___x_213_ = lean_nat_add(v_value_206_, v___x_212_);
lean_dec(v___x_212_);
return v___x_213_;
}
else
{
lean_dec(v___x_210_);
lean_inc(v_value_206_);
return v_value_206_;
}
}
else
{
lean_inc(v_value_206_);
return v_value_206_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_alignUp___boxed(lean_object* v_value_214_, lean_object* v_alignment_215_){
_start:
{
lean_object* v_res_216_; 
v_res_216_ = lp_oak_x2dspec_Oak_RecordLayout_alignUp(v_value_214_, v_alignment_215_);
lean_dec(v_alignment_215_);
lean_dec(v_value_214_);
return v_res_216_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_placeFrom(lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v___x_219_; 
v___x_219_ = lean_box(0);
return v___x_219_;
}
else
{
lean_object* v_head_220_; lean_object* v_tail_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_235_; 
v_head_220_ = lean_ctor_get(v_x_218_, 0);
v_tail_221_ = lean_ctor_get(v_x_218_, 1);
v_isSharedCheck_235_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_235_ == 0)
{
v___x_223_ = v_x_218_;
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_tail_221_);
lean_inc(v_head_220_);
lean_dec(v_x_218_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_235_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v_identity_225_; lean_object* v_size_226_; lean_object* v_alignment_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_233_; 
v_identity_225_ = lean_ctor_get(v_head_220_, 0);
lean_inc(v_identity_225_);
v_size_226_ = lean_ctor_get(v_head_220_, 1);
lean_inc_n(v_size_226_, 2);
v_alignment_227_ = lean_ctor_get(v_head_220_, 2);
lean_inc(v_alignment_227_);
lean_dec(v_head_220_);
v___x_228_ = lp_oak_x2dspec_Oak_RecordLayout_alignUp(v_x_217_, v_alignment_227_);
lean_inc(v___x_228_);
v___x_229_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_229_, 0, v_identity_225_);
lean_ctor_set(v___x_229_, 1, v_size_226_);
lean_ctor_set(v___x_229_, 2, v_alignment_227_);
lean_ctor_set(v___x_229_, 3, v___x_228_);
v___x_230_ = lean_nat_add(v___x_228_, v_size_226_);
lean_dec(v_size_226_);
lean_dec(v___x_228_);
v___x_231_ = lp_oak_x2dspec_Oak_RecordLayout_placeFrom(v___x_230_, v_tail_221_);
lean_dec(v___x_230_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_231_);
lean_ctor_set(v___x_223_, 0, v___x_229_);
v___x_233_ = v___x_223_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_229_);
lean_ctor_set(v_reuseFailAlloc_234_, 1, v___x_231_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_placeFrom___boxed(lean_object* v_x_236_, lean_object* v_x_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = lp_oak_x2dspec_Oak_RecordLayout_placeFrom(v_x_236_, v_x_237_);
lean_dec(v_x_236_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_cursorAfter(lean_object* v_x_239_, lean_object* v_x_240_){
_start:
{
if (lean_obj_tag(v_x_240_) == 0)
{
return v_x_239_;
}
else
{
lean_object* v_head_241_; lean_object* v_tail_242_; lean_object* v_size_243_; lean_object* v_alignment_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_head_241_ = lean_ctor_get(v_x_240_, 0);
v_tail_242_ = lean_ctor_get(v_x_240_, 1);
v_size_243_ = lean_ctor_get(v_head_241_, 1);
v_alignment_244_ = lean_ctor_get(v_head_241_, 2);
v___x_245_ = lp_oak_x2dspec_Oak_RecordLayout_alignUp(v_x_239_, v_alignment_244_);
lean_dec(v_x_239_);
v___x_246_ = lean_nat_add(v___x_245_, v_size_243_);
lean_dec(v___x_245_);
v_x_239_ = v___x_246_;
v_x_240_ = v_tail_242_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_cursorAfter___boxed(lean_object* v_x_248_, lean_object* v_x_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = lp_oak_x2dspec_Oak_RecordLayout_cursorAfter(v_x_248_, v_x_249_);
lean_dec(v_x_249_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_maxAlignment(lean_object* v_x_251_){
_start:
{
if (lean_obj_tag(v_x_251_) == 0)
{
lean_object* v___x_252_; 
v___x_252_ = lean_unsigned_to_nat(1u);
return v___x_252_;
}
else
{
lean_object* v_head_253_; lean_object* v_tail_254_; lean_object* v_alignment_255_; lean_object* v___x_256_; uint8_t v___x_257_; 
v_head_253_ = lean_ctor_get(v_x_251_, 0);
v_tail_254_ = lean_ctor_get(v_x_251_, 1);
v_alignment_255_ = lean_ctor_get(v_head_253_, 2);
v___x_256_ = lp_oak_x2dspec_Oak_RecordLayout_maxAlignment(v_tail_254_);
v___x_257_ = lean_nat_dec_le(v_alignment_255_, v___x_256_);
if (v___x_257_ == 0)
{
lean_dec(v___x_256_);
lean_inc(v_alignment_255_);
return v_alignment_255_;
}
else
{
return v___x_256_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_maxAlignment___boxed(lean_object* v_x_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = lp_oak_x2dspec_Oak_RecordLayout_maxAlignment(v_x_258_);
lean_dec(v_x_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_finalSize(lean_object* v_fields_260_){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lp_oak_x2dspec_Oak_RecordLayout_cursorAfter(v___x_261_, v_fields_260_);
v___x_263_ = lp_oak_x2dspec_Oak_RecordLayout_maxAlignment(v_fields_260_);
v___x_264_ = lp_oak_x2dspec_Oak_RecordLayout_alignUp(v___x_262_, v___x_263_);
lean_dec(v___x_263_);
lean_dec(v___x_262_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec_Oak_RecordLayout_finalSize___boxed(lean_object* v_fields_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = lp_oak_x2dspec_Oak_RecordLayout_finalSize(v_fields_265_);
lean_dec(v_fields_265_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_placeFrom_match__1_splitter___redArg(lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_h__1_269_, lean_object* v_h__2_270_){
_start:
{
if (lean_obj_tag(v_x_268_) == 0)
{
lean_object* v___x_271_; 
lean_dec(v_h__2_270_);
v___x_271_ = lean_apply_1(v_h__1_269_, v_x_267_);
return v___x_271_;
}
else
{
lean_object* v_head_272_; lean_object* v_tail_273_; lean_object* v___x_274_; 
lean_dec(v_h__1_269_);
v_head_272_ = lean_ctor_get(v_x_268_, 0);
lean_inc(v_head_272_);
v_tail_273_ = lean_ctor_get(v_x_268_, 1);
lean_inc(v_tail_273_);
lean_dec_ref_known(v_x_268_, 2);
v___x_274_ = lean_apply_3(v_h__2_270_, v_x_267_, v_head_272_, v_tail_273_);
return v___x_274_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_placeFrom_match__1_splitter(lean_object* v_motive_275_, lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v_h__1_278_, lean_object* v_h__2_279_){
_start:
{
if (lean_obj_tag(v_x_277_) == 0)
{
lean_object* v___x_280_; 
lean_dec(v_h__2_279_);
v___x_280_ = lean_apply_1(v_h__1_278_, v_x_276_);
return v___x_280_;
}
else
{
lean_object* v_head_281_; lean_object* v_tail_282_; lean_object* v___x_283_; 
lean_dec(v_h__1_278_);
v_head_281_ = lean_ctor_get(v_x_277_, 0);
lean_inc(v_head_281_);
v_tail_282_ = lean_ctor_get(v_x_277_, 1);
lean_inc(v_tail_282_);
lean_dec_ref_known(v_x_277_, 2);
v___x_283_ = lean_apply_3(v_h__2_279_, v_x_276_, v_head_281_, v_tail_282_);
return v___x_283_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_AllAligned_match__1_splitter___redArg(lean_object* v_x_284_, lean_object* v_h__1_285_, lean_object* v_h__2_286_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
lean_dec(v_h__2_286_);
v___x_287_ = lean_box(0);
v___x_288_ = lean_apply_1(v_h__1_285_, v___x_287_);
return v___x_288_;
}
else
{
lean_object* v_head_289_; lean_object* v_tail_290_; lean_object* v___x_291_; 
lean_dec(v_h__1_285_);
v_head_289_ = lean_ctor_get(v_x_284_, 0);
lean_inc(v_head_289_);
v_tail_290_ = lean_ctor_get(v_x_284_, 1);
lean_inc(v_tail_290_);
lean_dec_ref_known(v_x_284_, 2);
v___x_291_ = lean_apply_2(v_h__2_286_, v_head_289_, v_tail_290_);
return v___x_291_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_AllAligned_match__1_splitter(lean_object* v_motive_292_, lean_object* v_x_293_, lean_object* v_h__1_294_, lean_object* v_h__2_295_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec(v_h__2_295_);
v___x_296_ = lean_box(0);
v___x_297_ = lean_apply_1(v_h__1_294_, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v_head_298_; lean_object* v_tail_299_; lean_object* v___x_300_; 
lean_dec(v_h__1_294_);
v_head_298_ = lean_ctor_get(v_x_293_, 0);
lean_inc(v_head_298_);
v_tail_299_ = lean_ctor_get(v_x_293_, 1);
lean_inc(v_tail_299_);
lean_dec_ref_known(v_x_293_, 2);
v___x_300_ = lean_apply_2(v_h__2_295_, v_head_298_, v_tail_299_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_NonOverlapping_match__1_splitter___redArg(lean_object* v_x_301_, lean_object* v_h__1_302_, lean_object* v_h__2_303_, lean_object* v_h__3_304_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v___x_305_; lean_object* v___x_306_; 
lean_dec(v_h__3_304_);
lean_dec(v_h__2_303_);
v___x_305_ = lean_box(0);
v___x_306_ = lean_apply_1(v_h__1_302_, v___x_305_);
return v___x_306_;
}
else
{
lean_object* v_tail_307_; 
lean_dec(v_h__1_302_);
v_tail_307_ = lean_ctor_get(v_x_301_, 1);
if (lean_obj_tag(v_tail_307_) == 0)
{
lean_object* v_head_308_; lean_object* v___x_309_; 
lean_dec(v_h__3_304_);
v_head_308_ = lean_ctor_get(v_x_301_, 0);
lean_inc(v_head_308_);
lean_dec_ref_known(v_x_301_, 2);
v___x_309_ = lean_apply_1(v_h__2_303_, v_head_308_);
return v___x_309_;
}
else
{
lean_object* v_head_310_; lean_object* v_head_311_; lean_object* v_tail_312_; lean_object* v___x_313_; 
lean_inc_ref(v_tail_307_);
lean_dec(v_h__2_303_);
v_head_310_ = lean_ctor_get(v_x_301_, 0);
lean_inc(v_head_310_);
lean_dec_ref_known(v_x_301_, 2);
v_head_311_ = lean_ctor_get(v_tail_307_, 0);
lean_inc(v_head_311_);
v_tail_312_ = lean_ctor_get(v_tail_307_, 1);
lean_inc(v_tail_312_);
lean_dec_ref_known(v_tail_307_, 2);
v___x_313_ = lean_apply_3(v_h__3_304_, v_head_310_, v_head_311_, v_tail_312_);
return v___x_313_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_NonOverlapping_match__1_splitter(lean_object* v_motive_314_, lean_object* v_x_315_, lean_object* v_h__1_316_, lean_object* v_h__2_317_, lean_object* v_h__3_318_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_h__3_318_);
lean_dec(v_h__2_317_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_apply_1(v_h__1_316_, v___x_319_);
return v___x_320_;
}
else
{
lean_object* v_tail_321_; 
lean_dec(v_h__1_316_);
v_tail_321_ = lean_ctor_get(v_x_315_, 1);
if (lean_obj_tag(v_tail_321_) == 0)
{
lean_object* v_head_322_; lean_object* v___x_323_; 
lean_dec(v_h__3_318_);
v_head_322_ = lean_ctor_get(v_x_315_, 0);
lean_inc(v_head_322_);
lean_dec_ref_known(v_x_315_, 2);
v___x_323_ = lean_apply_1(v_h__2_317_, v_head_322_);
return v___x_323_;
}
else
{
lean_object* v_head_324_; lean_object* v_head_325_; lean_object* v_tail_326_; lean_object* v___x_327_; 
lean_inc_ref(v_tail_321_);
lean_dec(v_h__2_317_);
v_head_324_ = lean_ctor_get(v_x_315_, 0);
lean_inc(v_head_324_);
lean_dec_ref_known(v_x_315_, 2);
v_head_325_ = lean_ctor_get(v_tail_321_, 0);
lean_inc(v_head_325_);
v_tail_326_ = lean_ctor_get(v_tail_321_, 1);
lean_inc(v_tail_326_);
lean_dec_ref_known(v_tail_321_, 2);
v___x_327_ = lean_apply_3(v_h__3_318_, v_head_324_, v_head_325_, v_tail_326_);
return v___x_327_;
}
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_maxAlignment_match__1_splitter___redArg(lean_object* v_x_328_, lean_object* v_h__1_329_, lean_object* v_h__2_330_){
_start:
{
if (lean_obj_tag(v_x_328_) == 0)
{
lean_object* v___x_331_; lean_object* v___x_332_; 
lean_dec(v_h__2_330_);
v___x_331_ = lean_box(0);
v___x_332_ = lean_apply_1(v_h__1_329_, v___x_331_);
return v___x_332_;
}
else
{
lean_object* v_head_333_; lean_object* v_tail_334_; lean_object* v___x_335_; 
lean_dec(v_h__1_329_);
v_head_333_ = lean_ctor_get(v_x_328_, 0);
lean_inc(v_head_333_);
v_tail_334_ = lean_ctor_get(v_x_328_, 1);
lean_inc(v_tail_334_);
lean_dec_ref_known(v_x_328_, 2);
v___x_335_ = lean_apply_2(v_h__2_330_, v_head_333_, v_tail_334_);
return v___x_335_;
}
}
}
LEAN_EXPORT lean_object* lp_oak_x2dspec___private_Oak_RecordLayout_0__Oak_RecordLayout_maxAlignment_match__1_splitter(lean_object* v_motive_336_, lean_object* v_x_337_, lean_object* v_h__1_338_, lean_object* v_h__2_339_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v___x_340_; lean_object* v___x_341_; 
lean_dec(v_h__2_339_);
v___x_340_ = lean_box(0);
v___x_341_ = lean_apply_1(v_h__1_338_, v___x_340_);
return v___x_341_;
}
else
{
lean_object* v_head_342_; lean_object* v_tail_343_; lean_object* v___x_344_; 
lean_dec(v_h__1_338_);
v_head_342_ = lean_ctor_get(v_x_337_, 0);
lean_inc(v_head_342_);
v_tail_343_ = lean_ctor_get(v_x_337_, 1);
lean_inc(v_tail_343_);
lean_dec_ref_known(v_x_337_, 2);
v___x_344_ = lean_apply_2(v_h__2_339_, v_head_342_, v_tail_343_);
return v___x_344_;
}
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak_RecordLayout(uint8_t builtin) {
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
