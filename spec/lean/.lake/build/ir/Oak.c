// Lean compiler output
// Module: Oak
// Imports: public import Init public meta import Init public import Oak.TypeLattice public import Oak.Effects public import Oak.Borrowing public import Oak.BorrowRegions public import Oak.Reborrow public import Oak.Handles public import Oak.Slab public import Oak.Exhaustiveness public import Oak.SourcePosition public import Oak.Delimited public import Oak.RegionLifetime public import Oak.PhantomRepresentation public import Oak.Layout public import Oak.RecordLayout public import Oak.RecordShape public import Oak.RecordShapeRefinement public import Oak.GenericConstraintRefinement public import Oak.RepresentationPolymorphism public import Oak.TypeVarIdentity public import Oak.GeneralizationSafety public import Oak.Diagnostics
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_TypeLattice(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_Effects(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_Borrowing(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_BorrowRegions(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_Reborrow(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_Handles(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_Slab(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_Exhaustiveness(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_SourcePosition(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_Delimited(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_RegionLifetime(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_PhantomRepresentation(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_Layout(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_RecordLayout(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_RecordShape(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_RecordShapeRefinement(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_GenericConstraintRefinement(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_RepresentationPolymorphism(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_TypeVarIdentity(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_GeneralizationSafety(uint8_t builtin);
lean_object* initialize_oak_x2dspec_Oak_Diagnostics(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_oak_x2dspec_Oak(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_TypeLattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_Effects(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_Borrowing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_BorrowRegions(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_Reborrow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_Handles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_Slab(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_Exhaustiveness(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_SourcePosition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_Delimited(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_RegionLifetime(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_PhantomRepresentation(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_Layout(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_RecordLayout(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_RecordShape(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_RecordShapeRefinement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_GenericConstraintRefinement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_RepresentationPolymorphism(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_TypeVarIdentity(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_GeneralizationSafety(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_oak_x2dspec_Oak_Diagnostics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
