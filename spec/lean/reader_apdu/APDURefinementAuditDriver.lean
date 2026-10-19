import Oak.Stdlib.APDUExtracted
import Oak.Stdlib.APDULengthModel
import Oak.Stdlib.APDUModelErrorContracts
import Oak.Stdlib.APDUParserControls
import Oak.Stdlib.APDUParserCorrectness
import Oak.Stdlib.APDUParserHelperProofs
import Oak.Stdlib.APDUParserRefinement
import Oak.Stdlib.APDUReaderBridge
import Oak.Stdlib.BoundedReaderExtracted
import Oak.Stdlib.BoundedReaderModel
import Oak.Stdlib.BoundedReaderRefinement
/- Source-only proposed audit driver. It has not been elaborated or executed.
   Candidate modules are imported from the fresh gate output only. -/
import Lean.Elab.Command
import Lean.Util.CollectAxioms
import Lean.Data.Json

set_option autoImplicit false
open Lean Elab Command

namespace APDUParserRefinementAudit

def targetModules : Array Name := #[`Oak.Stdlib.APDUExtracted, `Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModelErrorContracts, `Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.BoundedReaderExtracted, `Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.BoundedReaderRefinement]
def allowedAxioms : Array Name := #[`propext, `Quot.sound, `Classical.choice]
def forbiddenOracleNames : Array Name := #[`sorryAx, `Lean.trustCompiler,
  `Lean.ofReduceBool, `Lean.ofReduceNat, `Lean.reduceBool, `Lean.reduceNat]

def expected : Array (Name × Name × Bool) := #[
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.data_window_take_iff, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.short_response_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.extended_response_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.short_zero_sentinel, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.extended_zero_sentinel, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.shape_unique, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.shape_frame_bound, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.shape_payload_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.shape_payload_sum_no_u32_wrap, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.layout_consumed, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.layout_response_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.short_data_sound, true),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.extended_data_sound, true),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.decode_sound, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.decode_of_shape, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.decode_success_iff, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.decode_payload_safe, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.positions_in_bounds, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.positions_count, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_too_long, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_header, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_six_byte_marker, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_extended_zero_lc, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_short_data, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_short_trailing, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_extended_data, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_one_byte_extended_le, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.reject_extended_trailing, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.frame_unchanged, false),
  (`Oak.Stdlib.APDULengthModel, `Oak.Stdlib.APDUModel.rejection_returns_no_command, false),
  (`Oak.Stdlib.APDUModelErrorContracts, `Oak.Stdlib.APDUModelErrorContracts.decode_error_iff, false),
  (`Oak.Stdlib.APDUModelErrorContracts, `Oak.Stdlib.APDUModelErrorContracts.too_long_iff, false),
  (`Oak.Stdlib.APDUModelErrorContracts, `Oak.Stdlib.APDUModelErrorContracts.truncated_header_iff, false),
  (`Oak.Stdlib.APDUModelErrorContracts, `Oak.Stdlib.APDUModelErrorContracts.truncated_length_iff, false),
  (`Oak.Stdlib.APDUModelErrorContracts, `Oak.Stdlib.APDUModelErrorContracts.zero_data_length_iff, false),
  (`Oak.Stdlib.APDUModelErrorContracts, `Oak.Stdlib.APDUModelErrorContracts.truncated_data_iff, false),
  (`Oak.Stdlib.APDUModelErrorContracts, `Oak.Stdlib.APDUModelErrorContracts.trailing_bytes_iff, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case1, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case2_short_zero, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case3_short, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case4_short_zero, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case2_extended_zero, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case3_extended, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case4_extended_zero, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.too_long, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.truncated_header, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.truncated_extended_length, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.zero_data_length, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.truncated_short_data, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.trailing_short, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.one_trailing_extended, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.truncated_extended_data, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.trailing_extended, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case2_short_max, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case2_extended_max, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case2_extended_asymmetric, false),
  (`Oak.Stdlib.APDUParserControls, `Oak.Stdlib.APDUParserControls.case4_extended_asymmetric, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.sourceHeader_observation, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.sourceHeader_checked, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_eq, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_total, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_result_iff, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_fuel_independent, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.fullSpec_error_iff, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_error_iff, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_form_iff, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_success_bounds, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_header_observation, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_header_preserved, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_header_indices_valid, false),
  (`Oak.Stdlib.APDUParserCorrectness, `Oak.Stdlib.APDUParserCorrectness.decode_success_response_bounds, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceBytes_length, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.source_byteAt, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceInput_n, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceInput_first, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceInput_shortLe, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.wordAt_toNat, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceInput_word, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceInput_extendedLe, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.nat32_toNat, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.u8_zero_iff, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.u16_zero_iff, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.u32_eq_iff, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.u32_beq_nat, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.u16_beq_zero, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.short_response_raw, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.extended_response_raw, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.short_response_toNat, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.extended_response_toNat, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.short_response_eq, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.extended_response_eq, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.short_response_sentinel, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.extended_response_sentinel, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.short_response_bounds, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.extended_response_bounds, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceWindow_lift, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceWindow_valid, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceWindow_remaining_nat, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceWindow_advance, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.take_source_short, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.take_source_good, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.read_u8_source_good, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.read_be16_source_short, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.read_be16_source_good, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.sourceInput_first_value, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.read_first_byte, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.short_data_eq, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.extended_data_eq, false),
  (`Oak.Stdlib.APDUParserHelperProofs, `Oak.Stdlib.APDUParserHelperProofs.extended_eq, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.liftByte_injective, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.liftWord_injective, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.liftCase_injective, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.liftError_injective, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.liftResponse_injective, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.command_observation, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.command_header_preserved, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.fullSpec_success_header, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.liftCommand_injective, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.liftResult_injective, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.fullSpec_success_lengths, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.fullSpec_shape_iff, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.fullSpec_success_bounds, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.decode_too_long_raw, false),
  (`Oak.Stdlib.APDUParserRefinement, `Oak.Stdlib.APDUParserRefinement.decode_short_header_raw, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.range_fits_bridge, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.remaining_bridge, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.take_bridge, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.endian_be16_bridge, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_be16_bridge, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.remaining_model, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.take_model, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_be16_model, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_from_take, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_error_from_take, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_index_valid, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_zero_fuel, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_invalid_precedes_short, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_empty_window, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.toReaderError_injective, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.toReaderWindow_injective, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.toReaderRange_injective, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.toReaderRangeResult_injective, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.take_invalid_raw, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.take_short_raw, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.take_good_raw, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_model, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.toReaderWord_injective, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.toReaderWordResult_injective, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_be16_short_raw, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_be16_good_raw, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.byte_model_index_valid, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.byteSpec_eq_checked, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_checked_model, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_checked_success, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.liftByte_injective, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.liftByteResult_injective, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_result_iff, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_total, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_invalid_raw, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_short_raw, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_good_raw, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_invalid_iff, false),
  (`Oak.Stdlib.APDUReaderBridge, `Oak.Stdlib.APDUReaderBridge.read_u8_insufficient_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.range_fits_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.range_fits_empty_at_end, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.range_fits_offset_past_end, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.range_fits_sum_fits_u32, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.window_ok_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.window_invalid_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.window_ok_bounds, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.remaining_valid, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.remaining_invalid, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.remaining_ok_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_ok_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_invalid_precedence, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_insufficient_iff, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_ok_bounds, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_ok_fits_u32, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_failure_no_rest, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_frame_unchanged, false),
  (`Oak.Stdlib.BoundedReaderModel, `Oak.Stdlib.ReaderModel.take_failure_keeps_committed_cursor, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.u8_toNat_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.u16_toNat_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.u32_toNat_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.liftError_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.liftWindow_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.liftRange_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.liftWord_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.liftWindowResult_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.liftRemainingResult_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.liftRangeResult_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.liftWordResult_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.optionMap_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.optionMap_reflect, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.optionMap_some_witness, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.optionMap_total, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.size_toNat, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.u32_sub_toNat, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.u32_add_toNat, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.range_fits_eq, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.window_eq, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.remaining_valid_raw, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.remaining_invalid_raw, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.remaining_eq, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_invalid_raw, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_short_raw, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_good_raw, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_eq, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.window_success_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.window_invalid_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.remaining_success_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.remaining_invalid_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_success_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_invalid_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_insufficient_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.core_total, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.error_no_rest, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_error_keeps_committed_cursor, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.window_error_distinction, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.remaining_error_distinction, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.window_success_bounds, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_success_bounds, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_success_representable, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.projection_constructors, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.projection_error_distinct, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.projection_options, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.projection_fields, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.projection_ok_err_disjoint, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.result_option_maps_injective, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.u32_comparison_nat, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.range_fits_total, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.take_failure_no_rest, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.be16ValueExpr_toNat, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.be16ValueExpr_le_65535, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.be16ValueExpr_lt_65536, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.good_window_bounds, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.good_index0, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.good_index1, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.good_no_wrap, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.u32_two_indices, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.getD_checked, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.checked_bytes_proof_irrelevant, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.endian_range_after_good, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.generated_reads_checked, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.endian_good_raw, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.endian_total, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_invalid_raw, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_short_raw, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_good_raw, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_eq, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_invalid_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_insufficient_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_success_iff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_total, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_success_unique, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_success_implies_good, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_cases_disjoint_complete, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.endian_error_unreachable_after_take, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_same_take_rest, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_success_value_and_access, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_failure_no_rest, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.read_fuel_irrelevant, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.window_empty, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.window_empty_at_end, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.window_offset_past_end, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.window_wrapping_endpoint_refused, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.take_invalid_precedes_short, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.take_end_past_source, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.take_short, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.take_zero_at_end, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_0000, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_0001, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_00ff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_0100, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_ffff, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_invalid_precedes_short, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_source_bound_refused, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_short_window, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_empty_at_end, false),
  (`Oak.Stdlib.BoundedReaderRefinement, `Oak.Stdlib.BoundedReaderRefinement.Controls.read_narrow_subwindow, false)
]

def jnames (ns : Array Name) : Json := Json.arr (ns.map fun n => Json.str n.toString)

def owner? (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.allImportedModuleNames[idx.toNat]?

def directRefs (ci : ConstantInfo) : Array Name := Id.run do
  let mut refs := ci.type.getUsedConstants
  if let some value := ci.value? (allowOpaque := true) then
    refs := refs ++ value.getUsedConstants
  if let .inductInfo val := ci then
    refs := refs ++ val.ctors.toArray
  return refs.toList.mergeSort Name.lt |>.toArray

def kind (ci : ConstantInfo) : String :=
  match ci with
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "definition"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"

def emit (value : Json) : CommandElabM Unit :=
  logInfo m!"OAK_READER_REFINEMENT_AUDIT {value.compress}"

/-- Independent bounded dependency traversal, in addition to collectAxioms. -/
def reachableAxioms (env : Environment) (root : Name) : CommandElabM (Array Name) := do
  let mut todo := #[root]
  let mut seen : NameSet := {}
  let mut axioms : NameSet := {}
  let mut count := 0
  let mut edges := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless seen.contains n do
      count := count + 1
      if count > 10000 then throwError "dependency traversal node cap"
      seen := seen.insert n
      if forbiddenOracleNames.contains n then throwError "forbidden proof oracle: {n}"
      let some ci := env.checked.get.find? n
        | throwError "unresolved checked dependency: {n}"
      if ci.isUnsafe then throwError "unsafe proof dependency: {n}"
      if let .axiomInfo _ := ci then
        unless allowedAxioms.contains n do throwError "unapproved axiom: {n}"
        axioms := axioms.insert n
      let deps := directRefs ci
      edges := edges + deps.size
      if edges > 100000 || todo.size + deps.size > 100000 then
        throwError "per-root dependency edge/pending cap"
      todo := todo ++ deps
  return axioms.toArray.qsort Name.lt

run_cmd do
  let env := (← getEnv).setExporting false
  let imports := env.allImportedModuleNames
  emit <| Json.mkObj [("record", Json.str "imports"), ("modules", jnames imports)]
  let constants := env.checked.get.constants.toList.toArray
  let candidates := constants.filter fun pair =>
    (owner? env pair.1).any (fun m => targetModules.contains m)
  if candidates.isEmpty || candidates.size > 4000 then
    throwError "empty or oversized candidate-owned declaration inventory"
  unless expected.size == 280 do throwError "wrong expected theorem count"
  let mut resolved : Array Name := #[]
  for (moduleName, userName, isPrivate) in expected do
    let theoremMatches := candidates.filter fun pair =>
      privateToUserName pair.1 == userName && owner? env pair.1 == some moduleName
    unless theoremMatches.size == 1 do throwError "missing or duplicate expected theorem: {userName}"
    let (actualName, ci) := theoremMatches[0]!
    unless ci.isTheorem do throwError "expected theorem has another declaration kind: {actualName}"
    unless isPrivateName actualName == isPrivate do throwError "private/public mismatch: {actualName}"
    if resolved.contains actualName then throwError "duplicate theorem resolution: {actualName}"
    resolved := resolved.push actualName
    let builtin ← collectAxioms actualName
    let walked ← reachableAxioms env actualName
    unless builtin.qsort Name.lt == walked do
      throwError "builtin/traversed axiom disagreement: {actualName}"
    emit <| Json.mkObj [("record", Json.str "expected_theorem"),
      ("owner", Json.str moduleName.toString), ("user_name", Json.str userName.toString),
      ("actual_name", Json.str actualName.toString), ("private", Json.bool isPrivate),
      ("axioms", jnames walked), ("direct_dependencies", jnames (directRefs ci))]
  for (n, ci) in candidates do
    if ci.isUnsafe || ci.isPartial then throwError "unsafe/partial candidate declaration: {n}"
    if let .axiomInfo _ := ci then throwError "candidate-owned axiom: {n}"
    let axs ← collectAxioms n
    for ax in axs do
      unless allowedAxioms.contains ax do throwError "unapproved candidate axiom: {n}: {ax}"
    emit <| Json.mkObj [("record", Json.str "candidate_declaration"),
      ("actual_name", Json.str n.toString), ("user_name", Json.str (privateToUserName n).toString),
      ("owner", Json.str ((owner? env n).getD .anonymous).toString),
      ("kind", Json.str (kind ci)), ("axioms", jnames axs),
      ("direct_dependencies", jnames (directRefs ci))]
  let mut todo := candidates.map (·.1)
  let mut seen : NameSet := {}
  let mut nodes := 0
  let mut edges := 0
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    unless seen.contains n do
      nodes := nodes + 1
      if nodes > 10000 then throwError "combined graph node cap"
      seen := seen.insert n
      if forbiddenOracleNames.contains n then throwError "forbidden dependency: {n}"
      let some ci := env.checked.get.find? n | throwError "missing graph dependency: {n}"
      if ci.isUnsafe then throwError "unsafe dependency: {n}"
      if let .axiomInfo _ := ci then
        unless allowedAxioms.contains n do throwError "unapproved graph axiom: {n}"
      let deps := directRefs ci
      edges := edges + deps.size
      if edges > 100000 || todo.size + deps.size > 100000 then
        throwError "combined graph edge/pending cap"
      emit <| Json.mkObj [("record", Json.str "dependency"),
        ("actual_name", Json.str n.toString), ("kind", Json.str (kind ci)),
        ("direct_dependencies", jnames deps)]
      todo := todo ++ deps
  emit <| Json.mkObj [("record", Json.str "complete"),
    ("expected_theorems", toJson resolved.size), ("candidate_declarations", toJson candidates.size),
    ("dependency_nodes", toJson nodes), ("dependency_edges", toJson edges),
    ("anonymous_examples_persisted", Json.bool false),
    ("anonymous_examples_accounted_by_exact_source_compile", toJson (15 : Nat))]

end APDUParserRefinementAudit
