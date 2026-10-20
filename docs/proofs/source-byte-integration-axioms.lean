/- Reproduce from spec/lean: lake env lean ../../docs/proofs/source-byte-integration-axioms.lean
   Every listed closure must contain only propext, Classical.choice, and Quot.sound. -/
import Oak.BitwiseFunction
import Oak.AArch64BitwiseFunction
import Oak.RiscVBitwiseFunction
import Oak.BitwiseModule
import Oak.MinimalELF
import Oak.RiscVBitwiseELF
import Oak.AArch64MinimalStartup
import Oak.RiscVFramedBitwise
import Oak.BitwiseSource
import Oak.BitwiseSourceParity
import Oak.BitwiseSourceLowering
#print axioms Oak.BitwiseFunction.assembled_function
#print axioms Oak.BitwiseFunction.exact_encoding
#print axioms Oak.BitwiseFunction.body_success
#print axioms Oak.BitwiseFunction.function_success
#print axioms Oak.BitwiseFunction.assemblyPlan_encoding
#print axioms Oak.BitwiseFunction.emitted_function_success
#print axioms Oak.BitwiseFunction.accepts_iff
#print axioms Oak.BitwiseFunction.accepted_execution
#print axioms Oak.AArch64BitwiseFunction.function_success
#print axioms Oak.AArch64BitwiseFunction.result_u32
#print axioms Oak.AArch64BitwiseFunction.preserves_other_registers
#print axioms Oak.AArch64BitwiseFunction.return_boundary
#print axioms Oak.AArch64BitwiseFunction.accepted_execution
#print axioms Oak.AArch64BitwiseFunction.rejects_changed_bytes
#print axioms Oak.RiscVBitwiseFunction.exact_encoding
#print axioms Oak.RiscVBitwiseFunction.decoded_execution
#print axioms Oak.RiscVBitwiseFunction.eval64_widen
#print axioms Oak.RiscVBitwiseFunction.result_register
#print axioms Oak.RiscVBitwiseFunction.return_pc
#print axioms Oak.RiscVBitwiseFunction.preserves_register
#print axioms Oak.RiscVBitwiseFunction.zero_register
#print axioms Oak.RiscVBitwiseFunction.function_success
#print axioms Oak.RiscVBitwiseFunction.accepts_iff
#print axioms Oak.RiscVBitwiseFunction.accepted_execution
#print axioms Oak.BitwiseModule.admitted_module_success
#print axioms Oak.BitwiseModule.canonical_loaded
#print axioms Oak.BitwiseModule.canonical_admitted
#print axioms Oak.BitwiseModule.canonical_success
#print axioms Oak.BitwiseModule.padded_type_length_admitted
#print axioms Oak.BitwiseModule.single_bit_mutations_refused
#print axioms Oak.MinimalELF.admitted_iff
#print axioms Oak.MinimalELF.admitted_body
#print axioms Oak.MinimalELF.admitted_load
#print axioms Oak.MinimalELF.admitted_bounds
#print axioms Oak.MinimalELF.admitted_execution
#print axioms Oak.RiscVBitwiseELF.body_length
#print axioms Oak.RiscVBitwiseELF.admitted_function
#print axioms Oak.AArch64MinimalStartup.startup_request
#print axioms Oak.AArch64MinimalStartup.admitted_startup_request
#print axioms Oak.RiscVFramedBitwise.exact_decode
#print axioms Oak.RiscVFramedBitwise.run_memory
#print axioms Oak.RiscVFramedBitwise.run_pc
#print axioms Oak.RiscVFramedBitwise.run_registers
#print axioms Oak.RiscVFramedBitwise.run_success
#print axioms Oak.RiscVFramedBitwise.function_success
#print axioms Oak.RiscVFramedBitwise.preserved_register
#print axioms Oak.RiscVFramedBitwise.stack_and_saves_restored
#print axioms Oak.RiscVFramedBitwise.memory_footprint
#print axioms Oak.RiscVFramedBitwise.writes_within_frame
#print axioms Oak.RiscVFramedBitwise.accessed_addresses_fit
#print axioms Oak.RiscVFramedBitwise.result_register
#print axioms Oak.RiscVFramedBitwise.all_input_result
#print axioms Oak.RiscVFramedBitwise.accepts_iff
#print axioms Oak.RiscVFramedBitwise.accepted_success
#print axioms Oak.BitwiseSource.parse_sound
#print axioms Oak.BitwiseSource.parse_exact
#print axioms Oak.BitwiseSource.grammar_evaluation
#print axioms Oak.BitwiseSource.refuses_source_replay
#print axioms Oak.BitwiseSource.accepted_source_to_module
#print axioms Oak.BitwiseSource.fixture_op
#print axioms Oak.BitwiseSource.fixture_name
#print axioms Oak.BitwiseSource.fixture_parsed
#print axioms Oak.BitwiseSource.fixture_admitted
#print axioms Oak.BitwiseSource.source_mutations_refused
#print axioms Oak.BitwiseSourceParity.accepted_all_input_success
#print axioms Oak.BitwiseSourceParity.accepted_native_bytes
#print axioms Oak.BitwiseSourceParity.fixture_admitted
#print axioms Oak.BitwiseSourceLowering.lowering_success
#print axioms Oak.BitwiseSourceLowering.grammar_to_existing
#print axioms Oak.BitwiseSourceLowering.means_iff_existing
#print axioms Oak.BitwiseSourceLowering.accepted_module_existing
