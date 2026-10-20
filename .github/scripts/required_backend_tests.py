#!/usr/bin/env python3
"""Run equipped-lane backend checks, rejecting missing tests and nested skips.

Ordinary development tests can still skip unavailable tools. These focused CI
suites require every named root and audited child to pass, and reject any skip
or failure in the selected tests. Keep the names here synchronized with the
Go tests; --check compares the exact selectors with Go's live test inventory.
"""
import argparse
from dataclasses import dataclass
import json
import subprocess
import sys


@dataclass(frozen=True)
class Suite:
    package: str
    timeout: str
    tests: tuple[str, ...]
    exact_children: bool = False
    race: bool = False

    @property
    def roots(self):
        return sorted({name.split("/", 1)[0] for name in self.tests})

    @property
    def pattern(self):
        return "^(" + "|".join(self.roots) + ")$"

    @property
    def import_path(self):
        return "github.com/SCKelemen/oak" + self.package[1:]


SUITES = {
    'checked-image-sources': Suite('./spec/lean', '5m', (
        'TestEmbeddedClosureCustody',
        'TestImageEmbeddedClosureCustody',
    ), exact_children=True),
    'checked-image-runtime': Suite('./bitwisecheck', '45m', (
        'TestArchiveDigestMismatch',
        'TestArchiveFIFORefusesWithoutBlocking',
        'TestExtractionBoundaries',
        'TestExtractionBoundaries/absolute',
        'TestExtractionBoundaries/absolute_symlink',
        'TestExtractionBoundaries/device',
        'TestExtractionBoundaries/duplicate',
        'TestExtractionBoundaries/hardlink',
        'TestExtractionBoundaries/outside_symlink',
        'TestExtractionBoundaries/symlink_ancestor',
        'TestExtractionBoundaries/traversal',
        'TestExtractionBoundaries/wrong_prefix',
        'TestImageMaximumProtocolSize',
        'TestImagePinnedRuntime',
        'TestImagePinnedRuntime/ActualBodyMutation',
        'TestImagePinnedRuntime/ActualSuccessfulRefusalProof',
        'TestImagePinnedRuntime/CanceledGlobalQueue',
        'TestImagePinnedRuntime/CanceledInstallationQueue',
        'TestImagePinnedRuntime/CloseActiveRequest',
        'TestImagePinnedRuntime/CanceledSetup',
        'TestImagePinnedRuntime/CanceledActiveRequest',
        'TestImagePinnedRuntime/InvalidCurrentDependencyBody',
        'TestImagePinnedRuntime/CrossProfileInstallationSeal',
        'TestImagePinnedRuntime/CanceledBeforeRequest',
        'TestImagePinnedRuntime/CopiedInstallationClose',
        'TestImagePinnedRuntime/DropContract/arm',
        'TestImagePinnedRuntime/DropContract/rv',
        'TestImagePinnedRuntime/MaximumNameAndSource',
        'TestImagePinnedRuntime/ValidRecordThenFailure',
        'TestImagePinnedRuntime/WrongExactRootType',
        'TestImageProtocolFieldLimits',
        'TestImageProtocolFieldLimits/arm',
        'TestImageProtocolFieldLimits/rv',
        'TestImageProtocolFieldLimits/source',
        'TestImageProtocolFieldLimits/wasm',
        'TestImageSnapshotAndRenderer',
        'TestImageStrictProtocol',
        'TestImageStrictProtocol/axiom_null',
        'TestImageStrictProtocol/duplicate_axiom',
        'TestImageStrictProtocol/duplicate_field',
        'TestImageStrictProtocol/duplicate_nested',
        'TestImageStrictProtocol/exponent_byte',
        'TestImageStrictProtocol/extra_whitespace_record',
        'TestImageStrictProtocol/float_byte',
        'TestImageStrictProtocol/forbidden_axiom',
        'TestImageStrictProtocol/image_byte_null',
        'TestImageStrictProtocol/leading_log',
        'TestImageStrictProtocol/missing_field',
        'TestImageStrictProtocol/negative_byte',
        'TestImageStrictProtocol/null_byte',
        'TestImageStrictProtocol/object_proof_field',
        'TestImageStrictProtocol/oversized_byte',
        'TestImageStrictProtocol/spaced_record',
        'TestImageStrictProtocol/string_byte',
        'TestImageStrictProtocol/trailing_log',
        'TestImageStrictProtocol/truncated',
        'TestImageStrictProtocol/two_records',
        'TestImageStrictProtocol/unknown_field',
        'TestImageStrictProtocol/unsorted_axioms',
        'TestImageStrictProtocol/wrong_declaration',
        'TestImageStrictProtocol/wrong_echo',
        'TestImageStrictProtocol/wrong_profile',
        'TestImageStrictProtocol/wrong_root',
        'TestImageStrictProtocol/wrong_schema',
        'TestImageStrictProtocol/wrong_version',
        'TestImageZeroAuthority',
        'TestImageClosedInstallationProfile',
        'TestInstallRefusesUntrustedArchive',
        'TestProcessRefusal',
    ), exact_children=True, race=True),
    'checked-image-bundle': Suite('./compiler', '60m', (
        'TestCheckedImageProposalProduction',
        'TestCheckedImageProposalProduction/arm64_mix_and',
        'TestCheckedImageProposalProduction/arm64_mix_or',
        'TestCheckedImageProposalProduction/arm64_mix_xor',
        'TestCheckedImageProposalProduction/arm64_Mix9_and',
        'TestCheckedImageProposalProduction/arm64_Mix9_or',
        'TestCheckedImageProposalProduction/arm64_Mix9_xor',
        'TestCheckedImageProposalProduction/arm64_one_and',
        'TestCheckedImageProposalProduction/arm64_max256_and',
        'TestCheckedImageProposalProduction/riscv64_mix_and',
        'TestCheckedImageProposalProduction/riscv64_mix_or',
        'TestCheckedImageProposalProduction/riscv64_mix_xor',
        'TestCheckedImageProposalProduction/riscv64_Mix9_and',
        'TestCheckedImageProposalProduction/riscv64_Mix9_or',
        'TestCheckedImageProposalProduction/riscv64_Mix9_xor',
        'TestCheckedImageProposalProduction/riscv64_one_and',
        'TestCheckedImageProposalProduction/riscv64_max256_and',
        'TestCheckedImageProposalRefusesMalformedObjects',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/trailing',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/oversized',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/symbol_name',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/duplicate_function',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/magic',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/class',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/endianness',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/ident_version',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/osabi',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/type',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/machine',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/version',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/entry',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/program_offset',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/section_offset_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/section_offset_header',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/flags',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/header_size',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/program_entry_size',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/program_count',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/section_entry_size',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/section_count',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/section_names',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/text_type',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/text_compressed',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/text_writable',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/text_address',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/text_offset_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/text_offset_header',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/text_size_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/text_alignment',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/text_entry_size',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/data_nonempty',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/body_relocation',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/relocation_owner',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/symbol_compressed',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/symbol_table_size',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/symbol_string_link',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/string_compressed',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/string_offset_overlap',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/string_size_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/name_table_compressed',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_name_bounds',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_missing',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_local',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_hidden',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_undefined',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_data_owner',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_owner_bounds',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_extent_shift',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_extent_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_size_zero',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/function_size_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/every_truncation',
        'TestCheckedImageProposalRefusesMalformedObjects/arm64/wrong_target',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/trailing',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/oversized',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/symbol_name',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/duplicate_function',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/magic',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/class',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/endianness',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/ident_version',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/osabi',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/type',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/machine',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/version',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/entry',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/program_offset',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/section_offset_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/section_offset_header',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/flags',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/header_size',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/program_entry_size',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/program_count',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/section_entry_size',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/section_count',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/section_names',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/text_type',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/text_compressed',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/text_writable',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/text_address',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/text_offset_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/text_offset_header',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/text_size_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/text_alignment',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/text_entry_size',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/data_nonempty',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/body_relocation',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/relocation_owner',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/symbol_compressed',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/symbol_table_size',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/symbol_string_link',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/string_compressed',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/string_offset_overlap',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/string_size_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/name_table_compressed',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_name_bounds',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_missing',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_local',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_hidden',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_undefined',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_data_owner',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_owner_bounds',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_extent_shift',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_extent_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_size_zero',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/function_size_overflow',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/every_truncation',
        'TestCheckedImageProposalRefusesMalformedObjects/riscv64/wrong_target',
        'TestCheckedImageProposalOwnsCopyWithoutClaimingBodyAuthority',
        'TestCheckedImageProposedSymbolBoundaries',
        'TestEmitKernelCheckedBitwiseImageBundleRefusesInvalidInstallation',
        'TestEmitKernelCheckedBitwiseImageBundleRefusesInvalidInstallation/nil',
        'TestEmitKernelCheckedBitwiseImageBundleRefusesInvalidInstallation/zero',
        'TestEmitKernelCheckedBitwiseImageBundleRefusesCanceledContext',
        'TestKernelCheckedBitwiseImageBundleDoesNotPromoteLegacyAuthority',
        'TestEmitKernelCheckedBitwiseImageBundleReal',
        'TestEmitKernelCheckedBitwiseImageBundleReal/Canonical',
        'TestEmitKernelCheckedBitwiseImageBundleReal/Canonical/bitwise/and',
        'TestEmitKernelCheckedBitwiseImageBundleReal/Canonical/bitwise/or',
        'TestEmitKernelCheckedBitwiseImageBundleReal/Canonical/bitwise/xor',
        'TestEmitKernelCheckedBitwiseImageBundleReal/Canonical/Mix9/and',
        'TestEmitKernelCheckedBitwiseImageBundleReal/Canonical/Mix9/or',
        'TestEmitKernelCheckedBitwiseImageBundleReal/Canonical/Mix9/xor',
        'TestEmitKernelCheckedBitwiseImageBundleReal/LegacyAuthorityUnchanged',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceBounds',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceBounds/OneByteName',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceBounds/MaximumName',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceBounds/MaximumSource',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/comment',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/main',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/nul',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/name257',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/extra_declaration',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/crlf',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/bom',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/wrong_type',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/wrong_reference',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/swapped_references',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/spacing',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/missing_lf',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/unsupported_operation',
        'TestEmitKernelCheckedBitwiseImageBundleReal/SourceRefusals/oversized',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals/source_operation',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals/source_name',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals/wasm_trailing',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals/wasm_truncated',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals/arm_body',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals/arm_trailing',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals/rv_abi',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals/rv_body',
        'TestEmitKernelCheckedBitwiseImageBundleReal/ArtifactRefusals/swapped_targets',
        'TestEmitKernelCheckedBitwiseImageBundleReal/CrossProfileInstallationRefusal',
        'TestEmitKernelCheckedBitwiseImageBundleReal/RelocatableObjectsAreNotImages',
        'TestEmitKernelCheckedBitwiseImageBundleReal/CopyCustody',
        'TestEmitKernelCheckedBitwiseImageBundleReal/RenamedParametersFreshAdmission',
        'TestEmitKernelCheckedBitwiseImageBundleReal/Canceled',
        'TestEmitKernelCheckedBitwiseImageBundleReal/StageCancellation',
        'TestEmitKernelCheckedBitwiseImageBundleReal/StageCancellation/wasm',
        'TestEmitKernelCheckedBitwiseImageBundleReal/StageCancellation/arm64_object',
        'TestEmitKernelCheckedBitwiseImageBundleReal/StageCancellation/arm64_proposal',
        'TestEmitKernelCheckedBitwiseImageBundleReal/StageCancellation/arm64_image',
        'TestEmitKernelCheckedBitwiseImageBundleReal/StageCancellation/rv64_object',
        'TestEmitKernelCheckedBitwiseImageBundleReal/StageCancellation/rv64_proposal',
        'TestEmitKernelCheckedBitwiseImageBundleReal/StageCancellation/rv64_image',
        'TestEmitKernelCheckedBitwiseImageBundleReal/Closed',
    ), exact_children=True),
    "checked-bitwise-sources": Suite("./spec/lean", "5m", (
        "TestEmbeddedClosureCustody",
    )),
    "checked-bitwise-runtime": Suite("./bitwisecheck", "40m", (
        "TestArchiveFIFORefusesWithoutBlocking",
        "TestArchiveDigestMismatch",
        "TestExtractionBoundaries",
        "TestExtractionBoundaries/absolute",
        "TestExtractionBoundaries/traversal",
        "TestExtractionBoundaries/wrong_prefix",
        "TestExtractionBoundaries/duplicate",
        "TestExtractionBoundaries/outside_symlink",
        "TestExtractionBoundaries/absolute_symlink",
        "TestExtractionBoundaries/symlink_ancestor",
        "TestExtractionBoundaries/device",
        "TestExtractionBoundaries/hardlink",
        "TestStrictProtocol",
        "TestStrictProtocol/leading_log",
        "TestStrictProtocol/trailing_log",
        "TestStrictProtocol/two_records",
        "TestStrictProtocol/truncated",
        "TestStrictProtocol/unknown_field",
        "TestStrictProtocol/duplicate_field",
        "TestStrictProtocol/duplicate_nested",
        "TestStrictProtocol/missing_field",
        "TestStrictProtocol/wrong_version",
        "TestStrictProtocol/null_byte",
        "TestStrictProtocol/negative_byte",
        "TestStrictProtocol/float_byte",
        "TestStrictProtocol/oversized_byte",
        "TestStrictProtocol/wrong_echo",
        "TestStrictProtocol/axiom_null",
        "TestStrictProtocol/forbidden_axiom",
        "TestStrictProtocol/duplicate_axiom",
        "TestStrictProtocol/unsorted_axioms",
        "TestStrictProtocol/wrong_root",
        "TestStrictProtocol/wrong_declaration",
        "TestStrictProtocol/wrong_profile",
        "TestStrictProtocol/extra_whitespace_record",
        "TestProcessRefusal",
        "TestZeroAuthority",
        "TestSnapshotsAndDriver",
        "TestInstallRefusesUntrustedArchive",
        "TestRealKernelAdmission",
        "TestRealKernelAdmission/ValidRecordThenFailure",
        "TestRealKernelAdmission/CanceledQueue",
        "TestRealKernelAdmission/CloseActiveRequest",
    )),
    "checked-bitwise-bundle": Suite("./compiler", "50m", (
        "TestEmitKernelCheckedBitwiseBundleRefusesInvalidInstallation",
        "TestEmitKernelCheckedBitwiseBundleRefusesInvalidInstallation/nil",
        "TestEmitKernelCheckedBitwiseBundleRefusesInvalidInstallation/zero",
        "TestEmitKernelCheckedBitwiseBundleRefusesCanceledContext",
        "TestKernelCheckedBitwiseBundleDoesNotPromoteLegacyAuthority",
        "TestVerifiedProfileClosesOverCallees",
        "TestVerdictCacheRoundTripsDependencies",
        "TestVerdictCacheRejectsMalformedDependencyRecords",
        "TestVerdictCacheKeyIncludesMachineOnlyCalleeBodies",
        "TestVerdictCacheMachineCalleesAgreeWithStrictResolver",
        "TestEmitKernelCheckedBitwiseBundleReal",
        "TestEmitKernelCheckedBitwiseBundleReal/Canonical",
        "TestEmitKernelCheckedBitwiseBundleReal/Canonical/bitwise/and",
        "TestEmitKernelCheckedBitwiseBundleReal/Canonical/bitwise/or",
        "TestEmitKernelCheckedBitwiseBundleReal/Canonical/bitwise/xor",
        "TestEmitKernelCheckedBitwiseBundleReal/Canonical/Mix9/and",
        "TestEmitKernelCheckedBitwiseBundleReal/Canonical/Mix9/or",
        "TestEmitKernelCheckedBitwiseBundleReal/Canonical/Mix9/xor",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/comment",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/extra_declaration",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/crlf",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/bom",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/wrong_type",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/wrong_reference",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/swapped_references",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/spacing",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/missing_lf",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/unsupported_operation",
        "TestEmitKernelCheckedBitwiseBundleReal/SourceRefusals/oversized",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals/source_operation",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals/source_name",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals/wasm_trailing",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals/wasm_truncated",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals/arm_body",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals/arm_trailing",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals/rv_abi",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals/rv_body",
        "TestEmitKernelCheckedBitwiseBundleReal/ArtifactRefusals/swapped_targets",
        "TestEmitKernelCheckedBitwiseBundleReal/CopyCustody",
        "TestEmitKernelCheckedBitwiseBundleReal/RenamedParametersFreshAdmission",
        "TestEmitKernelCheckedBitwiseBundleReal/Canceled",
        "TestEmitKernelCheckedBitwiseBundleReal/StageCancellation",
        "TestEmitKernelCheckedBitwiseBundleReal/StageCancellation/wasm",
        "TestEmitKernelCheckedBitwiseBundleReal/StageCancellation/arm64",
        "TestEmitKernelCheckedBitwiseBundleReal/StageCancellation/rv64",
        "TestEmitKernelCheckedBitwiseBundleReal/Closed",
    )),
    "native-object": Suite("./compiler", "15m", (
        "TestNativeBitwiseObjectLean",
    )),
    "strict-entry": Suite("./compiler", "30m", (
        "TestRV64StrictEntryToolchainSelection",
        "TestRV64StrictEntryBitwiseCompilerMatchesLean",
        "TestRV64StrictEntryBitwiseCompilerMatchesLean/interfaces",
        "TestRV64StrictEntryBitwiseCompilerMatchesLean/pins",
        "TestRV64StrictEntryBitwiseCompilerMatchesLean/audit",
    ), exact_children=True),
    "native-image": Suite("./compiler", "30m", (
        "TestNativeBitwiseImageLean",
    )),
    "cross-compiler": Suite("./compiler", "15m", (
        "TestE2EInferredValueNativeRV64UnderQEMU",
        "TestE2EDispatchSelectsSVEUnderQEMU",
        "TestE2EFreestandingPartialLink",
        "TestE2ENativeConstantTablesExecutable",
        "TestE2ENativeConstantTablesExecutable/freestanding/riscv64",
        "TestE2ENativeConstantTablesExecutable/freestanding/arm64",
        "TestRingsCrossTargets",
        "TestRingsCrossTargets/linux/riscv64",
        "TestRingsCrossTargets/linux/arm64",
    )),
    "cross-testrunner": Suite("./testrunner", "10m", (
        "TestForeignTargetRunsUnderEmulator",
        "TestTargetFlagBuildsWithoutRunning",
    )),
    "lean-compiler": Suite("./compiler", "10m", (
        "TestLeanFloatBitsAgreeWithHost",
        "TestE2ELeanFunctionArguments",
        "TestE2ELeanFunctionArguments/Lean",
        "TestE2ELeanReduceLanesFunctionArgument",
        "TestE2ELeanReduceLanesFunctionArgument/Lean",
        "TestE2ELeanNestedAssignment",
        "TestE2ELeanNestedAssignment/Lean",
    )),
    "lean-cli": Suite(".", "10m", (
        "TestBuildLeanNamespace",
        "TestBuildLeanNamespace/LeanImports",
    )),
    "sail-source": Suite("./asm", "10m", (
        "TestSailArmBRKDispatchSource",
        "TestSailArmCBZ32DispatchSource",
        "TestScalarADDPPinnedSailContract",
        "TestScalarADDPPinnedSailContract/vector_reduce_add_sisd_decode",
        "TestScalarADDPPinnedSailContract/vector_reduce_add_sisd",
        "TestScalarADDPPinnedSailContract/Reduce",
        "TestScalarADDPPinnedSailContract/aset_V",
    )),
    "llvm": Suite("./asm", "10m", (
        "TestEncoderAgainstLLVM",
        "TestEncoderFuzzAgainstLLVM",
        "TestEncodeFunctionAgainstLLVM",
        "TestObjectsAgainstLLVMTools",
        "TestObjectsAgainstLLVMTools/macho",
        "TestObjectsAgainstLLVMTools/elf",
        "TestSMEAgainstLLVM",
        "TestSystemRegistersAgainstLLVM",
    )),
}


class RequiredResults:
    def __init__(self, suite):
        self.suite = suite
        self.passed = set()
        self.running = set()
        self.package_passed = False
        self.errors = []

    def accept(self, event):
        if not isinstance(event, dict):
            raise ValueError("Go test JSON event is not an object")
        action = event.get("Action")
        if action not in {"start", "run", "pause", "cont", "pass", "bench", "fail", "output", "skip"}:
            raise ValueError(f"unknown Go test action: {action!r}")
        if event.get("Package") != self.suite.import_path:
            raise ValueError(f"unexpected Go test package: {event.get('Package')!r}")
        name = event.get("Test", "")
        if not isinstance(name, str):
            raise ValueError("invalid Go test name")
        if name and name.split("/", 1)[0] not in self.suite.roots:
            raise ValueError(f"unexpected selected test: {name}")
        if name and self.suite.exact_children and name not in self.suite.tests:
            raise ValueError(f"unexpected unlisted test: {name}")
        if action == "run" and name:
            if name in self.running or name in self.passed:
                raise ValueError(f"duplicate test run: {name}")
            self.running.add(name)
        if action in {"pass", "skip", "fail"} and name:
            if name not in self.running:
                raise ValueError(f"test finished without a run event: {name}")
            self.running.remove(name)
        if action in {"skip", "fail"}:
            self.errors.append(f"{name or self.suite.package}: {action}")
        elif action == "pass":
            if name:
                self.passed.add(name)
            else:
                self.package_passed = True
        if "Output" in event and not isinstance(event["Output"], str):
            raise ValueError("invalid Go test output")

    def finish(self, returncode):
        errors = list(self.errors)
        if returncode != 0:
            errors.append(f"go test exited {returncode}")
        if self.running:
            errors.append("tests did not finish: " + ", ".join(sorted(self.running)))
        missing = set(self.suite.tests) - self.passed
        if missing:
            errors.append("required tests did not pass: " + ", ".join(sorted(missing)))
        if not self.package_passed:
            errors.append("package did not pass")
        if errors:
            raise ValueError("\n".join(errors))


def check_inventory(suite):
    # Go itself evaluates this regex; renames/removals must not silently turn
    # a required command into a successful no-tests run.
    output = subprocess.check_output(
        ["go", "test"] + (["-race"] if suite.race else []) + [suite.package, "-list", suite.pattern], text=True,
    )
    names = [line for line in output.splitlines() if line.startswith("Test")]
    if sorted(names) != suite.roots:
        raise ValueError(f"{suite.package}: expected {suite.roots}, selected {names}")


def run_suite(suite):
    command = ["go", "test"] + (["-race"] if suite.race else []) + ["-json", "-count=1", "-timeout=" + suite.timeout,
               suite.package, "-run", suite.pattern]
    print("Required backend checks: " + " ".join(command), flush=True)
    results = RequiredResults(suite)
    # Merge stderr so compiler/process errors cannot escape JSON validation.
    with subprocess.Popen(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True, encoding="utf-8") as process:
        try:
            for line in process.stdout:
                try:
                    event = json.loads(line)
                except ValueError as error:
                    raise ValueError(f"invalid Go test JSON: {line.rstrip()}") from error
                results.accept(event)
                if "Output" in event:
                    print(event["Output"], end="", flush=True)
            returncode = process.wait()
        except BaseException:
            process.terminate()
            process.wait()
            raise
    results.finish(returncode)
    print(f"Required backend checks passed: {len(suite.tests)} named checks; no skips", flush=True)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("suite", choices=SUITES, nargs="?")
    parser.add_argument("--check", action="store_true", help="validate all selectors against Go")
    args = parser.parse_args(argv)
    if not args.check and args.suite is None:
        parser.error("choose a suite or --check")
    try:
        if args.check:
            for name, suite in SUITES.items():
                check_inventory(suite)
                print(f"{name}: {len(suite.roots)} roots selected exactly", flush=True)
        else:
            run_suite(SUITES[args.suite])
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Required backend checks FAILED: {error}", file=sys.stderr, flush=True)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
