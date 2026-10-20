import Oak.NativeBitwiseObject

/-!
# Complete production native object fixtures

The byte literals below are complete outputs of the unchanged production
`compiler.EmitNativeObject(asm.ELF)` path, from the included original sources.
All admission/refusal facts use kernel reduction of the full ELF objects.
The Go inspection and mutation manifests are diagnostic generators only.
These finite fixtures neither prove whole-compiler correctness nor change
production verification authority. Original-source parsing is not claimed.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
namespace Oak.NativeBitwiseObjectFixtures
open Oak.NativeBitwiseObject
open Oak.MinimalELF (Bytes)

/-- Write exactly width low little-endian bytes, using bounded List.set. -/
def setLE (image : Bytes) (offset width value : Nat) : Bytes :=
  (List.range width).foldl (fun bytes i =>
    bytes.set (offset + i) (BitVec.ofNat 8 (value / 256^i % 256))) image

namespace arm64_bitwise_and
def source : List UInt8 := [98,105,116,119,105,115,101,58,32,40,120,58,32,117,51,50,44,32,121,58,32,117,51,50,41,58,32,117,51,50,32,61,32,120,32,38,32,121,10]
def name : List UInt8 := [98,105,116,119,105,115,101]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,183,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,240,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,0,0,1,10,192,3,95,214,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,168,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,181,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .arm64 nameBytes image (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = true := by decide +kernel
end arm64_bitwise_and

namespace arm64_bitwise_and
theorem reject_header_ident_0 : accepts .arm64 nameBytes (image.set 0 ((image.getD 0 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_1 : accepts .arm64 nameBytes (image.set 1 ((image.getD 1 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_2 : accepts .arm64 nameBytes (image.set 2 ((image.getD 2 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_3 : accepts .arm64 nameBytes (image.set 3 ((image.getD 3 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_4 : accepts .arm64 nameBytes (image.set 4 ((image.getD 4 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_5 : accepts .arm64 nameBytes (image.set 5 ((image.getD 5 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_6 : accepts .arm64 nameBytes (image.set 6 ((image.getD 6 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_7 : accepts .arm64 nameBytes (image.set 7 ((image.getD 7 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_8 : accepts .arm64 nameBytes (image.set 8 ((image.getD 8 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_9 : accepts .arm64 nameBytes (image.set 9 ((image.getD 9 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_10 : accepts .arm64 nameBytes (image.set 10 ((image.getD 10 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_11 : accepts .arm64 nameBytes (image.set 11 ((image.getD 11 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_12 : accepts .arm64 nameBytes (image.set 12 ((image.getD 12 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_13 : accepts .arm64 nameBytes (image.set 13 ((image.getD 13 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_14 : accepts .arm64 nameBytes (image.set 14 ((image.getD 14 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ident_15 : accepts .arm64 nameBytes (image.set 15 ((image.getD 15 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_type : accepts .arm64 nameBytes (setLE image 16 2 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_machine : accepts .arm64 nameBytes (setLE image 18 2 182) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_version : accepts .arm64 nameBytes (setLE image 20 4 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_entry : accepts .arm64 nameBytes (setLE image 24 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_phoff : accepts .arm64 nameBytes (setLE image 32 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_shoff : accepts .arm64 nameBytes (setLE image 40 8 241) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_flags : accepts .arm64 nameBytes (setLE image 48 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_ehsize : accepts .arm64 nameBytes (setLE image 52 2 65) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_phentsize : accepts .arm64 nameBytes (setLE image 54 2 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_phnum : accepts .arm64 nameBytes (setLE image 56 2 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_shentsize : accepts .arm64 nameBytes (setLE image 58 2 65) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_shnum : accepts .arm64 nameBytes (setLE image 60 2 6) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_header_shstrndx : accepts .arm64 nameBytes (setLE image 62 2 7) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_name : accepts .arm64 nameBytes (setLE image 240 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_type : accepts .arm64 nameBytes (setLE image 244 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_flags : accepts .arm64 nameBytes (setLE image 248 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_addr : accepts .arm64 nameBytes (setLE image 256 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_offset : accepts .arm64 nameBytes (setLE image 264 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_size : accepts .arm64 nameBytes (setLE image 272 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_link : accepts .arm64 nameBytes (setLE image 280 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_info : accepts .arm64 nameBytes (setLE image 284 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_align : accepts .arm64 nameBytes (setLE image 288 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_0_entsize : accepts .arm64 nameBytes (setLE image 296 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_name : accepts .arm64 nameBytes (setLE image 304 4 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_type : accepts .arm64 nameBytes (setLE image 308 4 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_flags : accepts .arm64 nameBytes (setLE image 312 8 7) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_addr : accepts .arm64 nameBytes (setLE image 320 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_offset : accepts .arm64 nameBytes (setLE image 328 8 65) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_size : accepts .arm64 nameBytes (setLE image 336 8 9) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_link : accepts .arm64 nameBytes (setLE image 344 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_info : accepts .arm64 nameBytes (setLE image 348 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_align : accepts .arm64 nameBytes (setLE image 352 8 5) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_1_entsize : accepts .arm64 nameBytes (setLE image 360 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_name : accepts .arm64 nameBytes (setLE image 368 4 6) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_type : accepts .arm64 nameBytes (setLE image 372 4 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_flags : accepts .arm64 nameBytes (setLE image 376 8 3) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_addr : accepts .arm64 nameBytes (setLE image 384 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_offset : accepts .arm64 nameBytes (setLE image 392 8 73) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_size : accepts .arm64 nameBytes (setLE image 400 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_link : accepts .arm64 nameBytes (setLE image 408 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_info : accepts .arm64 nameBytes (setLE image 412 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_align : accepts .arm64 nameBytes (setLE image 416 8 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_2_entsize : accepts .arm64 nameBytes (setLE image 424 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_name : accepts .arm64 nameBytes (setLE image 432 4 14) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_type : accepts .arm64 nameBytes (setLE image 436 4 5) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_flags : accepts .arm64 nameBytes (setLE image 440 8 65) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_addr : accepts .arm64 nameBytes (setLE image 448 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_offset : accepts .arm64 nameBytes (setLE image 456 8 73) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_size : accepts .arm64 nameBytes (setLE image 464 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_link : accepts .arm64 nameBytes (setLE image 472 4 5) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_info : accepts .arm64 nameBytes (setLE image 476 4 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_align : accepts .arm64 nameBytes (setLE image 480 8 9) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_3_entsize : accepts .arm64 nameBytes (setLE image 488 8 25) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_name : accepts .arm64 nameBytes (setLE image 496 4 27) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_type : accepts .arm64 nameBytes (setLE image 500 4 3) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_flags : accepts .arm64 nameBytes (setLE image 504 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_addr : accepts .arm64 nameBytes (setLE image 512 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_offset : accepts .arm64 nameBytes (setLE image 520 8 73) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_size : accepts .arm64 nameBytes (setLE image 528 8 97) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_link : accepts .arm64 nameBytes (setLE image 536 4 4) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_info : accepts .arm64 nameBytes (setLE image 540 4 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_align : accepts .arm64 nameBytes (setLE image 544 8 9) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_4_entsize : accepts .arm64 nameBytes (setLE image 552 8 25) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_name : accepts .arm64 nameBytes (setLE image 560 4 35) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_type : accepts .arm64 nameBytes (setLE image 564 4 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_flags : accepts .arm64 nameBytes (setLE image 568 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_addr : accepts .arm64 nameBytes (setLE image 576 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_offset : accepts .arm64 nameBytes (setLE image 584 8 169) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_size : accepts .arm64 nameBytes (setLE image 592 8 12) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_link : accepts .arm64 nameBytes (setLE image 600 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_info : accepts .arm64 nameBytes (setLE image 604 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_align : accepts .arm64 nameBytes (setLE image 608 8 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_5_entsize : accepts .arm64 nameBytes (setLE image 616 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_name : accepts .arm64 nameBytes (setLE image 624 4 43) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_type : accepts .arm64 nameBytes (setLE image 628 4 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_flags : accepts .arm64 nameBytes (setLE image 632 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_addr : accepts .arm64 nameBytes (setLE image 640 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_offset : accepts .arm64 nameBytes (setLE image 648 8 180) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_size : accepts .arm64 nameBytes (setLE image 656 8 53) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_link : accepts .arm64 nameBytes (setLE image 664 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_info : accepts .arm64 nameBytes (setLE image 668 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_align : accepts .arm64 nameBytes (setLE image 672 8 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_6_entsize : accepts .arm64 nameBytes (setLE image 680 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_0_name : accepts .arm64 nameBytes (setLE image 72 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_0_info : accepts .arm64 nameBytes (setLE image 76 1 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_0_other : accepts .arm64 nameBytes (setLE image 77 1 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_0_shndx : accepts .arm64 nameBytes (setLE image 78 2 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_0_value : accepts .arm64 nameBytes (setLE image 80 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_0_size : accepts .arm64 nameBytes (setLE image 88 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_1_name : accepts .arm64 nameBytes (setLE image 96 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_1_info : accepts .arm64 nameBytes (setLE image 100 1 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_1_other : accepts .arm64 nameBytes (setLE image 101 1 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_1_shndx : accepts .arm64 nameBytes (setLE image 102 2 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_1_value : accepts .arm64 nameBytes (setLE image 104 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_1_size : accepts .arm64 nameBytes (setLE image 112 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_2_name : accepts .arm64 nameBytes (setLE image 120 4 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_2_info : accepts .arm64 nameBytes (setLE image 124 1 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_2_other : accepts .arm64 nameBytes (setLE image 125 1 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_2_shndx : accepts .arm64 nameBytes (setLE image 126 2 3) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_2_value : accepts .arm64 nameBytes (setLE image 128 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_2_size : accepts .arm64 nameBytes (setLE image 136 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_3_name : accepts .arm64 nameBytes (setLE image 144 4 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_3_info : accepts .arm64 nameBytes (setLE image 148 1 19) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_3_other : accepts .arm64 nameBytes (setLE image 149 1 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_3_shndx : accepts .arm64 nameBytes (setLE image 150 2 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_3_value : accepts .arm64 nameBytes (setLE image 152 8 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_3_size : accepts .arm64 nameBytes (setLE image 160 8 9) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_body_byte_64 : accepts .arm64 nameBytes (image.set 64 ((image.getD 64 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_body_byte_65 : accepts .arm64 nameBytes (image.set 65 ((image.getD 65 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_body_byte_66 : accepts .arm64 nameBytes (image.set 66 ((image.getD 66 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_body_byte_67 : accepts .arm64 nameBytes (image.set 67 ((image.getD 67 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_body_byte_68 : accepts .arm64 nameBytes (image.set 68 ((image.getD 68 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_body_byte_69 : accepts .arm64 nameBytes (image.set 69 ((image.getD 69 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_body_byte_70 : accepts .arm64 nameBytes (image.set 70 ((image.getD 70 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_body_byte_71 : accepts .arm64 nameBytes (image.set 71 ((image.getD 71 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_168 : accepts .arm64 nameBytes (image.set 168 ((image.getD 168 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_169 : accepts .arm64 nameBytes (image.set 169 ((image.getD 169 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_170 : accepts .arm64 nameBytes (image.set 170 ((image.getD 170 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_171 : accepts .arm64 nameBytes (image.set 171 ((image.getD 171 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_172 : accepts .arm64 nameBytes (image.set 172 ((image.getD 172 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_173 : accepts .arm64 nameBytes (image.set 173 ((image.getD 173 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_174 : accepts .arm64 nameBytes (image.set 174 ((image.getD 174 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_175 : accepts .arm64 nameBytes (image.set 175 ((image.getD 175 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_176 : accepts .arm64 nameBytes (image.set 176 ((image.getD 176 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_177 : accepts .arm64 nameBytes (image.set 177 ((image.getD 177 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_178 : accepts .arm64 nameBytes (image.set 178 ((image.getD 178 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_179 : accepts .arm64 nameBytes (image.set 179 ((image.getD 179 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_byte_180 : accepts .arm64 nameBytes (image.set 180 ((image.getD 180 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_181 : accepts .arm64 nameBytes (image.set 181 ((image.getD 181 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_182 : accepts .arm64 nameBytes (image.set 182 ((image.getD 182 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_183 : accepts .arm64 nameBytes (image.set 183 ((image.getD 183 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_184 : accepts .arm64 nameBytes (image.set 184 ((image.getD 184 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_185 : accepts .arm64 nameBytes (image.set 185 ((image.getD 185 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_186 : accepts .arm64 nameBytes (image.set 186 ((image.getD 186 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_187 : accepts .arm64 nameBytes (image.set 187 ((image.getD 187 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_188 : accepts .arm64 nameBytes (image.set 188 ((image.getD 188 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_189 : accepts .arm64 nameBytes (image.set 189 ((image.getD 189 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_190 : accepts .arm64 nameBytes (image.set 190 ((image.getD 190 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_191 : accepts .arm64 nameBytes (image.set 191 ((image.getD 191 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_192 : accepts .arm64 nameBytes (image.set 192 ((image.getD 192 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_193 : accepts .arm64 nameBytes (image.set 193 ((image.getD 193 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_194 : accepts .arm64 nameBytes (image.set 194 ((image.getD 194 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_195 : accepts .arm64 nameBytes (image.set 195 ((image.getD 195 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_196 : accepts .arm64 nameBytes (image.set 196 ((image.getD 196 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_197 : accepts .arm64 nameBytes (image.set 197 ((image.getD 197 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_198 : accepts .arm64 nameBytes (image.set 198 ((image.getD 198 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_199 : accepts .arm64 nameBytes (image.set 199 ((image.getD 199 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_200 : accepts .arm64 nameBytes (image.set 200 ((image.getD 200 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_201 : accepts .arm64 nameBytes (image.set 201 ((image.getD 201 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_202 : accepts .arm64 nameBytes (image.set 202 ((image.getD 202 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_203 : accepts .arm64 nameBytes (image.set 203 ((image.getD 203 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_204 : accepts .arm64 nameBytes (image.set 204 ((image.getD 204 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_205 : accepts .arm64 nameBytes (image.set 205 ((image.getD 205 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_206 : accepts .arm64 nameBytes (image.set 206 ((image.getD 206 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_207 : accepts .arm64 nameBytes (image.set 207 ((image.getD 207 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_208 : accepts .arm64 nameBytes (image.set 208 ((image.getD 208 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_209 : accepts .arm64 nameBytes (image.set 209 ((image.getD 209 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_210 : accepts .arm64 nameBytes (image.set 210 ((image.getD 210 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_211 : accepts .arm64 nameBytes (image.set 211 ((image.getD 211 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_212 : accepts .arm64 nameBytes (image.set 212 ((image.getD 212 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_213 : accepts .arm64 nameBytes (image.set 213 ((image.getD 213 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_214 : accepts .arm64 nameBytes (image.set 214 ((image.getD 214 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_215 : accepts .arm64 nameBytes (image.set 215 ((image.getD 215 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_216 : accepts .arm64 nameBytes (image.set 216 ((image.getD 216 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_217 : accepts .arm64 nameBytes (image.set 217 ((image.getD 217 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_218 : accepts .arm64 nameBytes (image.set 218 ((image.getD 218 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_219 : accepts .arm64 nameBytes (image.set 219 ((image.getD 219 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_220 : accepts .arm64 nameBytes (image.set 220 ((image.getD 220 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_221 : accepts .arm64 nameBytes (image.set 221 ((image.getD 221 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_222 : accepts .arm64 nameBytes (image.set 222 ((image.getD 222 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_223 : accepts .arm64 nameBytes (image.set 223 ((image.getD 223 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_224 : accepts .arm64 nameBytes (image.set 224 ((image.getD 224 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_225 : accepts .arm64 nameBytes (image.set 225 ((image.getD 225 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_226 : accepts .arm64 nameBytes (image.set 226 ((image.getD 226 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_227 : accepts .arm64 nameBytes (image.set 227 ((image.getD 227 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_228 : accepts .arm64 nameBytes (image.set 228 ((image.getD 228 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_229 : accepts .arm64 nameBytes (image.set 229 ((image.getD 229 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_230 : accepts .arm64 nameBytes (image.set 230 ((image.getD 230 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_231 : accepts .arm64 nameBytes (image.set 231 ((image.getD 231 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_names_byte_232 : accepts .arm64 nameBytes (image.set 232 ((image.getD 232 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_padding_byte_233 : accepts .arm64 nameBytes (image.set 233 ((image.getD 233 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_padding_byte_234 : accepts .arm64 nameBytes (image.set 234 ((image.getD 234 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_padding_byte_235 : accepts .arm64 nameBytes (image.set 235 ((image.getD 235 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_padding_byte_236 : accepts .arm64 nameBytes (image.set 236 ((image.getD 236 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_padding_byte_237 : accepts .arm64 nameBytes (image.set 237 ((image.getD 237 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_padding_byte_238 : accepts .arm64 nameBytes (image.set 238 ((image.getD 238 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_padding_byte_239 : accepts .arm64 nameBytes (image.set 239 ((image.getD 239 0) ^^^ (BitVec.ofNat 8 1))) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_0 : accepts .arm64 nameBytes (image.take 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_1 : accepts .arm64 nameBytes (image.take 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_15 : accepts .arm64 nameBytes (image.take 15) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_63 : accepts .arm64 nameBytes (image.take 63) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_64 : accepts .arm64 nameBytes (image.take 64) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_71 : accepts .arm64 nameBytes (image.take 71) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_72 : accepts .arm64 nameBytes (image.take 72) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_168 : accepts .arm64 nameBytes (image.take 168) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_181 : accepts .arm64 nameBytes (image.take 181) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_240 : accepts .arm64 nameBytes (image.take 240) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_truncate_687 : accepts .arm64 nameBytes (image.take 687) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_append_zero : accepts .arm64 nameBytes (image ++ [0]) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_append_one : accepts .arm64 nameBytes (image ++ [1]) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_text_offset_overflow : accepts .arm64 nameBytes (setLE image 328 8 18446744073709551615) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_section_text_overlap_header : accepts .arm64 nameBytes (setLE image 328 8 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_function_undefined : accepts .arm64 nameBytes (setLE image 150 2 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_function_local : accepts .arm64 nameBytes (setLE image 148 1 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_function_short_prefix : accepts .arm64 nameBytes (setLE image 160 8 4) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_symbol_function_name_alias_null : accepts .arm64 nameBytes (setLE image 144 4 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_e_shoff_inside_header : accepts .arm64 nameBytes (setLE image 40 8 40) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_e_shoff_overflow : accepts .arm64 nameBytes (setLE image 40 8 18446744073709551615) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_text_offset_inside_header : accepts .arm64 nameBytes (setLE image 328 8 40) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_text_offset_overflow : accepts .arm64 nameBytes (setLE image 328 8 18446744073709551615) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_truncate_function_symbol : accepts .arm64 nameBytes (image.take 167) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_truncate_final_section : accepts .arm64 nameBytes (image.take 687) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_function_name_alias_suffix : accepts .arm64 nameBytes (setLE image 144 4 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_function_undefined : accepts .arm64 nameBytes (setLE image 150 2 0) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_function_in_rodata : accepts .arm64 nameBytes (setLE image 150 2 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_function_local_info2 : accepts .arm64 nameBytes (setLE image 148 1 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_function_global_object_info17 : accepts .arm64 nameBytes (setLE image 148 1 17) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
-- The symbol no longer covers the whole text section.
theorem reject_targeted_function_suffix_value4 : accepts .arm64 nameBytes (setLE (setLE image 152 8 4) 160 8 4) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_function_short_good_prefix : accepts .arm64 nameBytes (setLE image 160 8 4) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_function_extent_into_padding_or_symbols : accepts .arm64 nameBytes (setLE image 160 8 12) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_text_missing_exec : accepts .arm64 nameBytes (setLE image 312 8 2) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_symtab_wrong_string_link : accepts .arm64 nameBytes (setLE image 536 4 6) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_append_zero : accepts .arm64 nameBytes (image ++ [0]) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_append_extra_symbol_record : accepts .arm64 nameBytes (image ++ [1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0]) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_nonzero_padding_233 : accepts .arm64 nameBytes (setLE image 233 1 1) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_targeted_arm_wrong_flags4 : accepts .arm64 nameBytes (setLE image 48 4 4) (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
def targeted_extra_duplicate_function_symbolImage : Bytes := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,183,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,1,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,0,0,1,10,192,3,95,214,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,120,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,192,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,205,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
-- Complete ELF with five symbols; later payload/table offsets shifted consistently.
theorem reject_targeted_extra_duplicate_function_symbol : accepts .arm64 nameBytes targeted_extra_duplicate_function_symbolImage (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
def targeted_extra_relocation_touching_bodyImage : Bytes := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,183,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,1,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,0,0,1,10,192,3,95,214,0,0,0,0,0,0,0,0,27,1,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,192,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,205,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
-- Complete ELF with one relocation into .text; later payload/table offsets shifted consistently.
theorem reject_targeted_extra_relocation_touching_body : accepts .arm64 nameBytes targeted_extra_relocation_touching_bodyImage (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
def targeted_and_object_with_or_opcodeImage : Bytes := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,183,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,240,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,0,0,1,42,192,3,95,214,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,168,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,181,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
-- Retain AND expected operation and source; body is actual corresponding OR emission.
theorem reject_targeted_and_object_with_or_opcode : accepts .arm64 nameBytes targeted_and_object_with_or_opcodeImage (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_wrong_target : accepts .rv64 nameBytes image (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_name_replay : accepts .arm64 (fromUInt8 [77,105,120,57]) image (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_embedded_nul_requested_name : accepts .arm64 (nameBytes ++ [0,120]) image (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = false := by decide +kernel
theorem reject_operation_replay : accepts .arm64 nameBytes image (fromUInt8 (AArch64BitwiseFunction.functionBytes .or)) = false := by decide +kernel
end arm64_bitwise_and

namespace arm64_bitwise_or
def source : List UInt8 := [98,105,116,119,105,115,101,58,32,40,120,58,32,117,51,50,44,32,121,58,32,117,51,50,41,58,32,117,51,50,32,61,32,120,32,124,32,121,10]
def name : List UInt8 := [98,105,116,119,105,115,101]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,183,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,240,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,0,0,1,42,192,3,95,214,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,168,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,181,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .arm64 nameBytes image (fromUInt8 (AArch64BitwiseFunction.functionBytes .or)) = true := by decide +kernel
end arm64_bitwise_or

namespace arm64_bitwise_xor
def source : List UInt8 := [98,105,116,119,105,115,101,58,32,40,120,58,32,117,51,50,44,32,121,58,32,117,51,50,41,58,32,117,51,50,32,61,32,120,32,94,32,121,10]
def name : List UInt8 := [98,105,116,119,105,115,101]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,183,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,240,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,0,0,1,74,192,3,95,214,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,168,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,181,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .arm64 nameBytes image (fromUInt8 (AArch64BitwiseFunction.functionBytes .xor)) = true := by decide +kernel
end arm64_bitwise_xor

namespace arm64_Mix9_and
def source : List UInt8 := [77,105,120,57,58,32,40,108,101,102,116,48,58,32,117,51,50,44,32,82,105,103,104,116,57,58,32,117,51,50,41,58,32,117,51,50,32,61,32,108,101,102,116,48,32,38,32,82,105,103,104,116,57,10]
def name : List UInt8 := [77,105,120,57]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,183,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,232,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,0,0,1,10,192,3,95,214,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,111,97,107,95,77,105,120,57,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,168,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,178,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .arm64 nameBytes image (fromUInt8 (AArch64BitwiseFunction.functionBytes .and)) = true := by decide +kernel
end arm64_Mix9_and

namespace arm64_Mix9_or
def source : List UInt8 := [77,105,120,57,58,32,40,108,101,102,116,48,58,32,117,51,50,44,32,82,105,103,104,116,57,58,32,117,51,50,41,58,32,117,51,50,32,61,32,108,101,102,116,48,32,124,32,82,105,103,104,116,57,10]
def name : List UInt8 := [77,105,120,57]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,183,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,232,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,0,0,1,42,192,3,95,214,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,111,97,107,95,77,105,120,57,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,168,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,178,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .arm64 nameBytes image (fromUInt8 (AArch64BitwiseFunction.functionBytes .or)) = true := by decide +kernel
end arm64_Mix9_or

namespace arm64_Mix9_xor
def source : List UInt8 := [77,105,120,57,58,32,40,108,101,102,116,48,58,32,117,51,50,44,32,82,105,103,104,116,57,58,32,117,51,50,41,58,32,117,51,50,32,61,32,108,101,102,116,48,32,94,32,82,105,103,104,116,57,10]
def name : List UInt8 := [77,105,120,57]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,183,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,232,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,0,0,1,74,192,3,95,214,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,111,97,107,95,77,105,120,57,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,72,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,168,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,178,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .arm64 nameBytes image (fromUInt8 (AArch64BitwiseFunction.functionBytes .xor)) = true := by decide +kernel
end arm64_Mix9_xor

namespace riscv64_bitwise_and
def source : List UInt8 := [98,105,116,119,105,115,101,58,32,40,120,58,32,117,51,50,44,32,121,58,32,117,51,50,41,58,32,117,51,50,32,61,32,120,32,38,32,121,10]
def name : List UInt8 := [98,105,116,119,105,115,101]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,19,1,1,250,35,48,145,0,35,52,33,1,19,137,5,0,51,117,181,0,131,52,1,0,3,57,129,0,19,1,1,6,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,200,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .rv64 nameBytes image (RiscVFramedBitwise.functionBytes .and) = true := by decide +kernel
end riscv64_bitwise_and

namespace riscv64_bitwise_and
theorem reject_header_ident_0 : accepts .rv64 nameBytes (image.set 0 ((image.getD 0 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_1 : accepts .rv64 nameBytes (image.set 1 ((image.getD 1 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_2 : accepts .rv64 nameBytes (image.set 2 ((image.getD 2 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_3 : accepts .rv64 nameBytes (image.set 3 ((image.getD 3 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_4 : accepts .rv64 nameBytes (image.set 4 ((image.getD 4 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_5 : accepts .rv64 nameBytes (image.set 5 ((image.getD 5 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_6 : accepts .rv64 nameBytes (image.set 6 ((image.getD 6 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_7 : accepts .rv64 nameBytes (image.set 7 ((image.getD 7 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_8 : accepts .rv64 nameBytes (image.set 8 ((image.getD 8 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_9 : accepts .rv64 nameBytes (image.set 9 ((image.getD 9 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_10 : accepts .rv64 nameBytes (image.set 10 ((image.getD 10 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_11 : accepts .rv64 nameBytes (image.set 11 ((image.getD 11 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_12 : accepts .rv64 nameBytes (image.set 12 ((image.getD 12 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_13 : accepts .rv64 nameBytes (image.set 13 ((image.getD 13 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_14 : accepts .rv64 nameBytes (image.set 14 ((image.getD 14 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ident_15 : accepts .rv64 nameBytes (image.set 15 ((image.getD 15 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_type : accepts .rv64 nameBytes (setLE image 16 2 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_machine : accepts .rv64 nameBytes (setLE image 18 2 242) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_version : accepts .rv64 nameBytes (setLE image 20 4 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_entry : accepts .rv64 nameBytes (setLE image 24 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_phoff : accepts .rv64 nameBytes (setLE image 32 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_shoff : accepts .rv64 nameBytes (setLE image 40 8 273) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_flags : accepts .rv64 nameBytes (setLE image 48 4 5) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_ehsize : accepts .rv64 nameBytes (setLE image 52 2 65) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_phentsize : accepts .rv64 nameBytes (setLE image 54 2 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_phnum : accepts .rv64 nameBytes (setLE image 56 2 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_shentsize : accepts .rv64 nameBytes (setLE image 58 2 65) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_shnum : accepts .rv64 nameBytes (setLE image 60 2 6) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_header_shstrndx : accepts .rv64 nameBytes (setLE image 62 2 7) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_name : accepts .rv64 nameBytes (setLE image 272 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_type : accepts .rv64 nameBytes (setLE image 276 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_flags : accepts .rv64 nameBytes (setLE image 280 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_addr : accepts .rv64 nameBytes (setLE image 288 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_offset : accepts .rv64 nameBytes (setLE image 296 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_size : accepts .rv64 nameBytes (setLE image 304 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_link : accepts .rv64 nameBytes (setLE image 312 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_info : accepts .rv64 nameBytes (setLE image 316 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_align : accepts .rv64 nameBytes (setLE image 320 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_0_entsize : accepts .rv64 nameBytes (setLE image 328 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_name : accepts .rv64 nameBytes (setLE image 336 4 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_type : accepts .rv64 nameBytes (setLE image 340 4 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_flags : accepts .rv64 nameBytes (setLE image 344 8 7) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_addr : accepts .rv64 nameBytes (setLE image 352 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_offset : accepts .rv64 nameBytes (setLE image 360 8 65) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_size : accepts .rv64 nameBytes (setLE image 368 8 37) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_link : accepts .rv64 nameBytes (setLE image 376 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_info : accepts .rv64 nameBytes (setLE image 380 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_align : accepts .rv64 nameBytes (setLE image 384 8 5) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_1_entsize : accepts .rv64 nameBytes (setLE image 392 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_name : accepts .rv64 nameBytes (setLE image 400 4 6) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_type : accepts .rv64 nameBytes (setLE image 404 4 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_flags : accepts .rv64 nameBytes (setLE image 408 8 3) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_addr : accepts .rv64 nameBytes (setLE image 416 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_offset : accepts .rv64 nameBytes (setLE image 424 8 105) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_size : accepts .rv64 nameBytes (setLE image 432 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_link : accepts .rv64 nameBytes (setLE image 440 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_info : accepts .rv64 nameBytes (setLE image 444 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_align : accepts .rv64 nameBytes (setLE image 448 8 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_2_entsize : accepts .rv64 nameBytes (setLE image 456 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_name : accepts .rv64 nameBytes (setLE image 464 4 14) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_type : accepts .rv64 nameBytes (setLE image 468 4 5) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_flags : accepts .rv64 nameBytes (setLE image 472 8 65) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_addr : accepts .rv64 nameBytes (setLE image 480 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_offset : accepts .rv64 nameBytes (setLE image 488 8 105) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_size : accepts .rv64 nameBytes (setLE image 496 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_link : accepts .rv64 nameBytes (setLE image 504 4 5) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_info : accepts .rv64 nameBytes (setLE image 508 4 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_align : accepts .rv64 nameBytes (setLE image 512 8 9) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_3_entsize : accepts .rv64 nameBytes (setLE image 520 8 25) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_name : accepts .rv64 nameBytes (setLE image 528 4 27) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_type : accepts .rv64 nameBytes (setLE image 532 4 3) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_flags : accepts .rv64 nameBytes (setLE image 536 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_addr : accepts .rv64 nameBytes (setLE image 544 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_offset : accepts .rv64 nameBytes (setLE image 552 8 105) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_size : accepts .rv64 nameBytes (setLE image 560 8 97) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_link : accepts .rv64 nameBytes (setLE image 568 4 4) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_info : accepts .rv64 nameBytes (setLE image 572 4 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_align : accepts .rv64 nameBytes (setLE image 576 8 9) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_4_entsize : accepts .rv64 nameBytes (setLE image 584 8 25) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_name : accepts .rv64 nameBytes (setLE image 592 4 35) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_type : accepts .rv64 nameBytes (setLE image 596 4 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_flags : accepts .rv64 nameBytes (setLE image 600 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_addr : accepts .rv64 nameBytes (setLE image 608 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_offset : accepts .rv64 nameBytes (setLE image 616 8 201) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_size : accepts .rv64 nameBytes (setLE image 624 8 12) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_link : accepts .rv64 nameBytes (setLE image 632 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_info : accepts .rv64 nameBytes (setLE image 636 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_align : accepts .rv64 nameBytes (setLE image 640 8 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_5_entsize : accepts .rv64 nameBytes (setLE image 648 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_name : accepts .rv64 nameBytes (setLE image 656 4 43) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_type : accepts .rv64 nameBytes (setLE image 660 4 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_flags : accepts .rv64 nameBytes (setLE image 664 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_addr : accepts .rv64 nameBytes (setLE image 672 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_offset : accepts .rv64 nameBytes (setLE image 680 8 212) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_size : accepts .rv64 nameBytes (setLE image 688 8 53) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_link : accepts .rv64 nameBytes (setLE image 696 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_info : accepts .rv64 nameBytes (setLE image 700 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_align : accepts .rv64 nameBytes (setLE image 704 8 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_6_entsize : accepts .rv64 nameBytes (setLE image 712 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_0_name : accepts .rv64 nameBytes (setLE image 104 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_0_info : accepts .rv64 nameBytes (setLE image 108 1 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_0_other : accepts .rv64 nameBytes (setLE image 109 1 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_0_shndx : accepts .rv64 nameBytes (setLE image 110 2 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_0_value : accepts .rv64 nameBytes (setLE image 112 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_0_size : accepts .rv64 nameBytes (setLE image 120 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_1_name : accepts .rv64 nameBytes (setLE image 128 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_1_info : accepts .rv64 nameBytes (setLE image 132 1 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_1_other : accepts .rv64 nameBytes (setLE image 133 1 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_1_shndx : accepts .rv64 nameBytes (setLE image 134 2 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_1_value : accepts .rv64 nameBytes (setLE image 136 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_1_size : accepts .rv64 nameBytes (setLE image 144 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_2_name : accepts .rv64 nameBytes (setLE image 152 4 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_2_info : accepts .rv64 nameBytes (setLE image 156 1 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_2_other : accepts .rv64 nameBytes (setLE image 157 1 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_2_shndx : accepts .rv64 nameBytes (setLE image 158 2 3) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_2_value : accepts .rv64 nameBytes (setLE image 160 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_2_size : accepts .rv64 nameBytes (setLE image 168 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_3_name : accepts .rv64 nameBytes (setLE image 176 4 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_3_info : accepts .rv64 nameBytes (setLE image 180 1 19) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_3_other : accepts .rv64 nameBytes (setLE image 181 1 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_3_shndx : accepts .rv64 nameBytes (setLE image 182 2 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_3_value : accepts .rv64 nameBytes (setLE image 184 8 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_3_size : accepts .rv64 nameBytes (setLE image 192 8 37) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_64 : accepts .rv64 nameBytes (image.set 64 ((image.getD 64 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_65 : accepts .rv64 nameBytes (image.set 65 ((image.getD 65 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_66 : accepts .rv64 nameBytes (image.set 66 ((image.getD 66 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_67 : accepts .rv64 nameBytes (image.set 67 ((image.getD 67 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_68 : accepts .rv64 nameBytes (image.set 68 ((image.getD 68 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_69 : accepts .rv64 nameBytes (image.set 69 ((image.getD 69 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_70 : accepts .rv64 nameBytes (image.set 70 ((image.getD 70 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_71 : accepts .rv64 nameBytes (image.set 71 ((image.getD 71 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_72 : accepts .rv64 nameBytes (image.set 72 ((image.getD 72 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_73 : accepts .rv64 nameBytes (image.set 73 ((image.getD 73 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_74 : accepts .rv64 nameBytes (image.set 74 ((image.getD 74 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_75 : accepts .rv64 nameBytes (image.set 75 ((image.getD 75 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_76 : accepts .rv64 nameBytes (image.set 76 ((image.getD 76 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_77 : accepts .rv64 nameBytes (image.set 77 ((image.getD 77 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_78 : accepts .rv64 nameBytes (image.set 78 ((image.getD 78 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_79 : accepts .rv64 nameBytes (image.set 79 ((image.getD 79 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_80 : accepts .rv64 nameBytes (image.set 80 ((image.getD 80 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_81 : accepts .rv64 nameBytes (image.set 81 ((image.getD 81 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_82 : accepts .rv64 nameBytes (image.set 82 ((image.getD 82 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_83 : accepts .rv64 nameBytes (image.set 83 ((image.getD 83 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_84 : accepts .rv64 nameBytes (image.set 84 ((image.getD 84 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_85 : accepts .rv64 nameBytes (image.set 85 ((image.getD 85 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_86 : accepts .rv64 nameBytes (image.set 86 ((image.getD 86 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_87 : accepts .rv64 nameBytes (image.set 87 ((image.getD 87 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_88 : accepts .rv64 nameBytes (image.set 88 ((image.getD 88 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_89 : accepts .rv64 nameBytes (image.set 89 ((image.getD 89 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_90 : accepts .rv64 nameBytes (image.set 90 ((image.getD 90 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_91 : accepts .rv64 nameBytes (image.set 91 ((image.getD 91 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_92 : accepts .rv64 nameBytes (image.set 92 ((image.getD 92 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_93 : accepts .rv64 nameBytes (image.set 93 ((image.getD 93 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_94 : accepts .rv64 nameBytes (image.set 94 ((image.getD 94 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_95 : accepts .rv64 nameBytes (image.set 95 ((image.getD 95 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_96 : accepts .rv64 nameBytes (image.set 96 ((image.getD 96 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_97 : accepts .rv64 nameBytes (image.set 97 ((image.getD 97 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_98 : accepts .rv64 nameBytes (image.set 98 ((image.getD 98 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_body_byte_99 : accepts .rv64 nameBytes (image.set 99 ((image.getD 99 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_100 : accepts .rv64 nameBytes (image.set 100 ((image.getD 100 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_101 : accepts .rv64 nameBytes (image.set 101 ((image.getD 101 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_102 : accepts .rv64 nameBytes (image.set 102 ((image.getD 102 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_103 : accepts .rv64 nameBytes (image.set 103 ((image.getD 103 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_200 : accepts .rv64 nameBytes (image.set 200 ((image.getD 200 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_201 : accepts .rv64 nameBytes (image.set 201 ((image.getD 201 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_202 : accepts .rv64 nameBytes (image.set 202 ((image.getD 202 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_203 : accepts .rv64 nameBytes (image.set 203 ((image.getD 203 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_204 : accepts .rv64 nameBytes (image.set 204 ((image.getD 204 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_205 : accepts .rv64 nameBytes (image.set 205 ((image.getD 205 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_206 : accepts .rv64 nameBytes (image.set 206 ((image.getD 206 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_207 : accepts .rv64 nameBytes (image.set 207 ((image.getD 207 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_208 : accepts .rv64 nameBytes (image.set 208 ((image.getD 208 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_209 : accepts .rv64 nameBytes (image.set 209 ((image.getD 209 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_210 : accepts .rv64 nameBytes (image.set 210 ((image.getD 210 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_211 : accepts .rv64 nameBytes (image.set 211 ((image.getD 211 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_byte_212 : accepts .rv64 nameBytes (image.set 212 ((image.getD 212 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_213 : accepts .rv64 nameBytes (image.set 213 ((image.getD 213 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_214 : accepts .rv64 nameBytes (image.set 214 ((image.getD 214 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_215 : accepts .rv64 nameBytes (image.set 215 ((image.getD 215 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_216 : accepts .rv64 nameBytes (image.set 216 ((image.getD 216 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_217 : accepts .rv64 nameBytes (image.set 217 ((image.getD 217 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_218 : accepts .rv64 nameBytes (image.set 218 ((image.getD 218 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_219 : accepts .rv64 nameBytes (image.set 219 ((image.getD 219 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_220 : accepts .rv64 nameBytes (image.set 220 ((image.getD 220 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_221 : accepts .rv64 nameBytes (image.set 221 ((image.getD 221 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_222 : accepts .rv64 nameBytes (image.set 222 ((image.getD 222 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_223 : accepts .rv64 nameBytes (image.set 223 ((image.getD 223 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_224 : accepts .rv64 nameBytes (image.set 224 ((image.getD 224 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_225 : accepts .rv64 nameBytes (image.set 225 ((image.getD 225 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_226 : accepts .rv64 nameBytes (image.set 226 ((image.getD 226 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_227 : accepts .rv64 nameBytes (image.set 227 ((image.getD 227 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_228 : accepts .rv64 nameBytes (image.set 228 ((image.getD 228 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_229 : accepts .rv64 nameBytes (image.set 229 ((image.getD 229 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_230 : accepts .rv64 nameBytes (image.set 230 ((image.getD 230 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_231 : accepts .rv64 nameBytes (image.set 231 ((image.getD 231 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_232 : accepts .rv64 nameBytes (image.set 232 ((image.getD 232 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_233 : accepts .rv64 nameBytes (image.set 233 ((image.getD 233 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_234 : accepts .rv64 nameBytes (image.set 234 ((image.getD 234 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_235 : accepts .rv64 nameBytes (image.set 235 ((image.getD 235 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_236 : accepts .rv64 nameBytes (image.set 236 ((image.getD 236 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_237 : accepts .rv64 nameBytes (image.set 237 ((image.getD 237 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_238 : accepts .rv64 nameBytes (image.set 238 ((image.getD 238 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_239 : accepts .rv64 nameBytes (image.set 239 ((image.getD 239 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_240 : accepts .rv64 nameBytes (image.set 240 ((image.getD 240 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_241 : accepts .rv64 nameBytes (image.set 241 ((image.getD 241 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_242 : accepts .rv64 nameBytes (image.set 242 ((image.getD 242 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_243 : accepts .rv64 nameBytes (image.set 243 ((image.getD 243 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_244 : accepts .rv64 nameBytes (image.set 244 ((image.getD 244 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_245 : accepts .rv64 nameBytes (image.set 245 ((image.getD 245 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_246 : accepts .rv64 nameBytes (image.set 246 ((image.getD 246 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_247 : accepts .rv64 nameBytes (image.set 247 ((image.getD 247 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_248 : accepts .rv64 nameBytes (image.set 248 ((image.getD 248 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_249 : accepts .rv64 nameBytes (image.set 249 ((image.getD 249 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_250 : accepts .rv64 nameBytes (image.set 250 ((image.getD 250 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_251 : accepts .rv64 nameBytes (image.set 251 ((image.getD 251 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_252 : accepts .rv64 nameBytes (image.set 252 ((image.getD 252 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_253 : accepts .rv64 nameBytes (image.set 253 ((image.getD 253 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_254 : accepts .rv64 nameBytes (image.set 254 ((image.getD 254 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_255 : accepts .rv64 nameBytes (image.set 255 ((image.getD 255 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_256 : accepts .rv64 nameBytes (image.set 256 ((image.getD 256 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_257 : accepts .rv64 nameBytes (image.set 257 ((image.getD 257 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_258 : accepts .rv64 nameBytes (image.set 258 ((image.getD 258 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_259 : accepts .rv64 nameBytes (image.set 259 ((image.getD 259 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_260 : accepts .rv64 nameBytes (image.set 260 ((image.getD 260 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_261 : accepts .rv64 nameBytes (image.set 261 ((image.getD 261 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_262 : accepts .rv64 nameBytes (image.set 262 ((image.getD 262 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_263 : accepts .rv64 nameBytes (image.set 263 ((image.getD 263 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_names_byte_264 : accepts .rv64 nameBytes (image.set 264 ((image.getD 264 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_265 : accepts .rv64 nameBytes (image.set 265 ((image.getD 265 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_266 : accepts .rv64 nameBytes (image.set 266 ((image.getD 266 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_267 : accepts .rv64 nameBytes (image.set 267 ((image.getD 267 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_268 : accepts .rv64 nameBytes (image.set 268 ((image.getD 268 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_269 : accepts .rv64 nameBytes (image.set 269 ((image.getD 269 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_270 : accepts .rv64 nameBytes (image.set 270 ((image.getD 270 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_padding_byte_271 : accepts .rv64 nameBytes (image.set 271 ((image.getD 271 0) ^^^ (BitVec.ofNat 8 1))) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_0 : accepts .rv64 nameBytes (image.take 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_1 : accepts .rv64 nameBytes (image.take 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_15 : accepts .rv64 nameBytes (image.take 15) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_63 : accepts .rv64 nameBytes (image.take 63) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_64 : accepts .rv64 nameBytes (image.take 64) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_99 : accepts .rv64 nameBytes (image.take 99) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_104 : accepts .rv64 nameBytes (image.take 104) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_200 : accepts .rv64 nameBytes (image.take 200) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_213 : accepts .rv64 nameBytes (image.take 213) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_272 : accepts .rv64 nameBytes (image.take 272) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_truncate_719 : accepts .rv64 nameBytes (image.take 719) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_append_zero : accepts .rv64 nameBytes (image ++ [0]) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_append_one : accepts .rv64 nameBytes (image ++ [1]) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_text_offset_overflow : accepts .rv64 nameBytes (setLE image 360 8 18446744073709551615) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_section_text_overlap_header : accepts .rv64 nameBytes (setLE image 360 8 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_function_undefined : accepts .rv64 nameBytes (setLE image 182 2 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_function_local : accepts .rv64 nameBytes (setLE image 180 1 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_function_short_prefix : accepts .rv64 nameBytes (setLE image 192 8 32) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_symbol_function_name_alias_null : accepts .rv64 nameBytes (setLE image 176 4 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_e_shoff_inside_header : accepts .rv64 nameBytes (setLE image 40 8 40) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_e_shoff_overflow : accepts .rv64 nameBytes (setLE image 40 8 18446744073709551615) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_text_offset_inside_header : accepts .rv64 nameBytes (setLE image 360 8 40) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_text_offset_overflow : accepts .rv64 nameBytes (setLE image 360 8 18446744073709551615) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_truncate_function_symbol : accepts .rv64 nameBytes (image.take 199) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_truncate_final_section : accepts .rv64 nameBytes (image.take 719) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_function_name_alias_suffix : accepts .rv64 nameBytes (setLE image 176 4 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_function_undefined : accepts .rv64 nameBytes (setLE image 182 2 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_function_in_rodata : accepts .rv64 nameBytes (setLE image 182 2 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_function_local_info2 : accepts .rv64 nameBytes (setLE image 180 1 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_function_global_object_info17 : accepts .rv64 nameBytes (setLE image 180 1 17) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
-- The symbol no longer covers the whole text section.
theorem reject_targeted_function_suffix_value4 : accepts .rv64 nameBytes (setLE (setLE image 184 8 4) 192 8 32) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_function_short_good_prefix : accepts .rv64 nameBytes (setLE image 192 8 32) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_function_extent_into_padding_or_symbols : accepts .rv64 nameBytes (setLE image 192 8 40) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_text_missing_exec : accepts .rv64 nameBytes (setLE image 344 8 2) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_symtab_wrong_string_link : accepts .rv64 nameBytes (setLE image 568 4 6) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_append_zero : accepts .rv64 nameBytes (image ++ [0]) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_append_extra_symbol_record : accepts .rv64 nameBytes (image ++ [1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0]) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_nonzero_padding_100 : accepts .rv64 nameBytes (setLE image 100 1 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_nonzero_padding_265 : accepts .rv64 nameBytes (setLE image 265 1 1) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_rv_flags4_to_rvc5 : accepts .rv64 nameBytes (setLE image 48 4 5) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_targeted_rv_flags4_to_soft0 : accepts .rv64 nameBytes (setLE image 48 4 0) (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
def targeted_rv_leaf_instead_of_framed_wrapperImage : Bytes := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,51,117,181,0,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,200,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
theorem reject_targeted_rv_leaf_instead_of_framed_wrapper : accepts .rv64 nameBytes targeted_rv_leaf_instead_of_framed_wrapperImage (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
def targeted_extra_duplicate_function_symbolImage : Bytes := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,19,1,1,250,35,48,145,0,35,52,33,1,19,137,5,0,51,117,181,0,131,52,1,0,3,57,129,0,19,1,1,6,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,120,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,224,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,237,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
-- Complete ELF with five symbols; later payload/table offsets shifted consistently.
theorem reject_targeted_extra_duplicate_function_symbol : accepts .rv64 nameBytes targeted_extra_duplicate_function_symbolImage (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
def targeted_extra_relocation_touching_bodyImage : Bytes := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,19,1,1,250,35,48,145,0,35,52,33,1,19,137,5,0,51,117,181,0,131,52,1,0,3,57,129,0,19,1,1,6,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,19,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,128,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,224,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,237,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
-- Complete ELF with one relocation into .text; later payload/table offsets shifted consistently.
theorem reject_targeted_extra_relocation_touching_body : accepts .rv64 nameBytes targeted_extra_relocation_touching_bodyImage (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
def targeted_and_object_with_or_opcodeImage : Bytes := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,19,1,1,250,35,48,145,0,35,52,33,1,19,137,5,0,51,101,181,0,131,52,1,0,3,57,129,0,19,1,1,6,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,200,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
-- Retain AND expected operation and source; body is actual corresponding OR emission.
theorem reject_targeted_and_object_with_or_opcode : accepts .rv64 nameBytes targeted_and_object_with_or_opcodeImage (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_wrong_target : accepts .arm64 nameBytes image (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_name_replay : accepts .rv64 (fromUInt8 [77,105,120,57]) image (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_embedded_nul_requested_name : accepts .rv64 (nameBytes ++ [0,120]) image (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_operation_replay : accepts .rv64 nameBytes image (RiscVFramedBitwise.functionBytes .or) = false := by decide +kernel
def leafAnd : Bytes := [51,117,181,0,103,128,0,0]
theorem reject_leaf_as_complete_object : accepts .rv64 nameBytes leafAnd (RiscVFramedBitwise.functionBytes .and) = false := by decide +kernel
theorem reject_leaf_as_expected_body : accepts .rv64 nameBytes image leafAnd = false := by decide +kernel
end riscv64_bitwise_and

namespace riscv64_bitwise_or
def source : List UInt8 := [98,105,116,119,105,115,101,58,32,40,120,58,32,117,51,50,44,32,121,58,32,117,51,50,41,58,32,117,51,50,32,61,32,120,32,124,32,121,10]
def name : List UInt8 := [98,105,116,119,105,115,101]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,19,1,1,250,35,48,145,0,35,52,33,1,19,137,5,0,51,101,181,0,131,52,1,0,3,57,129,0,19,1,1,6,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,200,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .rv64 nameBytes image (RiscVFramedBitwise.functionBytes .or) = true := by decide +kernel
end riscv64_bitwise_or

namespace riscv64_bitwise_xor
def source : List UInt8 := [98,105,116,119,105,115,101,58,32,40,120,58,32,117,51,50,44,32,121,58,32,117,51,50,41,58,32,117,51,50,32,61,32,120,32,94,32,121,10]
def name : List UInt8 := [98,105,116,119,105,115,101]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,16,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,19,1,1,250,35,48,145,0,35,52,33,1,19,137,5,0,51,69,181,0,131,52,1,0,3,57,129,0,19,1,1,6,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,98,105,116,119,105,115,101,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,200,0,0,0,0,0,0,0,13,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,213,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .rv64 nameBytes image (RiscVFramedBitwise.functionBytes .xor) = true := by decide +kernel
end riscv64_bitwise_xor

namespace riscv64_Mix9_and
def source : List UInt8 := [77,105,120,57,58,32,40,108,101,102,116,48,58,32,117,51,50,44,32,82,105,103,104,116,57,58,32,117,51,50,41,58,32,117,51,50,32,61,32,108,101,102,116,48,32,38,32,82,105,103,104,116,57,10]
def name : List UInt8 := [77,105,120,57]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,19,1,1,250,35,48,145,0,35,52,33,1,19,137,5,0,51,117,181,0,131,52,1,0,3,57,129,0,19,1,1,6,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,77,105,120,57,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,200,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,210,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .rv64 nameBytes image (RiscVFramedBitwise.functionBytes .and) = true := by decide +kernel
end riscv64_Mix9_and

namespace riscv64_Mix9_or
def source : List UInt8 := [77,105,120,57,58,32,40,108,101,102,116,48,58,32,117,51,50,44,32,82,105,103,104,116,57,58,32,117,51,50,41,58,32,117,51,50,32,61,32,108,101,102,116,48,32,124,32,82,105,103,104,116,57,10]
def name : List UInt8 := [77,105,120,57]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,19,1,1,250,35,48,145,0,35,52,33,1,19,137,5,0,51,101,181,0,131,52,1,0,3,57,129,0,19,1,1,6,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,77,105,120,57,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,200,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,210,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .rv64 nameBytes image (RiscVFramedBitwise.functionBytes .or) = true := by decide +kernel
end riscv64_Mix9_or

namespace riscv64_Mix9_xor
def source : List UInt8 := [77,105,120,57,58,32,40,108,101,102,116,48,58,32,117,51,50,44,32,82,105,103,104,116,57,58,32,117,51,50,41,58,32,117,51,50,32,61,32,108,101,102,116,48,32,94,32,82,105,103,104,116,57,10]
def name : List UInt8 := [77,105,120,57]
def object : List UInt8 := [127,69,76,70,2,1,1,0,0,0,0,0,0,0,0,0,1,0,243,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,8,1,0,0,0,0,0,0,4,0,0,0,64,0,0,0,0,0,64,0,7,0,6,0,19,1,1,250,35,48,145,0,35,52,33,1,19,137,5,0,51,69,181,0,131,52,1,0,3,57,129,0,19,1,1,6,103,128,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,18,0,1,0,0,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,111,97,107,95,77,105,120,57,0,0,46,116,101,120,116,0,46,114,111,100,97,116,97,0,46,114,101,108,97,46,116,101,120,116,0,46,115,121,109,116,97,98,0,46,115,116,114,116,97,98,0,46,115,104,115,116,114,116,97,98,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,6,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,64,0,0,0,0,0,0,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,7,0,0,0,1,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,15,0,0,0,4,0,0,0,64,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,1,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,26,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,104,0,0,0,0,0,0,0,96,0,0,0,0,0,0,0,5,0,0,0,3,0,0,0,8,0,0,0,0,0,0,0,24,0,0,0,0,0,0,0,34,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,200,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,210,0,0,0,0,0,0,0,52,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def nameBytes : Bytes := fromUInt8 name
def image : Bytes := fromUInt8 object
theorem admitted : accepts .rv64 nameBytes image (RiscVFramedBitwise.functionBytes .xor) = true := by decide +kernel
end riscv64_Mix9_xor

end Oak.NativeBitwiseObjectFixtures
