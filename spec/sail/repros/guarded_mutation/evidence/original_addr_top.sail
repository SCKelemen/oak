/**************************************************************************/
/* BSD 3-clause Clear License                                             */
/*                                                                        */
/* Copyright (c) 2019                                                     */
/*   Arm Limited (or its affiliates),                                     */
/*   Alasdair Armstrong,                                                  */
/*   Alastair Reid,                                                       */
/*   Thomas Bauereiss,                                                    */
/*   Peter Sewell,                                                        */
/*   Kathryn Gray,                                                        */
/*   Anthony Fox                                                          */
/*                                                                        */
/* All rights reserved.                                                   */
/*                                                                        */
/* Redistribution and use in source and binary forms, with or without     */
/* modification, are permitted (subject to the limitations in the         */
/* disclaimer below) provided that the following conditions are met:      */
/*                                                                        */
/* 	* Redistributions of source code must retain the above            */
/*        copyright notice, this list of conditions and the following     */
/* 	  disclaimer.                                                     */
/*      * Redistributions in binary form must reproduce the above         */
/*        copyright notice, this list of conditions and the following     */
/*        disclaimer in the documentation and/or other materials          */
/* 	  provided with the distribution.                                 */
/* 	* Neither the name of ARM Limited nor the names of its            */
/*        contributors may be used to endorse or promote products         */
/*        derived from this software without specific prior written       */
/*        permission.                                                     */
/*                                                                        */
/* NO EXPRESS OR IMPLIED LICENSES TO ANY PARTY'S PATENT RIGHTS ARE        */
/* GRANTED BY THIS LICENSE. THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT    */
/* HOLDERS AND CONTRIBUTORS "AS IS" AND ANY EXPRESS OR IMPLIED            */
/* WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF   */
/* MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE               */
/* DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE  */
/* LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR    */
/* CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF   */
/* SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR        */
/* BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,  */
/* WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE   */
/* OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN */
/* IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.                          */
/**************************************************************************/

default Order dec
$include <flow.sail>
$include <vector.sail>
$include <arith.sail>
$include <string.sail>
overload ~ = {not_bool, not_vec}
register TCR_EL1 : bits(64)

register TCR_EL2 : bits(64)

register TCR_EL3 : bits(32)

let EL1 : bits(2) = 0b01

let EL2 : bits(2) = 0b10

let EL3 : bits(2) = 0b11

val HaveEL : bits(2) -> bool
function HaveEL(el) = true
val S1TranslationRegime : bits(2) -> bits(2)
function S1TranslationRegime(el) = 0b01
val ELUsingAArch32 : bits(2) -> bool
function ELUsingAArch32(el) = false
val HavePACExt : unit -> bool
function HavePACExt() = false
val HaveVirtHostExt : unit -> bool
function HaveVirtHostExt() = false
val ELIsInHost : bits(2) -> bool
function ELIsInHost(el) = false
val AddrTop : forall ('IsInstr : Bool).
  (bits(64), bool('IsInstr), bits(2)) -> int effect {escape, rreg, undef}

function AddrTop (address, IsInstr, el) = {
    assert(HaveEL(el));
    let regime = S1TranslationRegime(el);
    tbi : bits(1) = undefined : bits(1);
    tbid : bits(1) = undefined : bits(1);
    if ELUsingAArch32(regime) then {
        return(31)
    } else {
        match regime {
          ? if ? == EL1 => {
              tbi = if [address[55]] == 0b1 then [TCR_EL1[38]] else [TCR_EL1[37]];
              if HavePACExt() then {
                  tbid = if [address[55]] == 0b1 then [TCR_EL1[52]] else [TCR_EL1[51]]
              }
          },
          ? if ? == EL2 => {
              if HaveVirtHostExt() & ELIsInHost(el) then {
                  tbi = if [address[55]] == 0b1 then [TCR_EL2[38]] else [TCR_EL2[37]];
                  if HavePACExt() then {
                      tbid = if [address[55]] == 0b1 then [TCR_EL2[52]] else [TCR_EL2[51]]
                  }
              } else {
                  tbi = [TCR_EL2[20]];
                  if HavePACExt() then {
                      tbid = [TCR_EL2[29]]
                  }
              }
          },
          ? if ? == EL3 => {
              tbi = [TCR_EL3[20]];
              if HavePACExt() then {
                  tbid = [TCR_EL3[29]]
              }
          }
        }
    };
    if tbi == 0b1 & ((~(HavePACExt()) | tbid == 0b0) | ~(IsInstr)) then 55 else 63
}

val observe : bits(64) -> int
function observe(tcr) = {
 TCR_EL1 = tcr;
 AddrTop(0x0000000000000000, true, 0b01)
}
val main : unit -> unit
function main() = {
 print_int("TBI0=0 -> ", observe(0x0000000000000000));
 print_int("TBI0=1 -> ", observe(0x0000002000000000))
}
