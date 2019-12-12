module Hacl.Spec.P256.Core

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Basic

open FStar.Mul

#set-options "--z3rlimit 300"

(* This code is used only for proving, so the code is NOT side channel resistant *)
inline_for_extraction noextract
val gt: a: uint64 -> b: uint64 -> Tot uint64

let gt a b = 
  let open Lib.RawIntTypes in
  if FStar.UInt64.(u64_to_UInt64 b <^ u64_to_UInt64 a) then u64 1 else u64 0

let eq_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

let eq_0_u64 a = eq_u64 a (u64 0)

