module Hacl.Spec.P256.Core

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas

open FStar.Mul

#set-options "--z3rlimit 300"

(* This code is used only for proving, so the code is NOT side channel resistant *)
let eq_u64 a b =
  let open Lib.RawIntTypes in
  FStar.UInt64.(u64_to_UInt64 a =^ u64_to_UInt64 b)

let eq_0_u64 a = eq_u64 a (u64 0)

