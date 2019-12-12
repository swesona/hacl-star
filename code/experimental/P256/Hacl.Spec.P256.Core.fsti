module Hacl.Spec.P256.Core

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas

open FStar.Mul


(* This code is not side channel resistant *)
inline_for_extraction noextract
val eq_u64:a:uint64 -> b:uint64 -> Tot (r: bool {if uint_v a = uint_v b then r == true else r == false})

(* This code is not side channel resistant *)
inline_for_extraction noextract
val eq_0_u64: a: uint64 -> Tot (r: bool {if uint_v a = 0 then r == true else r == false})
