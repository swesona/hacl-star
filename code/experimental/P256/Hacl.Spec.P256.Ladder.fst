module Hacl.Spec.P256.Ladder

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open Lib.Sequence
open Lib.ByteSequence


type scalar = lbytes 32

let ith_bit (k:scalar) (i:nat{i < 256}) : uint64 =
	let q = i / 8 in let r = size (i % 8) in
 	to_u64 ((index k q >>. r) &. u8 1)
