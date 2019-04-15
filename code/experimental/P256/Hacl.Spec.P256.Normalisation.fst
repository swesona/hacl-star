module Hacl.Spec.P256.Normalisation


open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Field64.Core
module C =  Hacl.Spec.Curve25519.Field64.Core
module D = Hacl.Spec.Curve25519.Field64.Definition
open  Hacl.Spec.P256.Core
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.MontgomeryMultiplication


open Lib.Loops
open FStar.Math.Lemmas

module B = LowStar.Buffer


let _norm p =
  let open FStar.Mul in 
  let (x, y, z) = p in
  let z2 = z * z % prime in 
  let z2i = modp_inv2 z in 
  let z3 = z * z *  z % prime in 
  let z3i = modp_inv2 z3 in 
  let x3 = (x * z2i) % prime in 
  let y3 = (y * z3i) % prime in 
  let z3 = 1 in 
  (x3, y3, z3)

open FStar.Mul

(* z * z * pow2 256 * z % prime *)
val lemma_1: z: nat-> Lemma (toDomain_ (fromDomain_ ((z * z % prime) * pow2 256 % prime) * z % prime) == toDomain_ (z * z * z % prime)) 
