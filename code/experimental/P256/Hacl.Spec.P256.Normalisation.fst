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
 

let modp_inv2_pow (x: nat) : Tot (r: nat {r < prime}) = 
   power_distributivity x (prime - 2) prime;
   pow x (prime - 2) % prime

let _norm (p : nat * nat * nat) =
  let open FStar.Mul in 
  let (x, y, z) = p in
  let z2 = z * z in 
  let z2i = modp_inv2_pow z2 in 
  let z3 = z * z * z in 
  let z3i = modp_inv2_pow z3 in 
  let x3 = (z2i * x) % prime in 
  let y3 = (z3i * y) % prime in 
  let z3 = 1 in 
  assert(x3 == (x * (pow (z * z) (prime -2) % prime) % prime));
  assert(y3 == (y * (pow (z * z * z) (prime - 2) % prime) % prime));
  assert(z3 == 1);
  (x3, y3, z3)

open FStar.Mul

(* z * z * pow2 256 * z % prime *)
val lemma_erase_norm: z: nat-> Lemma (toDomain_ (fromDomain_ (toDomain_ (z * z % prime)) * z % prime) == toDomain_ (z * z * z % prime))

let lemma_erase_norm z = 
  lemma_mod_mul_distr_l (z * z) z prime
  
#reset-options "--z3refresh --z3rlimit 300" 

val lemma_norm_as_specification: xD: nat -> yD: nat -> zD: nat -> 
  x3 : nat {x3 == xD * (pow (zD * zD) (prime-2) % prime) % prime}-> 
  y3 : nat {y3 == yD * (pow (zD * zD * zD) (prime -2) % prime) % prime} -> 
  z3: nat{z3 == 1} -> Lemma (let (xN, yN, zN) = _norm (xD, yD, zD) in 
  x3 == xN /\ y3 == yN /\ z3 == zN)

let lemma_norm_as_specification xD yD zD x3 y3 z3 = 
  power_distributivity (zD * zD * zD) (prime - 2) prime;
  power_distributivity (zD * zD) (prime -2) prime
