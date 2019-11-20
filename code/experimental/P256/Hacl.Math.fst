module Hacl.Math

open FStar.Math.Lemmas
open FStar.Math
open FStar.Mul

open Hacl.Spec.P256.Lemmas

noextract
let prime256:pos =
  assert_norm (pow2 256 - pow2 224 + pow2 192 + pow2 96 -1 > 0);
  pow2 256 - pow2 224 + pow2 192 + pow2 96 -1

assume val lemma_montgomery_mod_inverse_addition: a: nat -> 
  Lemma (
    (a * modp_inv2_prime(pow2 64) prime256  * modp_inv2_prime (pow2 64) prime256) % prime256 == (a * modp_inv2_prime(pow2 128) prime256) % prime256)

assume val lemma_montgomery_mod_inverse_addition2: a: nat -> 
  Lemma (
    (a * modp_inv2_prime (pow2 128) prime256  * modp_inv2_prime (pow2 128) prime256) % prime256 == (a * modp_inv2_prime(pow2 256) prime256) % prime256)
