module Hacl.Spec.P256.SolinasReduction

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
module D = Hacl.Spec.Curve25519.Field64.Definition
open FStar.Mul
open Lib.Sequence

open Hacl.Spec.P256.Core


#reset-options " --z3rlimit 300"

type _uint32 = a: nat {a < pow2 32}


val c8_reduction: c8: _uint32  -> 
  Lemma((c8 * pow2 256) % prime == (c8 * pow2 (7 * 32) - c8 *  pow2 (6 * 32) - c8 *  pow2 (3 * 32) + c8) % prime)

let c8_reduction c8 = 
  assert_norm(pow2 256 % prime = pow2 224 - pow2 192 - pow2 96 + 1);
  lemma_mod_mul_distr_r c8 (pow2 256) prime;
  lemma_mod_mul_distr_r c8 (pow2 224 - pow2 192 - pow2 96 + 1) prime


val c9_reduction: c9: _uint32 -> 
  Lemma (c9 * pow2 (9 * 32) % prime == (- c9 *  pow2 (6 * 32) - c9 * pow2 (4 * 32) - c9 *  pow2 (3 * 32) + c9 * pow2 (1 * 32) + c9) % prime)

let c9_reduction c9 = 
  lemma_mod_mul_distr_r c9 (pow2 288) prime;
  assert_norm (pow2 288 % prime == (pow2 32 - pow2 192 - pow2 128 - pow2 96 + 1) % prime);
  lemma_mod_mul_distr_r c9 (pow2 32 - pow2 192 - pow2 128 - pow2 96 + 1) prime


val c10_reduction: c10: _uint32 -> Lemma (c10 * pow2 (10* 32) % prime ==  (- c10 * pow2 (7 * 32) -c10 *  pow2 (5*32) - c10 * pow2 (4 * 32) + c10 * pow2 32 + c10 * pow2 (2 * 32)) % prime)

let c10_reduction c10 = 
  lemma_mod_mul_distr_r c10 (pow2 (32 * 10)) prime;
  assert_norm (pow2 (10 * 32) % prime = (-pow2 224 - pow2 160 - pow2 128 + pow2 32 + pow2 64)% prime);
  lemma_mod_mul_distr_r c10 (-pow2 224 - pow2 160 - pow2 128 + pow2 32 + pow2 64) prime


val c11_reduction: c11: _uint32  -> Lemma (c11 * pow2 (11 * 32) % prime == (2 * c11 * pow2 (3 * 32) + c11 * pow2 (2 * 32) - c11 - c11 * pow2 (32 * 7) - c11 * pow2 (5 * 32)) % prime)

let c11_reduction c11  = 
  assert_norm((pow2 (11 * 32) % prime == (2 * pow2 96 + pow2 64 - 1 - pow2 224 - pow2 160) % prime));
  lemma_mod_mul_distr_r c11 (pow2 (11 * 32)) prime;
  lemma_mod_mul_distr_r c11 (2 * pow2 96 + pow2 64 - 1 - pow2 224 - pow2 160) prime


val c12_reduction: c12: _uint32-> Lemma (c12 * pow2 (12 * 32) % prime == (2 * c12 * pow2 (4 * 32) + 2 * c12 * pow2 (3 * 32) - c12 * pow2 32 - c12 - c12 * pow2 (7 * 32)) % prime)

let c12_reduction c12 = 
  assert_norm (pow2 (12 * 32) % prime == (2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32))% prime);
  lemma_mod_mul_distr_r c12 (pow2 (12 * 32)) prime;
  lemma_mod_mul_distr_r c12 (2 * pow2 (4 * 32) + 2 * pow2 (3 * 32) - pow2 32 - 1 - pow2 (7 * 32)) prime


val c13_reduction: c13: _uint32-> Lemma (c13 * pow2 (13 * 32) % prime == (2 * c13 * pow2 (5 * 32) + 2 * c13 * pow2 (4 * 32) + c13 * pow2 (3 * 32) + c13 *  pow2 (6 * 32) - c13 * pow2 (2 * 32) - c13 *  pow2 32 - c13 - c13 * pow2 (7 * 32)) % prime)

let c13_reduction c13 = 
  assert_norm (pow2 (13 * 32) % prime == (2 *  pow2 (5 * 32) + 2 * pow2 (4 * 32) +  pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 -  pow2 (7 * 32)) % prime);
  lemma_mod_mul_distr_r c13 (pow2 (13 * 32)) prime;
  lemma_mod_mul_distr_r c13 (2 *  pow2 (5 * 32) + 2 * pow2 (4 * 32) +  pow2 (3 * 32) + pow2 (6 * 32) - pow2 (2 * 32) - pow2 32 - 1 -  pow2 (7 * 32)) prime


val c14_reduction: c14: _uint32 -> Lemma (c14 * pow2 (14 * 32) % prime == (2 * c14 * pow2 (6 * 32) + 2 * c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c14 * pow2 (4 * 32) - c14 * pow2 (2 * 32) - c14 * pow2 32 - c14) % prime)

let c14_reduction c14 = 
  assert_norm (pow2 (14 * 32) % prime == (2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) +  pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) % prime);
  lemma_mod_mul_distr_r c14 (pow2 (14 * 32)) prime;
  lemma_mod_mul_distr_r c14 (2 * pow2 (6 * 32) + 2 * pow2 (5 * 32) +  pow2 (6 * 32) + pow2 (4 * 32) - pow2 (2 * 32) - pow2 32 - 1) prime


val c15_reduction: c15: _uint32 -> Lemma (c15 * pow2 (15 * 32) % prime == (2 * c15 * pow2 (7 * 32) + 2 * c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c15 * pow2 (5 * 32) - c15 * pow2 (3 * 32) - c15 * pow2 (2 * 32) - c15 * pow2 32)% prime)

let c15_reduction c15 = 
  assert_norm (pow2 (15 * 32) % prime ==  (2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) +pow2 (7 * 32) + pow2 (5 * 32) -  pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) % prime);
  lemma_mod_mul_distr_r c15 (pow2 (15 * 32)) prime;
  lemma_mod_mul_distr_r c15  (2 * pow2 (7 * 32) + 2 * pow2 (6 * 32) +pow2 (7 * 32) + pow2 (5 * 32) -  pow2 (3 * 32) - pow2 (2 * 32) - pow2 32) prime


val inside_mod: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> h: int -> i: int ->
  Lemma (
  (a + b + c + d + e + f + g + h + i) % prime == 
  (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime) + (i % prime)) % prime)

let inside_mod a b c d e f g h i = 
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + (g % prime) + (h % prime)) i prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + (f % prime) + h + i) g prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + (e % prime) + g + h + i) f prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime) + (d % prime) + f + g + h + i) e prime;
  lemma_mod_add_distr (a + (b % prime) + (c % prime)  + e + f + g + h + i) d prime;
  lemma_mod_add_distr (a + (b % prime) + d + e + f + g + h + i) c prime;
  lemma_mod_add_distr (a + c+ d + e + f + g + h + i) b prime


val inside_mod1: a: int -> b: int -> c: int -> d: int -> e: int -> f: int -> g: int -> h: int -> i: int ->
  Lemma (
    (a + 2 * b + 2 * c + d + e  - f - g - h - i) % prime == 
    ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - (f % prime) - (g % prime) - (h % prime) - (i % prime)) % prime)

let inside_mod1 a b c d e f g h i = 
  lemma_mod_sub_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - (f % prime) - (g % prime) - (h % prime)) i prime;
  lemma_mod_sub_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - (f % prime) - (g % prime) - i) h prime;
  lemma_mod_sub_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - (f % prime) - h - i) g prime;
  lemma_mod_sub_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) + (e % prime) - g -h - i) f prime;
  lemma_mod_add_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + (d % prime) - f - g - h - i) e prime;
  lemma_mod_add_distr ((a % prime) + 2 * (b  % prime) + 2 * (c % prime) + e - f - g - h - i) d prime;
  
  lemma_mod_add_distr ((a % prime) + 2 * (b  % prime)  + d + e - f - g - h - i) (2 * (c % prime)) prime;
  lemma_mod_mul_distr_r 2 c prime;
  lemma_mod_add_distr ((a % prime) + 2 * (b  % prime)  + d + e - f - g - h - i) (2 * c) prime;

  lemma_mod_add_distr ((a % prime) + 2 * c  + d + e - f - g - h - i) (2 * (b % prime)) prime;
  lemma_mod_mul_distr_r 2 b prime;
  lemma_mod_add_distr ((a % prime) + 2 * c  + d + e - f - g - h - i) (2 * b) prime;

  lemma_mod_add_distr (2 * b + 2 * c + d + e - f - g - h - i) a prime


val solinas_reduction_nat: 
  c0_n: _uint32-> 
  c1_n: _uint32 -> 
  c2_n: _uint32 -> 
  c3_n: _uint32 -> 
  c4_n: _uint32 -> 
  c5_n: _uint32 -> 
  c6_n: _uint32 -> 
  c7_n: _uint32 -> 
  c8_n: _uint32 -> 
  c9_n: _uint32 -> 
  c10_n: _uint32 -> 
  c11_n: _uint32 -> 
  c12_n: _uint32 -> 
  c13_n: _uint32 -> 
  c14_n: _uint32 -> 
  c15_n: _uint32->
  s0: int {s0 = c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32)} -> 
  s1: int {s1 = c11_n * pow2 (3 * 32) + c12_n * pow2 (4 * 32) + c13_n * pow2 (5 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)} ->
  s2: int {s2 = c12_n * pow2 (3 * 32) + c13_n * pow2 (4 * 32) + c14_n * pow2 (5* 32) + c15_n * pow2 (6 * 32)} -> 
  s3: int {s3 = c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)} ->
  s4: int {s4 = c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32)} -> 
  s5: int {s5 = c11_n + c12_n * pow2 32 + c13_n * pow2 (2 * 32) + c8_n * pow2 (6 * 32) + c10_n * pow2 (7 * 32)} ->
  s6: int {s6 = c12_n + c13_n * pow2 32 + c14_n * pow2 (2 * 32) + c15_n * pow2 (3 * 32) + c9_n * pow2 (6 * 32) + c11_n * pow2 (7 * 32)} ->
  s7: int {s7 = c13_n + c14_n * pow2 32 + c15_n * pow2 (2 * 32) + c8_n * pow2 (3* 32) + c9_n * pow2 (4 * 32) + c10_n * pow2 (5 * 32) + c12_n * pow2 (7 * 32)} ->
  s8: int {s8 = c14_n + c15_n * pow2 32 + c9_n * pow2 (3 * 32) + c10_n * pow2 (4* 32) + c11_n * pow2 (5 * 32) + c13_n * pow2 (7 * 32)} -> 
  n: int {n = s0 + 2 * s1 + 2 * s2 + s3 + s4 - s5 - s6 - s7 - s8} -> 
Lemma (n % prime == (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + c14_n * pow2 (14 * 32) + c15_n * pow2 (15 * 32)) % prime)



let solinas_reduction_nat c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 s0 s1 s2 s3 s4 s5 s6 s7 s8 n =
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 

  assert_by_tactic (2 * (c11 * pow2 (3 * 32) + c12 * pow2 (4 * 32) + c13 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c15 * pow2 (7 * 32)) == 2 * c11 * pow2 (3 * 32) + 2 * c12 * pow2 (4 * 32) + 2 * c13 * pow2 (5 * 32) + 2 * c14 * pow2 (6 * 32) + 2 * c15 * pow2 (7 * 32)) canon;
  assert_by_tactic (2 * (c12 * pow2 (3 * 32) + c13 * pow2 (4 * 32) + c14 * pow2 (5 * 32) + c15 * pow2 (6 * 32)) = 2 * c12 * pow2 (3 * 32) + 2 * c13 * pow2 (4 * 32) + 2 * c14 * pow2 (5* 32) + 2* c15 * pow2 (6 * 32)) canon;

  let a_ =  c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) in 
  let c8_ = c8 * pow2 (7 * 32) - c8 * pow2 (6 * 32) - c8 * pow2 (3 * 32) + c8 in 
  let c9_ = - c9 * pow2 (6 * 32) - c9 * pow2 (4 * 32) - c9 * pow2 (3 * 32) + c9 * pow2 32 + c9 in 
  let c10_ = -c10 * pow2 (7 * 32) - c10 * pow2 (5 * 32) - c10 * pow2 (4 * 32) + c10 * pow2 32 + c10 * pow2 (2 * 32) in 
  let c11_ = 2 * c11 * pow2 96 + c11 * pow2 64 - c11 - c11 * pow2 (7 * 32) - c11 * pow2 (5 * 32) in 
  let c12_ = 2 * c12 * pow2 (4 * 32) + 2 * c12 * pow2 (3 * 32) - c12 * pow2 32 - c12 - c12 * pow2 (7 * 32) in 
  let c13_ = 2 * c13 * pow2 (5 * 32) + 2 * c13 * pow2 (4 * 32) + c13 * pow2 (3 * 32) + c13 * pow2 (6 * 32) - c13 * pow2 (2 * 32) - c13 * pow2 32 - c13 - c13 * pow2 (7 * 32) in 
  let c14_ = 2 * c14 * pow2 (6 * 32) + 2 * c14 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c14 * pow2 (4 * 32) - c14 * pow2 (2 * 32) - c14 * pow2 32 - c14  in 
  let c15_ = 2 * c15 * pow2 (7 * 32) + 2 * c15 * pow2 (6 * 32) + c15 * pow2 (7 * 32) + c15 * pow2 (5 * 32) - c15 * pow2 (3 * 32) - c15 * pow2 (2 * 32) - c15 * pow2 32 in 
  
  inside_mod a_ c8_ c9_ c10_ c11_ c12_ c13_ c14_ c15_;
  c8_reduction c8;
  c9_reduction c9;
  c10_reduction c10;
  c11_reduction c11;
  c12_reduction c12;
  c13_reduction c13;
  c14_reduction c14;
  c15_reduction c15;

  inside_mod a_ (c8 * pow2 (8 * 32)) (c9 * pow2 (9 * 32)) (c10 * pow2 (10 * 32)) (c11 * pow2 (11 * 32)) (c12 * pow2 (12 * 32)) (c13 * pow2 (13 * 32)) (c14 * pow2 (14 * 32)) (c15 * pow2 (15 * 32))

val solinas_reduction_mod: 
  c0_n: _uint32-> 
  c1_n: _uint32 -> 
  c2_n: _uint32 -> 
  c3_n: _uint32 -> 
  c4_n: _uint32 -> 
  c5_n: _uint32 -> 
  c6_n: _uint32 -> 
  c7_n: _uint32 -> 
  c8_n: _uint32 -> 
  c9_n: _uint32 -> 
  c10_n: _uint32 -> 
  c11_n: _uint32 -> 
  c12_n: _uint32 -> 
  c13_n: _uint32 -> 
  c14_n: _uint32 -> 
  c15_n: _uint32->
  s0: int {s0 = (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32)) % prime} -> 
  s1: int {s1 = (c11_n * pow2 (3 * 32) + c12_n * pow2 (4 * 32) + c13_n * pow2 (5 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)) % prime} ->
  s2: int {s2 = (c12_n * pow2 (3 * 32) + c13_n * pow2 (4 * 32) + c14_n * pow2 (5* 32) + c15_n * pow2 (6 * 32)) % prime} -> 
  s3: int {s3 = (c8_n + c9_n * pow2 32 + c10_n * pow2 (2 * 32) + c14_n * pow2 (6 * 32) + c15_n * pow2 (7 * 32)) % prime} ->
  s4: int {s4 = (c9_n + c10_n * pow2 32 + c11_n * pow2 (2 * 32) + c13_n * pow2 (3 * 32) + c14_n * pow2 (4 * 32) + c15_n * pow2 (5 * 32) + c13_n * pow2 (6 * 32) + c8_n * pow2 (7 * 32)) % prime} -> 
  s5: int {s5 = (c11_n + c12_n * pow2 32 + c13_n * pow2 (2 * 32) + c8_n * pow2 (6 * 32) + c10_n * pow2 (7 * 32)) % prime} ->
  s6: int {s6 = (c12_n + c13_n * pow2 32 + c14_n * pow2 (2 * 32) + c15_n * pow2 (3 * 32) + c9_n * pow2 (6 * 32) + c11_n * pow2 (7 * 32)) % prime} ->
  s7: int {s7 = (c13_n + c14_n * pow2 32 + c15_n * pow2 (2 * 32) + c8_n * pow2 (3* 32) + c9_n * pow2 (4 * 32) + c10_n * pow2 (5 * 32) + c12_n * pow2 (7 * 32)) % prime} ->
  s8: int {s8 = (c14_n + c15_n * pow2 32 + c9_n * pow2 (3 * 32) + c10_n * pow2 (4* 32) + c11_n * pow2 (5 * 32) + c13_n * pow2 (7 * 32)) % prime} -> 
  n: int {n = (s0 + 2 * s1 + 2 * s2 + s3 + s4 - s5 - s6 - s7 - s8) % prime} -> 
Lemma (n % prime == (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + c14_n * pow2 (14 * 32) + c15_n * pow2 (15 * 32)) % prime)

#reset-options "--z3refresh --z3rlimit 100"

(* slightly suspicious lemma *)
let solinas_reduction_mod c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 s0 s1 s2 s3 s4 s5 s6 s7 s8 n  = 
    assert(n =  (s0 + 2 * s1 + 2 * s2 + s3 + s4 - s5 - s6 - s7 - s8) % prime);
  let s0_ = c0 + c1 * pow2 32 + c2 * pow2 (2 * 32) + c3 * pow2 (3 * 32) + c4 * pow2 (4 * 32) + c5 * pow2 (5 * 32) + c6 * pow2 (6 * 32) + c7 * pow2 (7 * 32) in 
  let s1_ = c11 * pow2 (3 * 32) + c12 * pow2 (4 * 32) + c13 * pow2 (5 * 32) + c14 * pow2 (6 * 32) + c15 * pow2 (7 * 32) in 
  let s2_ = c12 * pow2 (3 * 32) + c13 * pow2 (4 * 32) + c14 * pow2 (5* 32) + c15 * pow2 (6 * 32) in
  let s3_ = c8 + c9 * pow2 32 + c10 * pow2 (2 * 32) + c14 * pow2 (6 * 32) + c15 * pow2 (7 * 32) in 
  let s4_ = c9 + c10 * pow2 32 + c11 * pow2 (2 * 32) + c13 * pow2 (3 * 32) + c14 * pow2 (4 * 32) + c15 * pow2 (5 * 32) + c13 * pow2 (6 * 32) + c8 * pow2 (7 * 32) in 
  let s5_ = c11 + c12 * pow2 32 + c13 * pow2 (2 * 32) + c8 * pow2 (6 * 32) + c10 * pow2 (7 * 32) in 
    assert(- (s5_ % prime) = - s5);   
  let s6_ = c12 + c13 * pow2 32 + c14 * pow2 (2 * 32) + c15 * pow2 (3 * 32) + c9 * pow2 (6 * 32) + c11 * pow2 (7 * 32) in 
    assert(- (s6_ % prime) = - s6); 
  let s7_ = c13 + c14 * pow2 32 + c15 * pow2 (2 * 32) + c8 * pow2 (3 * 32) + c9 * pow2 (4 * 32) + c10 * pow2 (5 * 32) + c12 * pow2 (7 * 32) in 
  let s8_ = c14 + c15 * pow2 32 + c9 * pow2 (3 * 32) + c10 * pow2 (4* 32) + c11 * pow2 (5 * 32) + c13 * pow2 (7 * 32) in 
  let n_ = s0_ + 2 * s1_ + 2 * s2_ + s3_ + s4_ - s5_ - s6_ - s7_ - s8_ in
  solinas_reduction_nat c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 s0_ s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_ n_;
  inside_mod1 s0_  s1_ s2_ s3_ s4_ s5_ s6_ s7_ s8_


inline_for_extraction noextract
val fast_reduction_upload_zero_buffer: input: felem8_32 -> Tot (r: felem4
{
   let (c0, c1, c2, c3, c4, c5, c6, c7) = input in 
   let (r0, r1, r2, r3) = r in 
   D.as_nat4 r == uint_v c0 + uint_v c1 * pow2 (1 * 32) + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + uint_v c4 * pow2 (4 * 32) + uint_v c5 * pow2 (5 * 32) + uint_v  c6 * pow2 (6 * 32) + uint_v c7 * pow2 (7 * 32)})

let fast_reduction_upload_zero_buffer (c0, c1, c2, c3, c4, c5, c6, c7)  = 
  (* let (c0, c1, c2, c3, c4, c5, c6, c7) = input in    *)
  let b0 = store_high_low_u c1 c0 in 
  let b1 = store_high_low_u c3 c2 in 
  let b2 = store_high_low_u c5 c4 in 
  let b3 = store_high_low_u c7 c6 in 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  (b0, b1, b2, b3)


inline_for_extraction noextract
val fast_reduction_upload_first_buffer: input: felem8_32 -> Tot (r: felem4 
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r == (uint_v c11 * pow2 (3 * 32) + uint_v c12 * pow2 (4 * 32) + uint_v c13 * pow2 (5 * 32) + uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime})

let fast_reduction_upload_first_buffer (c8, c9, c10, c11, c12, c13, c14, c15) = 
  (* let (c8, c9, c10, c11, c12, c13, c14, c15) = input in  *)
  let b0 = u64(0) in 
  let b1 = store_high_low_u c11 (u32 0) in 
  let b2 = store_high_low_u c13 c12 in 
  let b3 = store_high_low_u c15 c14 in 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  reduction_prime_2prime (b0, b1, b2, b3)
  

inline_for_extraction noextract
val fast_reduction_upload_second_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = (uint_v c12 * pow2 (3 * 32) + uint_v c13 * pow2 (4 * 32) + uint_v c14 * pow2 (5* 32) + uint_v c15 * pow2 (6 * 32)) % prime})

let fast_reduction_upload_second_buffer (c8, c9, c10, c11, c12, c13, c14, c15) = 
    (* let (c8, c9, c10, c11, c12, c13, c14, c15) = input in  *)
    let b0 = u64 (0) in 
    let b1 = store_high_low_u c12 (u32 0) in 
    let b2 = store_high_low_u c14 c13 in 
    let b3 = store_high_low_u (u32 0) c15 in 
      assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
      assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
      assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
      assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
    (b0, b1, b2, b3)

inline_for_extraction noextract
val fast_reduction_upload_third_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c8 + uint_v c9 * pow2 32 + uint_v c10 * pow2 (2 * 32) + uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)
  })

let fast_reduction_upload_third_buffer (c8, c9, c10, c11, c12, c13, c14, c15) = 
   (* let (c8, c9, c10, c11, c12, c13, c14, c15) = input in  *)
   let b0 = store_high_low_u c9 c8 in 
   let b1 = store_high_low_u (u32 0) c10 in 
   let b2 = u64 0 in 
   let b3 = store_high_low_u c15 c14 in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
   (b0, b1, b2, b3)

inline_for_extraction noextract
val fast_reduction_upload_forth_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c9 + uint_v c10 * pow2 32 + uint_v c11 * pow2 (2 * 32) + uint_v c13 * pow2 (3 * 32) + uint_v c14 * pow2 (4 * 32) + uint_v c15 * pow2 (5 * 32) + uint_v c13 * pow2 (6 * 32) + uint_v c8 * pow2 (7 * 32)})

let fast_reduction_upload_forth_buffer (c8, c9, c10, c11, c12, c13, c14, c15) = 
    (* let (c8, c9, c10, c11, c12, c13, c14, c15) = input in  *)
    let b0 = store_high_low_u c10 c9 in 
    let b1 = store_high_low_u c13 c11 in 
    let b2 = store_high_low_u c15 c14 in 
    let b3 = store_high_low_u c8 c13 in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    (b0, b1, b2, b3)

inline_for_extraction noextract
val fast_reduction_upload_fifth_buffer: input: felem8_32 -> Tot (r: felem4 
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c11 + uint_v c12 * pow2 32 + uint_v c13 * pow2 (2 * 32) + uint_v c8 * pow2 (6 * 32) + uint_v c10 * pow2 (7 * 32)})

let fast_reduction_upload_fifth_buffer (c8, c9, c10, c11, c12, c13, c14, c15) = 
    (* let (c8, c9, c10, c11, c12, c13, c14, c15) = input in  *)
    let b0 = store_high_low_u c12 c11 in 
    let b1 = store_high_low_u (u32 0) c13 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c10 c8 in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    (b0, b1, b2, b3)

inline_for_extraction noextract
val fast_reduction_upload_sixth_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c12 + uint_v c13 * pow2 32 + uint_v c14 * pow2 (2 * 32) + uint_v c15 * pow2 (3 * 32) + 
      uint_v c9 * pow2 (6 * 32) + uint_v c11 * pow2 (7 * 32)})

let fast_reduction_upload_sixth_buffer (c8, c9, c10, c11, c12, c13, c14, c15) = 
    (* let (c8, c9, c10, c11, c12, c13, c14, c15) = input in  *)
    let b0 = store_high_low_u c13 c12 in 
    let b1 = store_high_low_u c15 c14 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c11 c9 in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
   (b0, b1, b2, b3)

inline_for_extraction noextract
val fast_reduction_upload_seventh_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c13 + uint_v c14 * pow2 32 + uint_v c15 * pow2 (2 * 32) + uint_v c8 * pow2 (3* 32) +  uint_v c9 * pow2 (4 * 32) + uint_v c10 * pow2 (5 * 32) + uint_v c12 * pow2 (7 * 32)})


let fast_reduction_upload_seventh_buffer (c8, c9, c10, c11, c12, c13, c14, c15) = 
    (* let (c8, c9, c10, c11, c12, c13, c14, c15) = input in  *)
    let b0 = store_high_low_u c14 c13 in 
    let b1 = store_high_low_u c8 c15 in 
    let b2 = store_high_low_u c10 c9 in 
    let b3 = store_high_low_u c12 (u32 0) in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    (b0, b1, b2, b3)

inline_for_extraction noextract
val fast_reduction_upload_eighth_buffer: input: felem8_32 -> Tot (r: felem4
{
  let (c8, c9, c10, c11, c12, c13, c14, c15) = input in 
  let (r0, r1, r2, r3) = r in 
  D.as_nat4 r = uint_v c14 + uint_v c15 * pow2 32 + uint_v c9 * pow2 (3 * 32) + uint_v c10 * pow2 (4* 32) + uint_v c11 * pow2 (5 * 32) + uint_v c13 * pow2 (7 * 32)})


let fast_reduction_upload_eighth_buffer (c8, c9, c10, c11, c12, c13, c14, c15) = 
    (* let (c8, c9, c10, c11, c12, c13, c14, c15) = input in  *)
    let b0 = store_high_low_u c15 c14 in 
    let b1 = store_high_low_u c9 (u32 0) in 
    let b2 = store_high_low_u c11 c10 in 
    let b3 = store_high_low_u c13 (u32 0) in 
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));    
    (b0, b1, b2, b3)

#reset-options " --z3rlimit 300 --z3refresh"

val reduce_brackets: r0: nat -> r1: nat -> r2: nat -> r3: nat -> r4: nat -> r5: nat -> r6: nat -> r7: nat -> r8: nat ->  
  Lemma (
    (((((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) % prime - r7) % prime - r8) % prime == 
    (r0 + 2 * r1 + 2 * r2 + r3 + r4 - r5  - r6 - r7 - r8) % prime)

let reduce_brackets r0 r1 r2 r3 r4 r5 r6 r7 r8  =
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let n = (((((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) % prime - r7) % prime - r8) % prime in 
  lemma_mod_add_distr (- r8) ((((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) % prime - r7) prime;
  lemma_mod_add_distr (-r7 - r8) (((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) % prime - r6) prime;
  lemma_mod_add_distr (-r6 - r7 - r8)  ((((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) % prime - r5) prime;
  lemma_mod_add_distr (-r5 -r6 - r7 - r8)  (((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) % prime + r4) prime;
  lemma_mod_add_distr (r4 -r5 -r6 - r7 - r8)  ((((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) + r3) prime;
  lemma_mod_add_distr (r3 + r4 - r5 - r6 - r7 - r8) (((r0 + (2 * r1 % prime)) % prime +  (2 * r2 % prime)) % prime) prime;

  let t0 = r3 + r4 - r5 - r6 - r7 - r8 in 
  let l0 = (r0 + (2 * r1 % prime)) % prime in 
  
  assert(n == (l0 + (2 * r2 % prime) + t0) % prime);
  assert_by_tactic ((l0 + (2 * r2 % prime) + t0) == ((l0 + t0) + (2 * r2 % prime))) canon;
  lemma_mod_add_distr (l0 + t0) (2 * r2 % prime) prime;
  lemma_mod_mul_distr_r 2 r2 prime;
  lemma_mod_add_distr (l0 + t0) (2 * r2) prime;
  let t1 = 2 * r2 + r3 + r4 - r5 - r6 - r7 - r8  in 
  let l1 = r0 + (2 * r1 % prime) in  
  lemma_mod_add_distr t1 l1 prime;
  lemma_mod_add_distr (r0 + t1) (2 * r1 % prime) prime;
  lemma_mod_mul_distr_r 2 r1 prime;
  lemma_mod_add_distr (r0 + t1) (2 * r1) prime

#reset-options " --z3rlimit 200 --z3refresh"


let solinas_reduction (f0, f1, f2, f3, f4, f5, f6, f7) = 
    assert_norm (pow2 64 * pow2 64 = pow2 (2 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 (3 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (4 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64  = pow2 (6 * 64));
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64));

    assert(D.wide_as_nat4 (f0, f1, f2, f3, f4, f5, f6, f7) = uint_v f0 + uint_v f1 * pow2 64 + uint_v f2 * pow2 (2 * 64) + uint_v f3 * pow2 (3 * 64) + uint_v f4 * pow2 (4 * 64) + uint_v  f5 * pow2 (5 * 64) + uint_v f6*pow2 (6 * 64) + uint_v f7 * pow2 (7 * 64)); 

  let c0 = get_low_part f0 in 
  [@inline_let]
    let c0_n = uint_v c0 in 
  let c1 = get_high_part f0 in 
  [@inline_let]
    let c1_n = uint_v c1 in 
  let c2 = get_low_part f1 in
  [@inline_let]
    let c2_n = uint_v c2 in 
  let c3 = get_high_part f1 in
  [@inline_let]
    let c3_n = uint_v c3 in 
  let c4 = get_low_part f2 in
  [@inline_let]
    let c4_n = uint_v c4 in 
  let c5 = get_high_part f2 in
  [@inline_let]
    let c5_n = uint_v c5 in 
  let c6 = get_low_part f3 in
  [@inline_let]
    let c6_n = uint_v c6 in 
  let c7 = get_high_part f3 in
  [@inline_let]
    let c7_n = uint_v c7 in 
  let c8 = get_low_part f4 in 
  [@inline_let]
    let c8_n = uint_v c8 in 
  let c9 = get_high_part f4 in
  [@inline_let]
    let c9_n = uint_v c9 in
  let c10 = get_low_part f5 in   
  [@inline_let]
    let c10_n = uint_v c10 in 
  let c11 = get_high_part f5 in
  [@inline_let]
    let c11_n = uint_v c11 in 
  let c12 = get_low_part f6 in 
  [@inline_let]
    let c12_n = uint_v c12 in 
  let c13 = get_high_part f6 in
  [@inline_let]
    let c13_n = uint_v c13 in 
  let c14 = get_low_part  f7 in
  [@inline_let]
    let c14_n = uint_v c14 in 
  let c15 = get_high_part f7 in
  [@inline_let]
    let c15_n = uint_v c15 in

  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  assert_norm (pow2 (6 * 32) * pow2 (2 * 32) = pow2 (8 * 32));
  assert_norm (pow2 (7 * 32) * pow2 (2 * 32) = pow2 (9 * 32));
  assert_norm (pow2 (8 * 32) * pow2 (2 * 32) = pow2 (10 * 32));
  assert_norm (pow2 (9 * 32) * pow2 (2 * 32) = pow2 (11 * 32));
  assert_norm (pow2 (10 * 32) * pow2 (2 * 32) = pow2 (12 * 32));
  assert_norm (pow2 (11 * 32) * pow2 (2 * 32) = pow2 (13 * 32));
  assert_norm (pow2 (12 * 32) * pow2 (2 * 32) = pow2 (14 * 32));
  assert_norm (pow2 (13 * 32) * pow2 (2 * 32) = pow2 (15 * 32)); 

  assert(D.wide_as_nat4 (f0, f1, f2, f3, f4, f5, f6, f7) =  (c0_n + c1_n * pow2 32 + c2_n * pow2 (2 * 32) + c3_n * pow2 (3 * 32) + c4_n * pow2 (4 * 32) + c5_n * pow2 (5 * 32) + c6_n * pow2 (6 * 32) + c7_n * pow2 (7 * 32) + c8_n * pow2 256 + c9_n * pow2 288 + c10_n * pow2 (10 * 32)  + c11_n * pow2 (11 * 32) + c12_n * pow2 (12 * 32) + c13_n* pow2 (13 * 32) + c14_n * pow2 (14 * 32) + c15_n * pow2 (15 * 32)));

  (* let c_low = (c0, c1, c2, c3, c4, c5, c6, c7) in  *)
  (* let c_high = (c8, c9, c10, c11, c12, c13, c14, c15) in  *)

  let (state0_0, state0_1, state0_2, state0_3) = fast_reduction_upload_zero_buffer  (c0, c1, c2, c3, c4, c5, c6, c7) in 
    let (state0_red_0, state0_red_1, state0_red_2, state0_red_3) = reduction_prime_2prime (state0_0, state0_1, state0_2, state0_3) in 
  let state1 = fast_reduction_upload_first_buffer (c8, c9, c10, c11, c12, c13, c14, c15) in 
  let state2 = fast_reduction_upload_second_buffer (c8, c9, c10, c11, c12, c13, c14, c15) in 
  let state3 = fast_reduction_upload_third_buffer (c8, c9, c10, c11, c12, c13, c14, c15) in 
      let state3_red = reduction_prime_2prime state3 in 
  let state4 = fast_reduction_upload_forth_buffer (c8, c9, c10, c11, c12, c13, c14, c15) in 
      let state4_red = reduction_prime_2prime state4 in 
  let state5 = fast_reduction_upload_fifth_buffer (c8, c9, c10, c11, c12, c13, c14, c15) in
      let state5_red = reduction_prime_2prime state5 in     
  let state6 = fast_reduction_upload_sixth_buffer (c8, c9, c10, c11, c12, c13, c14, c15) in 
    let state6_red = reduction_prime_2prime state6 in 
  let state7 = fast_reduction_upload_seventh_buffer (c8, c9, c10, c11, c12, c13, c14, c15) in 
      let state7_red = reduction_prime_2prime state7 in 
  let state8 = fast_reduction_upload_eighth_buffer (c8, c9, c10, c11, c12, c13, c14, c15) in 
      let state8_red = reduction_prime_2prime state8 in 

  let state1_2 = shift_left_felem state1 in 
  let state2_2 = shift_left_felem state2 in 
  let r0 = felem_add (state0_red_0, state0_red_1, state0_red_2, state0_red_3)  state1_2 in 
  let r1 = felem_add r0 state2_2 in 
  let r0 = felem_add r1 state3_red in 
  let r1 = felem_add r0 state4_red in 
  let r0 = felem_sub r1 state5_red in 
  let r1 = felem_sub r0 state6_red in 
  let r0 = felem_sub r1 state7_red in 
  let result = felem_sub r0 state8_red in 
    modulo_lemma (D.as_nat4 result) prime;

  reduce_brackets (D.as_nat4 (state0_red_0, state0_red_1, state0_red_2, state0_red_3) ) (D.as_nat4 state1) (D.as_nat4 state2) (D.as_nat4 state3_red) (D.as_nat4 state4_red) (D.as_nat4 state5_red) (D.as_nat4 state6_red) (D.as_nat4 state7_red) (D.as_nat4 state8_red);

  solinas_reduction_mod c0_n c1_n c2_n c3_n c4_n c5_n c6_n c7_n c8_n c9_n c10_n c11_n c12_n c13_n c14_n c15_n 
    (D.as_nat4 (state0_red_0, state0_red_1, state0_red_2, state0_red_3) ) (D.as_nat4 state1) (D.as_nat4 state2) (D.as_nat4 state3_red) 
    (D.as_nat4 state4_red) (D.as_nat4 state5_red) (D.as_nat4 state6_red) (D.as_nat4 state7_red)
    (D.as_nat4  state8_red) (D.as_nat4 result);

 result

