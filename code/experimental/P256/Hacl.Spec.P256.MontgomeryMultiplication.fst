module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Core

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence
open Lib.Loops

#reset-options "--z3rlimit 300"

let prime = prime256

let fromDomain_ a = (a * modp_inv2 (pow2 256)) % prime256

let fromDomainPoint a = 
  let x, y, z = a in 
  fromDomain_ x, fromDomain_ y, fromDomain_ z


val fromDomain: a: felem4{as_nat4 a < prime256} -> Tot (result: felem4 {as_nat4 result = fromDomain_ (as_nat4 a)})

let fromDomain a =  
  let one = ((u64 1), (u64 0), u64 0, u64 0) in
    assert_norm (as_nat4 one = 1);
  Core.montgomery_multiplication one a


let toDomain_ a = (a * pow2 256) % prime256

let lemmaFromDomain a = ()

let lemmaToDomain a = ()


#reset-options "--z3rlimit 300 --z3refresh"

let lemmaToDomainAndBackIsTheSame a = 
  let to = toDomain_ a in 
    lemmaToDomain a;
  let from = fromDomain_ to in 
    lemmaFromDomain to;
    lemma_mod_mul_distr_l (a * pow2 256) (modp_inv2 (pow2 256)) prime256;
    assert(from = (a * pow2 256 * modp_inv2 (pow2 256)) % prime256);
    assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime256 = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 (pow2 256)) prime256;
    assert((a * pow2 256 * modp_inv2 (pow2 256)) % prime256 == (a * (pow2 256 * modp_inv2 (pow2 256) % prime)) % prime256);
    modulo_lemma a prime;
    assert(from = a)


let lemmaFromDomainToDomain a = 
  let from = fromDomain_ a in 
    lemmaFromDomain a;
  let to = toDomain_ from in 
    lemmaToDomain from;
  lemma_mod_mul_distr_l (a * modp_inv2 (pow2 256)) (pow2 256)  prime256;
  assert_norm (modp_inv2 (pow2 256) * (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (modp_inv2 (pow2 256)) (pow2 256) prime256;
  modulo_lemma a prime


let lemmaFromDomainToDomainModuloPrime a = 
  lemma_mod_mul_distr_l (a*pow2 256) (modp_inv2 (pow2 256)) prime256;
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime256 = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 (pow2 256)) prime256

(* it is the key lemma of Montgomery Multiplication, showing that it's correct (i.e. mm(a, b) = a * b * 2^-256 *)
(*
val lemmaMontgomeryMultiplicationCorrect: a: felem4{as_nat4 a < prime} -> b: felem4{as_nat4 b < prime} -> Lemma (
  let aDomain = toDomain_ a in 
  let bDomain = toDomain b in 
  let multInDomain = Core.montgomery_multiplication aDomain bDomain in 
  let multResultFromDomain = fromDomain multInDomain in 
  as_nat4 a * as_nat4 b % prime == as_nat4 multResultFromDomain)


let lemmaMontgomeryMultiplicationCorrect a b = 
  let aDomain = toDomain a in 
  let bDomain = toDomain b in 
  let multInDomain = montgomery_multiplication aDomain bDomain in 
  assert_norm (prime > 0);
  modulo_distributivity_mult2 (as_nat4 a * pow2 256) (as_nat4 b * pow2 256) (modp_inv2 (pow2 256)) prime;  
  lemma_brackets_l (as_nat4 a * pow2 256) ((as_nat4 b * pow2 256) * modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
  lemma_twice_brackets (as_nat4 a) (pow2 256) 1 (as_nat4 b) (pow2 256) 1 (modp_inv2 (pow2 256));
  modulo_distributivity_mult2 (as_nat4 a * pow2 256) (as_nat4 b * pow2 256) (modp_inv2 (pow2 256)) prime;
  modulo_distributivity_mult_last_two (as_nat4 a) (pow2 256) (as_nat4 b) (pow2 256) (modp_inv2 (pow2 256)) prime;
  assert_norm((pow2 256 * modp_inv2 (pow2 256)) % prime = 1);
  lemma_distr_mult3 (as_nat4 a) (pow2 256) (as_nat4 b);
  let multFromDomain = fromDomain multInDomain in 
  lemma_mod_mul_distr_l (as_nat4 a * as_nat4 b *pow2 256) (modp_inv2 (pow2 256)) prime;
  modulo_distributivity_mult_last_two (as_nat4 a) (as_nat4 b) 1 (pow2 256) (modp_inv2 (pow2 256)) prime
*)


let inDomain_mod_is_not_mod a = 
  lemma_mod_mul_distr_l a (pow2 256) prime256


(* the lemma shows that the result of multiplication moved out of domain is the multiplication of the numbers moved out of domain *)
val multiplicationInDomain: #k: nat -> #l: nat -> 
  a: felem4 {as_nat4 a == toDomain_ (k) /\ as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b == toDomain_ (l) /\ as_nat4 b < prime256} -> Lemma 
    (ensures (let multResult = Core.montgomery_multiplication a b in as_nat4 multResult == toDomain_ (k * l)))
    
let multiplicationInDomain #k #l a b = 
  let multResult = Core.montgomery_multiplication a b in 
  lemma_mul_nat2 k l;
  let secondBracket = toDomain_ (k * l) in 
    assert(as_nat4 multResult = toDomain_ (k) * toDomain_ (l) * modp_inv2 (pow2 256) % prime);
  modulo_distributivity_mult2 (k * pow2 256) (l* pow2 256) (modp_inv2 (pow2 256)) prime;
  lemma_twice_brackets k (pow2 256) 1 l (pow2 256) 1 (modp_inv2 (pow2 256));
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime == 1);
  modulo_distributivity_mult_last_two k (pow2 256) l (pow2 256) (modp_inv2 (pow2 256)) prime;
  lemma_mul_ass3 k (pow2 256) l


let multiplicationInDomainNat #k #l a b = 
  assert_norm (prime256 > 3);
  let multResult = a * b * modp_inv2_prime (pow2 256) prime256 % prime256 in 
  modulo_distributivity_mult2 (k * pow2 256) (l * pow2 256) (modp_inv2_prime (pow2 256) prime256) prime;
   lemma_twice_brackets k (pow2 256) 1 l (pow2 256) 1 (modp_inv2 (pow2 256));
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime == 1);
  modulo_distributivity_mult_last_two k (pow2 256) l (pow2 256) (modp_inv2 (pow2 256)) prime;
  lemma_mul_ass3 k (pow2 256) l


val additionInDomain: #k: nat -> #l: nat -> 
  a: felem4 {as_nat4 a == toDomain_ (k) /\ as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b == toDomain_ (l) /\ as_nat4 b < prime} -> Lemma 
  (ensures (let result = felem_add a b in as_nat4 result == toDomain_(k + l)))

let additionInDomain #k #l a b = 
  let result = felem_add a b in 
  assert(as_nat4 result = (as_nat4 a + as_nat4 b) % prime);
  assert(as_nat4 result = (toDomain_(k) + toDomain_(l)) % prime);
  assert(as_nat4 result = ((k * pow2 256 % prime) + (l * pow2 256 % prime)) % prime);
  modulo_distributivity (k * pow2 256) (l *pow2 256) prime;
  assert(as_nat4 result = toDomain_ (k + l))


val additionInDomainNat: #k: nat -> #l: nat -> a: nat {a == toDomain_ k /\ a < prime} -> b: nat {b == toDomain_ l /\ b < prime} ->
  Lemma (let result = (a + b) % prime in result == toDomain_ (k + l))

let additionInDomainNat #k #l a b = 
  modulo_distributivity (k * pow2 256) (l * pow2 256) prime


let additionInDomain2Nat a b = 
  let k = fromDomain_ a in 
  let l = fromDomain_ b in 
  lemmaFromDomainToDomain a;
  lemmaFromDomainToDomain b;
  additionInDomainNat #k #l a b


val substractionInDomainNat: #k: nat -> #l: nat -> a: nat {a == toDomain_ k /\ a < prime} -> b: nat {b == toDomain_ l /\ b < prime} -> 
  Lemma ((a - b) % prime  == toDomain_ (k - l))

let substractionInDomainNat #k #l a b = 
  lemma_mod_sub_distr a (l * pow2 256) prime;
  lemma_mod_add_distr (-l * pow2 256) (k * pow2 256) prime


let substractionInDomain2Nat a b = 
  let k = fromDomain_ a in 
  let l = fromDomain_ b in 
  lemmaFromDomainToDomain a;
  lemmaFromDomainToDomain b;
  substractionInDomainNat #k #l a b


val lemmaDistributivityInDomain: a: int -> b: int -> Lemma (toDomain_ (a * (b % prime) % prime) = toDomain_ (a * b % prime))
  [SMTPat (toDomain_ (a * (b % prime) % prime))]

let lemmaDistributivityInDomain a b = 
  lemma_mod_mul_distr_r a b prime

