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


(* the lemma shows that the result of addition in domain (moved out of domain) is the same if the variables were out of domain *)
val additionInDomain2: a: felem4{as_nat4 a < prime} -> b: felem4 {as_nat4 b < prime} -> Lemma (let result = felem_add a b in 
  as_nat4 result = toDomain_ (fromDomain_ (as_nat4 a) + fromDomain_ (as_nat4 b)))

let additionInDomain2 a b = 
  let k = fromDomain_ (as_nat4 a) in 
  let l = fromDomain_ (as_nat4 b) in 
  lemmaFromDomainToDomain (as_nat4 a);
  lemmaFromDomainToDomain (as_nat4 b);
  additionInDomain #k #l a b


let additionInDomain2Nat a b = 
  let k = fromDomain_ a in 
  let l = fromDomain_ b in 
  lemmaFromDomainToDomain a;
  lemmaFromDomainToDomain b;
  additionInDomainNat #k #l a b


(* the lemma shows the equivalence between fromDomain(a:nat) and fromDomain(a % prime) *)
val fromDomain_mod_is_not_mod: a: nat -> Lemma (fromDomain_ a == fromDomain_ (a % prime))

let fromDomain_mod_is_not_mod a = 
  lemma_mod_mul_distr_l a (modp_inv2(pow2 256)) prime


val additionInDomainLemma2: a: felem4{as_nat4 a < prime} -> b: felem4{as_nat4 b < prime} -> 
  Lemma (ensures (as_nat4 (fromDomain (felem_add a b)) = (as_nat4(fromDomain (a)) + as_nat4(fromDomain (b))) % prime))

let  additionInDomainLemma2 a b =  
  let k = (as_nat4 (fromDomain a) + as_nat4 (fromDomain b)) % prime in 
  modulo_distributivity (as_nat4 a * modp_inv2 (pow2 256)) (as_nat4 b * modp_inv2 (pow2 256)) prime;
  distributivity_add_left (as_nat4 a) (as_nat4 b) (modp_inv2 (pow2 256));
  fromDomain_mod_is_not_mod (as_nat4 a + as_nat4 b)

val subtractionInDomain: #k: nat -> #l: nat -> 
  a: felem4 {as_nat4 a == toDomain_ (k) /\ as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b == toDomain_ (l) /\ as_nat4 b < prime} -> Lemma 
  (ensures (let result = felem_sub a b in as_nat4 result == toDomain_(k - l)))

let subtractionInDomain #k #l a b = 
  let result = felem_sub a b in 
  lemma_mod_sub_distr (as_nat4 a) (l * pow2 256) prime;
  lemma_mod_add_distr (-l * pow2 256) (k * pow2 256) prime

val substractionInDomainNat: #k: nat -> #l: nat -> a: nat {a == toDomain_ k /\ a < prime} -> b: nat {b == toDomain_ l /\ b < prime} -> 
  Lemma ((a - b) % prime  == toDomain_ (k - l))

let substractionInDomainNat #k #l a b = 
  lemma_mod_sub_distr a (l * pow2 256) prime;
  lemma_mod_add_distr (-l * pow2 256) (k * pow2 256) prime


val substractionInDomain2: a: felem4{as_nat4 a < prime} -> b: felem4{as_nat4 b < prime} -> Lemma (let result = felem_sub a b in 
  as_nat4 result = toDomain_ (fromDomain_ (as_nat4 a) - fromDomain_ (as_nat4 b)))

let substractionInDomain2 a b = 
  let k = fromDomain_ (as_nat4 a) in 
  let l = fromDomain_ (as_nat4 b) in 
  lemmaFromDomainToDomain (as_nat4 a);
  lemmaFromDomainToDomain (as_nat4 b);
  subtractionInDomain #k #l a b

let substractionInDomain2Nat a b = 
  let k = fromDomain_ a in 
  let l = fromDomain_ b in 
  lemmaFromDomainToDomain a;
  lemmaFromDomainToDomain b;
  substractionInDomainNat #k #l a b


let felem_add_seq a b = 
  let a0 = index a 0 in 
  let a1 = index a 1 in 
  let a2 = index a 2 in 
  let a3 = index a 3 in 

  let b0 = index b 0 in 
  let b1 = index b 1 in 
  let b2 = index b 2 in 
  let b3 = index b 3 in 

  let (r0, r1, r2, r3) = felem_add (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  
  let r = create 4 (u64 0)  in 
  let r = upd r 0 r0 in
  let r = upd r 1 r1 in 
  let r = upd r 2 r2 in 
  let r = upd r 3 r3 in 

  additionInDomain2 (a0, a1, a2, a3) (b0, b1, b2, b3);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat4 (a0, a1, a2, a3)) + fromDomain_ (as_nat4 (b0, b1, b2, b3)));
  r


let felem_sub_seq a b = 
  let a0 = index a 0 in 
  let a1 = index a 1 in 
  let a2 = index a 2 in 
  let a3 = index a 3 in 

  let b0 = index b 0 in 
  let b1 = index b 1 in 
  let b2 = index b 2 in 
  let b3 = index b 3 in 

  let a_tuple = a0, a1, a2, a3 in 
  let b_tuple = b0, b1, b2, b3 in 
  let (r0, r1, r2, r3) = felem_sub a_tuple b_tuple in 

  
  let r = create 4 (u64 0)  in 
  let r = upd r 0 r0 in
  let r = upd r 1 r1 in 
  let r = upd r 2 r2 in 
  let r = upd r 3 r3 in 

  substractionInDomain2 (a0, a1, a2, a3) (b0, b1, b2, b3);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat4 (a0, a1, a2, a3)) - fromDomain_ (as_nat4 (b0, b1, b2, b3)));
  r


let montgomery_multiplication_seq a b  = 
  let a0 = index a 0 in 
  let a1 = index a 1 in 
  let a2 = index a 2 in 
  let a3 = index a 3 in 

  let b0 = index b 0 in 
  let b1 = index b 1 in 
  let b2 = index b 2 in 
  let b3 = index b 3 in 

    [@inline_let]
  let a_tuple = a0, a1, a2, a3 in 
    [@inline_let]
  let b_tuple = b0, b1, b2, b3 in 
  let (r0, r1, r2, r3) = montgomery_multiplication (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  lemmaFromDomainToDomain (as_nat4 a_tuple);
  lemmaFromDomainToDomain (as_nat4 b_tuple);
  multiplicationInDomain #(fromDomain_ (as_nat4 a_tuple)) #(fromDomain_ (as_nat4 b_tuple)) a_tuple b_tuple;
  inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat b));

  let r = create 4 (u64 0)  in 
  let r = upd r 0 r0 in
  let r = upd r 1 r1 in 
  let r = upd r 2 r2 in 
  let r = upd r 3 r3 in 
   r

#reset-options "--z3refresh --z3rlimit 100" 

val modulo_distributivity_mult_three: 
  a: int -> b: int ->  c: int -> d: pos -> Lemma ((a * b  * c) % d = ((a % d) * (b % d) * (c % d)) % d)


let modulo_distributivity_mult_three a b c d = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  assert_by_tactic (a * b * c = a * (b * c)) canon;
  lemma_mod_mul_distr_l a (b * c) d;
  assert_by_tactic (((a % d) * b * c) % d == (b * ((a % d) * c)) % d) canon;
  lemma_mod_mul_distr_l b ((a % d) * c) d;
  lemma_mod_mul_distr_r ((a % d) * (b % d)) c d


val modulo_distributivity_mult_four: 
  a: int -> b: int ->  c: int -> d: nat ->  e: pos -> Lemma ((a * b  * c * d) % e = ((a % e) * (b % e) * (c % e) * (d % e)) % e)


let modulo_distributivity_mult_four a b c d e = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  assert_by_tactic ((a * b * c * d) % e == ((a * b * c) * d) % e) canon;
    assert((a * b * c * d) % e == ((a * b * c) * d) % e);
  lemma_mod_mul_distr_l (a * b * c) d e;
    assert((((a * b * c) * d) % e) == ((a * b * c) % e * d) % e);
  modulo_distributivity_mult_three a b c e;
    assert((((a * b * c) * d) % e) == (((a % e) * (b % e) * (c % e)) % e * d) % e);
  lemma_mod_mul_distr_l ((a % e) * (b % e) * (c % e)) d e;  
    assert(((((a % e) * (b % e) * (c % e)) % e * d) % e) == (((a % e) * (b % e) * (c % e)) * d) % e);
  lemma_mod_mul_distr_r ((a % e) * (b % e) * (c % e)) d e;
  assert_by_tactic ((((a % e) * (b % e) * (c % e)) * (d % e)) % e == ((a % e) * (b % e) * (c % e) * (d % e)) % e) canon


val lemma_toDomain_reduce_prime3: a: int -> b: int -> c: int -> Lemma (toDomain_ ((a % prime) * (b % prime) * (c % prime)) = toDomain_ (a * b * c))

let lemma_toDomain_reduce_prime3 a b c = 
  inDomain_mod_is_not_mod ((a % prime) * (b % prime) * (c % prime));
  assert(toDomain_ (((a % prime) * (b % prime) * (c % prime)) % prime) == toDomain_ ((a % prime) * (b % prime) * (c % prime)));
    modulo_distributivity_mult_three a b c prime;
  assert(toDomain_ ((a % prime) * (b % prime) * (c % prime) % prime) = toDomain_ ((a * b * c) % prime));
  inDomain_mod_is_not_mod (a * b * c);
  assert(toDomain_ ((a * b * c) % prime) = toDomain_ (a * b * c))


#reset-options "--z3refresh --z3rlimit 300" 
val lemma_toDomain_reduce_prime4: a: int -> b: int -> c: int -> d: nat -> Lemma (toDomain_ ((a % prime) * (b % prime) * (c % prime) * (d % prime)) = toDomain_ (a * b * c * d))

let lemma_toDomain_reduce_prime4 a b c d = 
  inDomain_mod_is_not_mod ((a % prime) * (b % prime) * (c % prime) * (d % prime));
  modulo_distributivity_mult_four a b c d prime;
  inDomain_mod_is_not_mod (a * b * c * d)


let mm_cube_seq a= 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in  
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = cube_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    
    lemma_brackets5_twice (as_nat4 a_tuple) (as_nat4 a_tuple) (as_nat4 a_tuple) (modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
    lemma_mod_mul_distr_l ((as_nat4 a_tuple * modp_inv2 (pow2 256))  * (as_nat4 a_tuple * modp_inv2 (pow2 256))  * as_nat4 a_tuple) (modp_inv2 (pow2 256)) prime;
    lemma_brackets5 (as_nat4 a_tuple * modp_inv2 (pow2 256)) (as_nat4 a_tuple * modp_inv2 (pow2 256))  1 (as_nat4 a_tuple) (modp_inv2 (pow2 256));
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod ((as_nat4 a_tuple * modp_inv2 (pow2 256))  * (as_nat4 a_tuple * modp_inv2 (pow2 256))  * (as_nat4 a_tuple * modp_inv2 (pow2 256)) ) ;
    lemma_toDomain_reduce_prime3 (as_nat4 a_tuple * modp_inv2 (pow2 256)) (as_nat4 a_tuple * modp_inv2 (pow2 256)) (as_nat4 a_tuple * modp_inv2 (pow2 256));
    inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a));
    r


let mm_quatre_seq a= 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let result = montgomery_multiplication_seq a a in 
  let resultFinal = montgomery_multiplication_seq result result in 
      modulo_distributivity_mult ((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) ((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) prime;
      assert_by_tactic (((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) * ((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) == (fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) canon;
  resultFinal


val lemma_multiplicationInDomainByNumber: a: felem4 -> b: int -> Lemma (fromDomain_ (as_nat4 a * b % prime) = b * fromDomain_ (as_nat4 a) % prime)

let lemma_multiplicationInDomainByNumber a b = 
  lemma_mod_mul_distr_l (as_nat4 a * b) (modp_inv2 (pow2 256)) prime;
  lemma_brackets_l (as_nat4 a) b (modp_inv2 (pow2 256));
  lemma_brackets (as_nat4 a) b (modp_inv2 (pow2 256));
  lemma_brackets1 (as_nat4 a) b (modp_inv2 (pow2 256));
  lemma_mod_mul_distr_r b (as_nat4 a * modp_inv2 (pow2 256)) prime
  

let mm_byTwo_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = shift_left_felem (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 2;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (2 * fromDomain_ (as_nat4 a_tuple));
    r


let lemma_add_same_value_is_by_two a = 
    let r1 = felem_add_seq a a in 
    let r2 = mm_byTwo_seq a in 
    let a_ = felem_seq_as_nat a in 
    lemma_mod_mul_distr_r 2 (fromDomain_ a_) prime;
    inDomain_mod_is_not_mod (2 * (fromDomain_ a_ % prime));
    lemma_eq_funct r1 r2



let mm_byThree_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByThree_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 3;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (3 * fromDomain_ (as_nat4 a_tuple));
    r


let mm_byFour_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByFour_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 4;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (4 * fromDomain_ (as_nat4 a_tuple)); 
    r


let mm_byEight_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByEight_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 8;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (8 * fromDomain_ (as_nat4 a_tuple));
    r


val lemmaDistributivityInDomain: a: int -> b: int -> Lemma (toDomain_ (a * (b % prime) % prime) = toDomain_ (a * b % prime))
  [SMTPat (toDomain_ (a * (b % prime) % prime))]

let lemmaDistributivityInDomain a b = 
  lemma_mod_mul_distr_r a b prime

