module Hacl.Impl.P256.MontgomeryMultiplication

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open FStar.Math.Lemmas
open FStar.Mul

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas
open Hacl.Impl.LowLevel
open Hacl.Impl.P256.LowLevel

#reset-options "--z3refresh --z3rlimit 100"

val add8_without_carry1:  t: widefelem -> t1: widefelem -> result: widefelem  -> Stack unit
  (requires fun h -> live h t /\ live h t1 /\ live h result /\ eq_or_disjoint t1 result /\ 
    eq_or_disjoint t result /\ wide_as_nat h t1 < pow2 320 /\ wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\  wide_as_nat h1 result = wide_as_nat h0 t + wide_as_nat h0 t1)

let add8_without_carry1 t t1 result  = 
  let _  = add8 t t1 result in 
    assert_norm (pow2 320 + prime256 * prime256 < pow2 512)

inline_for_extraction noextract
val montgomery_multiplication_round: t: widefelem -> round: widefelem -> Stack unit 
  (requires fun h -> live h t /\ live h round /\ wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> modifies (loc round)  h0 h1 /\
    wide_as_nat h1 round = (wide_as_nat h0 t + prime256 * (wide_as_nat h0 t % pow2 64)) / pow2 64)

let montgomery_multiplication_round t round =
  push_frame(); 
    let h0 = ST.get() in 
    let t2 = create (size 8) (u64 0) in 
    let t3 = create (size 8) (u64 0) in 
    let t1 = mod64 t in 
      recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list); 
    shortened_mul prime256_buffer t1 t2;
    add8_without_carry1 t t2 t3;
    shift8 t3 round;
  pop_frame()  


(* move them all 2gether *)
private let mul_lemma_1 (a: nat) (c: nat) (b: pos) : Lemma (requires (a < c)) (ensures (a * b < c * b)) = ()
private let mul_lemma_ (a: nat) (b: nat) (c: nat) : Lemma (requires (a < c /\ b < c)) (ensures (a * b < c * c)) = ()

val montgomery_multiplication_one_round_proof: 
  t: nat {t < prime256 * prime256} -> 
  result: nat { result = (t + (t % pow2 64) * prime256) / pow2 64} ->
  co: nat{co % prime256 == t % prime256} -> 
    Lemma (
    result % prime256 == co * modp_inv2 (pow2 64) % prime256 /\
     result < prime256 * prime256)

let montgomery_multiplication_one_round_proof t result co = 
  mult_one_round t co;
  mul_lemma_1 (t % pow2 64) (pow2 64) prime256;
  assert_norm (prime256 * prime256 + pow2 64 * prime256 < pow2 575);
  lemma_div_lt (t + (t % pow2 64) * prime256) 575 64; 
  assert_norm (prime256 * prime256 > pow2 (575 - 64))


assume val lemma_montgomery_mod_inverse_addition: a: nat -> 
  Lemma (
    (a * modp_inv2_prime(pow2 64) prime256  * modp_inv2_prime (pow2 64) prime256) % prime256 == (a * modp_inv2_prime(pow2 128) prime256) % prime256)

assume val lemma_montgomery_mod_inverse_addition2: a: nat -> 
  Lemma (
    (a * modp_inv2_prime (pow2 128) prime256  * modp_inv2_prime (pow2 128) prime256) % prime256 == (a * modp_inv2_prime(pow2 256) prime256) % prime256)

inline_for_extraction noextract
val montgomery_multiplication_round_twice: t: widefelem -> result: widefelem -> Stack unit 
  (requires fun h -> live h t /\ live h result  /\ wide_as_nat h t < prime256 * prime256)
  (ensures fun h0 _ h1 -> 
    let round = (wide_as_nat h0 t + prime256 * (wide_as_nat h0 t % pow2 64)) / pow2 64 in 
    wide_as_nat h1 result < prime256 * prime256 /\
    wide_as_nat h1 result % prime256 == (wide_as_nat h0 t * modp_inv2_prime (pow2 128) prime256) % prime256 /\
    wide_as_nat h1 result == (round + prime256 * (round % pow2 64)) / pow2 64
  )
 

let montgomery_multiplication_round_twice t result = 
  push_frame();
    let tempRound = create (size 8) (u64 0) in 
      let h0 = ST.get() in 
    montgomery_multiplication_round t tempRound; 
      let h1 = ST.get() in 
      montgomery_multiplication_one_round_proof (wide_as_nat h0 t)  (wide_as_nat h1 tempRound) (wide_as_nat h0 t);
    montgomery_multiplication_round tempRound result;
      let h2 = ST.get() in 
      assert_norm (prime256 > 3);
      montgomery_multiplication_one_round_proof (wide_as_nat h1 tempRound) (wide_as_nat h2 result) (wide_as_nat h0 t * modp_inv2_prime (pow2 64) prime256);
      lemma_montgomery_mod_inverse_addition (wide_as_nat h0 t);
  pop_frame()


inline_for_extraction noextract
val montgomery_multiplication_buffer_by_one: a: felem -> r: felem ->  Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h r)) 
  (ensures (fun h0 _ h1 -> modifies1 r h0 h1 ))

let montgomery_multiplication_buffer_by_one a result = 
  push_frame();
    let t = create (size 8) (u64 0) in 
      let t_low = sub t (size 0) (size 4) in 
    let round2 = create (size 8) (u64 0) in 
    let round4 = create (size 8) (u64 0) in  

    (*mul a b t;  *)
    copy t_low a; 
      let h0 = ST.get() in 
      assert(wide_as_nat h0 t < prime256 * prime256);
    montgomery_multiplication_round_twice t round2;
    montgomery_multiplication_round_twice round2 round4; 
      lemma_montgomery_mod_inverse_addition2 (wide_as_nat h0 t);
      admit();
    reduction_prime256_2prime256_8_with_carry_impl round4 result; admit();
  pop_frame()  



val montgomery_multiplication_buffer: a: felem -> b: felem -> r: felem ->  Stack unit
  (requires (fun h -> live h a /\ as_nat h a < prime256 /\ live h b /\ live h r /\ as_nat h b < prime256)) 
  (ensures (fun h0 _ h1 -> modifies1 r h0 h1 ))

let montgomery_multiplication_buffer a b result = 
  push_frame();
    let t = create (size 8) (u64 0) in 
    let round2 = create (size 8) (u64 0) in 
    let round4 = create (size 8) (u64 0) in  

    mul a b t;  
      let h0 = ST.get() in 
      mul_lemma_ (as_nat h0 a) (as_nat h0 b) prime256;
      assert(wide_as_nat h0 t < prime256 * prime256);
    montgomery_multiplication_round_twice t round2;
    montgomery_multiplication_round_twice round2 round4; 
      lemma_montgomery_mod_inverse_addition2 (wide_as_nat h0 t);
      admit();
    reduction_prime256_2prime256_8_with_carry_impl round4 result; admit();
  pop_frame()  


