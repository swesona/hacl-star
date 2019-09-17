module Hacl.Impl.P256.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Basic
open Hacl.Spec.P256.MontgomeryMultiplication

open Hacl.Impl.LowLevel

open FStar.Math.Lemmas

open FStar.Mul

#reset-options "--z3refresh --z3rlimit 100"


inline_for_extraction noextract
val reduction_prime256_2prime256_with_carry_impl: cin: uint64 -> x: felem -> result: felem ->
  Stack unit 
    (requires fun h -> live h x /\ live h result /\  eq_or_disjoint x result /\ 
      (let x = as_seq h x in  felem_seq_as_nat x + uint_v cin * pow2 256) < 2 * prime256)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ 
      (
  let r = as_seq h1 result in 
  let x = as_seq h0 x in 
  felem_seq_as_nat r = (felem_seq_as_nat x + uint_v cin * pow2 256) % prime256
      )
    )  


let reduction_prime256_2prime256_with_carry_impl cin x result = 
  push_frame();
    let tempBuffer = create (size 4) (u64 0) in 
    let tempBufferForSubborrow = create (size 1) (u64 0) in 
    recall_contents prime256_buffer (Lib.Sequence.of_list p256_prime_list);
      let h0  = ST.get() in 
    let c = sub4_il x prime256_buffer tempBuffer in
      let h1 = ST.get() in 
	assert(let x = felem_seq_as_nat (as_seq h0 x) in if x < prime256 then uint_v c = 1 else uint_v c = 0);
	assert(felem_seq_as_nat (as_seq h1 tempBuffer)  = felem_seq_as_nat (as_seq h0 x) - prime256 + uint_v c * pow2 256);
    let carry = sub_borrow c cin (u64 0) tempBufferForSubborrow in 
      assert(if uint_v cin > 0 then uint_v carry == 0 else if uint_v c = 0 then uint_v carry = 0 else uint_v carry = 1);
      cmovznz4 carry tempBuffer x result;
      let h3 = ST.get() in 
      modulo_addition_lemma (felem_seq_as_nat (as_seq h3 result)) prime256 1;
      assert((felem_seq_as_nat (as_seq h3 result) + prime256) % prime256 = (felem_seq_as_nat (as_seq h3 result)) % prime256);
      small_modulo_lemma_1 (as_nat h3 result) prime256;
      assert(let resultN = felem_seq_as_nat (as_seq h3 result) in 
	if uint_v cin = 1 then 
	  if uint_v c = 0 then 
	    resultN = felem_seq_as_nat (as_seq h0 x) - prime256 /\
	    (felem_seq_as_nat (as_seq h0 x) + uint_v cin * pow2 256) % prime256 = resultN
	  else 
	    resultN = felem_seq_as_nat (as_seq h0 x) - prime256 + pow2 256 /\
	    resultN < prime256 /\
	    resultN % prime256 == resultN  /\
	    (felem_seq_as_nat (as_seq h0 x) + uint_v cin * pow2 256) % prime256 == resultN  
       else 
        True );

      assert(let resultN = felem_seq_as_nat (as_seq h3 result) in 
	if uint_v cin = 0 then 
	  if uint_v c = 0 then 
	    uint_v carry = 0 /\
	    resultN = felem_seq_as_nat (as_seq h0 x) - prime256 /\
	    (felem_seq_as_nat (as_seq h0 x) + uint_v carry * pow2 256) % prime256  == resultN
	  else 
	    uint_v carry = 1 /\
	    resultN = felem_seq_as_nat (as_seq h0 x) /\
	    (felem_seq_as_nat (as_seq h0 x) + uint_v cin * pow2 256) % prime256  = resultN % prime256 
	  else True  );
 
 pop_frame()   



val lemma_t_computation: t: uint64{uint_v t == 0 \/ uint_v t == 1} -> 
  Lemma
    (
        let t0 = u64 0 in 
	let t1 = (u64 0) -. (t <<. (size 32)) in 
	let t2 = (u64 0) -. t in 
	let t3 = (t <<. (size 32)) -. (t <<. (size 1)) in 
	let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in 
	if uint_v t = 1 then s == pow2 256 - prime256 - 1 else s == 0
    )

let lemma_t_computation t = 
  let t0 = u64 0 in 
  let t1 = (u64 0) -. (t <<. (size 32)) in 
  let t2 = (u64 0) -. t in 
  let t3 = (t <<. (size 32)) -. (t <<. (size 1)) in 
  let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in  
  assert_norm(18446744069414584320 * pow2 64 + 18446744073709551615 * pow2 128 + 4294967294 * pow2 192 = pow2 256 - prime256 - 1)


val lemma_t_computation2: t: uint64 {uint_v t == 0 \/ uint_v t == 1} ->
  Lemma
    (
      let t0 = (u64 0) -. t in 
      let t1 = ((u64 0) -. t) >>. (size 32) in 
      let t2 = u64 0 in 
      let t3 = t -. (t <<. (size 32)) in 
      let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in 
      if uint_v t = 1 then s == prime256 else s == 0
    )

let lemma_t_computation2 t = 
  let t0 = (u64 0) -. t in 
  let t1 = ((u64 0) -. t) >>. (size 32) in 
  let t2 = u64 0 in 
  let t3 = t -. (t <<. (size 32)) in 
  let s = uint_v t0 + uint_v t1 * pow2 64 + uint_v t2 * pow2 128 + uint_v t3 * pow2 192 in  
  assert_norm(18446744073709551615 + 4294967295 * pow2 64 + 18446744069414584321 * pow2 192 = prime256)


val p256_add: arg1: felem -> arg2: felem ->  out: felem -> Stack unit 
  (requires (fun h0 ->  
    live h0 arg1 /\ live h0 arg2 /\ live h0 out /\ 
    eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
    as_nat h0 arg1 < prime256 /\ as_nat h0 arg2 < prime256 
   )
  )
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\ 
      as_nat h1 out == (as_nat h0 arg1 + as_nat h0 arg2) % prime256 /\
      as_seq h1 out == felem_add_seq (as_seq h0 arg1) (as_seq h0 arg2)
  ))


let p256_add arg1 arg2 out = 
  let h0 = ST.get() in   
  let t = add4 arg1 arg2 out in 
    lemma_t_computation t;
    reduction_prime256_2prime256_with_carry_impl t out out;
  let h2 = ST.get() in 
    additionInDomain2Nat (as_nat h0 arg1) (as_nat h0 arg2);
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0 arg1) + fromDomain_ (as_nat h0 arg2));
    lemma_eq_funct (as_seq h2 out) (felem_add_seq (as_seq h0 arg1) (as_seq h0 arg2))


val p256_double: arg1: felem ->  out: felem -> Stack unit 
  (requires (fun h0 ->  live h0 arg1 /\ live h0 out /\ eq_or_disjoint arg1 out /\ as_nat h0 arg1 < prime256))
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\ as_nat h1 out == (2 * as_nat h0 arg1) % prime256 /\ as_nat h1 out < prime256))

let p256_double arg1 out = 
  let t = add4 arg1 arg1 out in 
  lemma_t_computation t;
  reduction_prime256_2prime256_with_carry_impl t out out


val p256_sub: arg1: felem -> arg2: felem -> out: felem -> Stack unit 
  (requires 
    (fun h0 -> live h0 out /\ live h0 arg1 /\ live h0 arg2 /\ 
      eq_or_disjoint arg1 out /\ eq_or_disjoint arg2 out /\
      as_nat h0 arg1 < prime256 /\ as_nat h0 arg2 < prime256))
    (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\ 
	as_nat h1 out == (as_nat h0 arg1 - as_nat h0 arg2) % prime256 /\
	as_seq h1 out == felem_sub_seq (as_seq h0 arg1) (as_seq h0 arg2)
  ))

let p256_sub arg1 arg2 out = 
    let h0 = ST.get() in 
  let t = sub4 arg1 arg2 out in 
    lemma_t_computation2 t;
  let t0 = (u64 0) -. t in 
  let t1 = ((u64 0) -. t) >>. (size 32) in 
  let t2 = u64 0 in 
  let t3 = t -. (t <<. (size 32)) in 
    modulo_addition_lemma  (as_nat h0 arg1 - as_nat h0 arg2) prime256 1;
  let c = add4_variables out (u64 0)  t0 t1 t2 t3 out in 
    let h2 = ST.get() in 
      assert(
      if as_nat h0 arg1 - as_nat h0 arg2 >= 0 then 
	begin
	  modulo_lemma (as_nat h0 arg1 - as_nat h0 arg2) prime256;
	  as_nat h2 out == (as_nat h0 arg1 - as_nat h0 arg2) % prime256
	end
      else
          begin
	    modulo_lemma (as_nat h2 out) prime256;
            as_nat h2 out == (as_nat h0 arg1 - as_nat h0 arg2) % prime256
	  end);

    substractionInDomain2Nat (felem_seq_as_nat (as_seq h0 arg1)) (felem_seq_as_nat (as_seq h0 arg2));
    inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat (as_seq h0 arg1)) - fromDomain_ (felem_seq_as_nat (as_seq h0 arg2)));
    lemma_eq_funct (as_seq h2 out) (felem_sub_seq (as_seq h0 arg1) (as_seq h0 arg2))
    
