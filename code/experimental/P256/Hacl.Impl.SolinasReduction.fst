module Hacl.Impl.SolinasReduction

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.Spec.P256.SolinasReduction
open Hacl.Impl.Gen
open Hacl.Spec.P256.Core
open Hacl.Spec.P256.Definitions
open FStar.Mul


module Seq = Lib.Sequence

#reset-options "--z3refresh --z3rlimit  100"

inline_for_extraction noextract
val load_buffer: a0: uint64 -> a1: uint64 -> a2: uint64 -> a3: uint64 -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ 
      (
	let o = as_seq h1 o in 
	felem_seq_as_nat o = uint_v a0 + uint_v a1 * pow2 64 + uint_v a2 * pow2 128 + uint_v a3 * pow2 192
      )
)

let load_buffer a0 a1 a2 a3 o = 
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  upd o (size 0) a0;
  upd o (size 1) a1;
  upd o (size 2) a2;
  upd o (size 3) a3


val upl_zer_buffer: c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32 -> c4: uint32 -> 
  c5: uint32 -> c6: uint32 -> c7: uint32
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\ 
      (
	let o = as_seq h1 o in 
	felem_seq_as_nat o == 
	  (uint_v c0 + uint_v c1 * pow2 (1 * 32) + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + 
	  uint_v c4 * pow2 (4 * 32) + uint_v c5 * pow2 (5 * 32) + uint_v  c6 * pow2 (6 * 32) + 
	  uint_v c7 * pow2 (7 * 32)) % prime
      )
   )

let upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 temp o = 
    let b0 = store_high_low_u c1 c0 in 
    let b1 = store_high_low_u c3 c2 in 
    let b2 = store_high_low_u c5 c4 in 
    let b3 = store_high_low_u c7 c6 in 
      assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
      assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
      assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o


val upl_fir_buffer: c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
      (
	let o = as_seq h1 o in 
	felem_seq_as_nat o == 
	  (uint_v c11 * pow2 (3 * 32) + uint_v c12 * pow2 (4 * 32) + uint_v c13 * pow2 (5 * 32) + 
	   uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime
      )
   )


let upl_fir_buffer c11 c12 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  let b0 = u64(0) in 
  let b1 = store_high_low_u c11 (u32 0) in 
  let b2 = store_high_low_u c13 c12 in 
  let b3 = store_high_low_u c15 c14 in 
  load_buffer b0 b1 b2 b3 temp;
  reduction_prime_2prime_impl temp o


val upl_sec_buffer: c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o )
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
      (
      	let o = as_seq h1 o in felem_seq_as_nat o == 
	     (uint_v c12 * pow2 (3 * 32) + uint_v c13 * pow2 (4 * 32) + 
        uint_v c14 * pow2 (5 * 32) + uint_v c15 * pow2 (6 * 32)) % prime /\
	felem_seq_as_nat o < prime
      )
 )


let upl_sec_buffer c12 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
    let b0 = u64 (0) in 
    let b1 = store_high_low_u c12 (u32 0) in 
    let b2 = store_high_low_u c14 c13 in 
    let b3 = store_high_low_u (u32 0) c15 in
    load_buffer b0 b1 b2 b3 o;
    
    let h1 = ST.get() in 
    let o = as_seq h1 o in 
    modulo_lemma (felem_seq_as_nat o) prime


val upl_thi_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c14: uint32 -> c15: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
 (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
      (
	let o = as_seq h1 o in felem_seq_as_nat o == 
	  (
      uint_v c8 + uint_v c9 * pow2 32 + uint_v c10 * pow2 (2 * 32) + 
      uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime
    )
 )  
	

let upl_thi_buffer c8 c9 c10 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
   let b0 = store_high_low_u c9 c8 in 
   let b1 = store_high_low_u (u32 0) c10 in 
   let b2 = u64 0 in 
   let b3 = store_high_low_u c15 c14 in 
   load_buffer b0 b1 b2 b3 temp;
   reduction_prime_2prime_impl temp o


val upl_for_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 ->
  temp: lbuffer uint64 (size 4)
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
      (
	let o = as_seq h1 o in felem_seq_as_nat o == 
	(
    uint_v c9 + uint_v c10 * pow2 32 + uint_v c11 * pow2 (2 * 32) + 
    uint_v c13 * pow2 (3 * 32) + uint_v c14 * pow2 (4 * 32) + 
    uint_v c15 * pow2 (5 * 32) + uint_v c13 * pow2 (6 * 32) + 
    uint_v c8 * pow2 (7 * 32)) % prime
  )
)  


let upl_for_buffer c8 c9 c10 c11 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
  let b0 = store_high_low_u c10 c9 in 
  let b1 = store_high_low_u c13 c11 in 
  let b2 = store_high_low_u c15 c14 in 
  let b3 = store_high_low_u c8 c13 in 
  load_buffer b0 b1 b2 b3 temp;
  reduction_prime_2prime_impl temp o


val upl_fif_buffer: c8: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
      (
	     let o = as_seq h1 o in 
	     felem_seq_as_nat o == (
        uint_v c11 + uint_v c12 * pow2 32 + uint_v c13 * pow2 (2 * 32) + 
        uint_v c8 * pow2 (6 * 32) + uint_v c10 * pow2 (7 * 32)) % prime
      )
 )  


let upl_fif_buffer c8 c10 c11 c12 c13 temp o = 
  
     assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
     assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
     assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
     assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
     assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = store_high_low_u c12 c11 in 
    let b1 = store_high_low_u (u32 0) c13 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c10 c8 in 
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o


val upl_six_buffer: c9: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> c14: uint32 -> c15: uint32
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
      (
	let o = as_seq h1 o in 
	felem_seq_as_nat o == (
    uint_v c12 + uint_v c13 * pow2 32 + uint_v c14 * pow2 (2 * 32) + uint_v c15 * pow2 (3 * 32) + 
	  uint_v c9 * pow2 (6 * 32) + uint_v c11 * pow2 (7 * 32)) % prime
      )
  )  


let upl_six_buffer c9 c11 c12 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = store_high_low_u c13 c12 in 
    let b1 = store_high_low_u c15 c14 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c11 c9 in 
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o


val upl_sev_buffer: c8: uint32 -> c9: uint32 -> c10: uint32 -> c12: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
      (
	     let o = as_seq h1 o in 
	     felem_seq_as_nat o == (
       uint_v c13 + uint_v c14 * pow2 32 + uint_v c15 * pow2 (2 * 32) + 
       uint_v c8 * pow2 (3 * 32) +  uint_v c9 * pow2 (4 * 32) + 
       uint_v c10 * pow2 (5 * 32) + uint_v c12 * pow2 (7 * 32)) % prime
      )
  ) 
  

let upl_sev_buffer c8 c9 c10 c12 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = store_high_low_u c14 c13 in 
    let b1 = store_high_low_u c8 c15 in 
    let b2 = store_high_low_u c10 c9 in 
    let b3 = store_high_low_u c12 (u32 0) in 
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o


val upl_eig_buffer: c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 
  -> temp: lbuffer uint64 (size 4) 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o /\ live h temp /\ disjoint o temp)
    (ensures fun h0 _ h1 -> modifies2 o temp h0 h1 /\
      (
	     let o = as_seq h1 o in felem_seq_as_nat o == (
        uint_v c14 + uint_v c15 * pow2 32 + uint_v c9 * pow2 (3 * 32) + 
        uint_v c10 * pow2 (4 * 32) + uint_v c11 * pow2 (5 * 32) + uint_v c13 * pow2 (7 * 32)) % prime
      )
  ) 
  

let upl_eig_buffer c9 c10 c11 c12 c13 c14 c15 temp o = 
  assert_norm (pow2 (1 * 32) * pow2 (2 * 32) = pow2 (3 * 32));
  assert_norm (pow2 (2 * 32) * pow2 (2 * 32) = pow2 (4 * 32));
  assert_norm (pow2 (3 * 32) * pow2 (2 * 32) = pow2 (5 * 32));
  assert_norm (pow2 (4 * 32) * pow2 (2 * 32) = pow2 (6 * 32));
  assert_norm (pow2 (5 * 32) * pow2 (2 * 32) = pow2 (7 * 32));
    let b0 = store_high_low_u c15 c14 in 
    let b1 = store_high_low_u c9 (u32 0) in 
    let b2 = store_high_low_u c11 c10 in 
    let b3 = store_high_low_u c13 (u32 0) in 
    load_buffer b0 b1 b2 b3 temp;
    reduction_prime_2prime_impl temp o


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


val solinas_reduction_upload0: c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32 -> c4: uint32 -> c5: uint32 -> 
  c6: uint32 -> c7: uint32 -> c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 -> tempBuffer: lbuffer uint64 (size 36) -> redBuffer: felem ->
    Stack unit 
      (fun h -> live h tempBuffer /\ live h redBuffer /\ disjoint redBuffer tempBuffer)
      (fun h0 _ h1 -> modifies2 tempBuffer redBuffer h0 h1 /\
	(
	  let t0 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 0) (size 4))) in 
	  let t1 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 4) (size 4))) in 
	  let t2 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 8) (size 4))) in 
	  let t3 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 12) (size 4))) in 
	  let t4 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 16) (size 4))) in 
	  let t5 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 20) (size 4))) in 
 	  t0 == (uint_v c0 + uint_v c1 * pow2 (1 * 32) + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + uint_v c4 * pow2 (4 * 32) + uint_v c5 * pow2 (5 * 32) + uint_v  c6 * pow2 (6 * 32) +  uint_v c7 * pow2 (7 * 32)) % prime /\
	  t1 == (uint_v c11 * pow2 (3 * 32) + uint_v c12 * pow2 (4 * 32) + uint_v c13 * pow2 (5 * 32) + 
	   uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime /\
	  t2 == (uint_v c12 * pow2 (3 * 32) + uint_v c13 * pow2 (4 * 32) +  uint_v c14 * pow2 (5 * 32) + uint_v c15 * pow2 (6 * 32)) % prime  /\
	  t3 == (uint_v c8 + uint_v c9 * pow2 32 + uint_v c10 * pow2 (2 * 32) + uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime /\
	  t4 == (uint_v c9 + uint_v c10 * pow2 32 + uint_v c11 * pow2 (2 * 32) + uint_v c13 * pow2 (3 * 32) + uint_v c14 * pow2 (4 * 32) + uint_v c15 * pow2 (5 * 32) + uint_v c13 * pow2 (6 * 32) + uint_v c8 * pow2 (7 * 32)) % prime /\
	  t5 == (uint_v c11 + uint_v c12 * pow2 32 + uint_v c13 * pow2 (2 * 32) + uint_v c8 * pow2 (6 * 32) + uint_v c10 * pow2 (7 * 32)) % prime
      
      )
)

let solinas_reduction_upload0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer redBuffer = 
    let t0 = sub tempBuffer (size 0) (size 4) in
    let t1 = sub tempBuffer (size 4) (size 4) in 
    let t2 = sub tempBuffer (size 8) (size 4) in 
    let t3 = sub tempBuffer (size 12) (size 4) in 
    let t4 = sub tempBuffer (size 16) (size 4) in 
    let t5 = sub tempBuffer (size 20) (size 4) in 
  upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 redBuffer t0; 
  upl_fir_buffer c11 c12 c13 c14 c15 redBuffer t1;
  upl_sec_buffer c12 c13 c14 c15 redBuffer t2; 
  upl_thi_buffer c8 c9 c10 c14 c15 redBuffer  t3;
  upl_for_buffer c8 c9 c10 c11 c13 c14 c15 redBuffer t4;
  upl_fif_buffer c8 c10 c11 c12 c13 redBuffer  t5

val solinas_reduction_upload: c0: uint32 -> c1: uint32 -> c2: uint32 -> c3: uint32 -> c4: uint32 -> c5: uint32 -> 
  c6: uint32 -> c7: uint32 -> c8: uint32 -> c9: uint32 -> c10: uint32 -> c11: uint32 -> c12: uint32 -> c13: uint32 -> 
  c14: uint32 -> c15: uint32 -> tempBuffer: lbuffer uint64 (size 36) -> 
  Stack unit
    (requires fun h -> live h tempBuffer)
    (ensures fun h0 _ h1 -> modifies1 tempBuffer h0 h1 /\ 
	(
	  let t0 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 0) (size 4))) in 
	  let t1 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 4) (size 4))) in 
	  let t2 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 8) (size 4))) in 
	  let t3 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 12) (size 4))) in 
	  let t4 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 16) (size 4))) in 
	  let t5 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 20) (size 4))) in 
	  let t6 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 24) (size 4))) in 
	  let t7 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 28) (size 4))) in 
	  let t8 = felem_seq_as_nat (as_seq h1 (gsub tempBuffer (size 32) (size 4))) in 
 	  t0 == (uint_v c0 + uint_v c1 * pow2 (1 * 32) + uint_v c2 * pow2 (2 * 32) + uint_v c3 * pow2 (3 * 32) + uint_v c4 * pow2 (4 * 32) + uint_v c5 * pow2 (5 * 32) + uint_v  c6 * pow2 (6 * 32) +  uint_v c7 * pow2 (7 * 32)) % prime /\
	  t1 == (uint_v c11 * pow2 (3 * 32) + uint_v c12 * pow2 (4 * 32) + uint_v c13 * pow2 (5 * 32) + 
	   uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime /\
	  t2 == (uint_v c12 * pow2 (3 * 32) + uint_v c13 * pow2 (4 * 32) +  uint_v c14 * pow2 (5 * 32) + uint_v c15 * pow2 (6 * 32)) % prime  /\
	  t3 == (uint_v c8 + uint_v c9 * pow2 32 + uint_v c10 * pow2 (2 * 32) + uint_v c14 * pow2 (6 * 32) + uint_v c15 * pow2 (7 * 32)) % prime /\
	  t4 == (uint_v c9 + uint_v c10 * pow2 32 + uint_v c11 * pow2 (2 * 32) + uint_v c13 * pow2 (3 * 32) + uint_v c14 * pow2 (4 * 32) + uint_v c15 * pow2 (5 * 32) + uint_v c13 * pow2 (6 * 32) + uint_v c8 * pow2 (7 * 32)) % prime /\
	  t5 == (uint_v c11 + uint_v c12 * pow2 32 + uint_v c13 * pow2 (2 * 32) + uint_v c8 * pow2 (6 * 32) + uint_v c10 * pow2 (7 * 32)) % prime /\
	  t6 == (uint_v c12 + uint_v c13 * pow2 32 + uint_v c14 * pow2 (2 * 32) + uint_v c15 * pow2 (3 * 32) + uint_v c9 * pow2 (6 * 32) + uint_v c11 * pow2 (7 * 32)) % prime /\
	  t7 == (uint_v c13 + uint_v c14 * pow2 32 + uint_v c15 * pow2 (2 * 32) +  uint_v c8 * pow2 (3 * 32) +  uint_v c9 * pow2 (4 * 32) + uint_v c10 * pow2 (5 * 32) + uint_v c12 * pow2 (7 * 32)) % prime /\
	  t8 == (uint_v c14 + uint_v c15 * pow2 32 + uint_v c9 * pow2 (3 * 32) +  uint_v c10 * pow2 (4 * 32) + uint_v c11 * pow2 (5 * 32) + uint_v c13 * pow2 (7 * 32)) % prime
    ))


let solinas_reduction_upload c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer  =  
  push_frame();
    let redBuffer = create (size 4) (u64 0) in 
    let t6 = sub tempBuffer (size 24) (size 4) in 
    let t7 = sub tempBuffer (size 28) (size 4) in 
    let t8 = sub tempBuffer (size 32) (size 4) in   
    
    let h0 = ST.get() in 
    solinas_reduction_upload0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 tempBuffer redBuffer;
    upl_six_buffer c9 c11 c12 c13 c14 c15 redBuffer  t6;
    upl_sev_buffer c8 c9 c10 c12 c13 c14 c15 redBuffer t7;
    upl_eig_buffer c9 c10 c11 c12 c13 c14 c15 redBuffer t8;
  pop_frame()
  

val solinas_reduction_impl: i: lbuffer uint64 (size 8) -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h i /\ live h o /\ disjoint i o)
    (ensures fun h0 _ h1 -> True)

let solinas_reduction_impl i o = 
  push_frame();
    let tempBuffer = create (size 44) (u64 0) in 
    let t0 = sub tempBuffer (size 0) (size 4) in
    let t1 = sub tempBuffer (size 4) (size 4) in 
    let t2 = sub tempBuffer (size 8) (size 4) in 
    let t3 = sub tempBuffer (size 12) (size 4) in 
    let t4 = sub tempBuffer (size 16) (size 4) in 
    let t5 = sub tempBuffer (size 20) (size 4) in 
    let t6 = sub tempBuffer (size 24) (size 4) in 
    let t7 = sub tempBuffer (size 28) (size 4) in 
    let t8 = sub tempBuffer (size 32) (size 4) in 
    let t11 = sub tempBuffer (size 36) (size 4) in 
    let t22 = sub tempBuffer (size 40) (size 4) in 

    let i0 = i.(size 0) in 
    let i1 = i.(size 1) in 
    let i2 = i.(size 2) in 
    let i3 = i.(size 3) in 
    let i4 = i.(size 4) in 
    let i5 = i.(size 5) in 
    let i6 = i.(size 6) in 
    let i7 = i.(size 7) in 

    let c0 = get_low_part i0 in 
    let c1 = get_high_part i0 in 
    let c2 = get_low_part i1 in 
    let c3 = get_high_part i1 in   
    let c4 = get_low_part i2 in 
    let c5 = get_high_part i2 in   
    let c6 = get_low_part i3 in 
    let c7 = get_high_part i3 in   
    let c8 = get_low_part i4 in 
    let c9 = get_high_part i4 in   
    let c10 = get_low_part i5 in 
    let c11 = get_high_part i5 in   
    let c12 = get_low_part i6 in 
    let c13 = get_high_part i6 in   
    let c14 = get_low_part i7 in 
    let c15 = get_high_part i7 in

  upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 redBuffer t0; 
  upl_fir_buffer c11 c12 c13 c14 c15 redBuffer t1;
  upl_sec_buffer c12 c13 c14 c15 t2;
  upl_thi_buffer c8 c9 c10 c14 c15 redBuffer  t3;
  upl_for_buffer c8 c9 c10 c11 c13 c14 c15 redBuffer t4;
  upl_fif_buffer c8 c10 c11 c12 c13 redBuffer  t5;
  upl_six_buffer c9 c11 c12 c13 c14 c15 redBuffer  t6;
  upl_sev_buffer c8 c9 c10 c12 c13 c14 c15 redBuffer t7;
  upl_eig_buffer c9 c10 c11 c12 c13 c14 c15 redBuffer t8; 

  assume(LowStar.Monotonic.Buffer.all_disjoint [loc t0; loc t1; loc t2; loc t3; loc t4; loc t5; loc t6; loc t7; loc t8; loc t11; loc t22; loc o]);

  p256_double t2 t22;  
  p256_double t1 t11;
  p256_add t0 t11 o;
  p256_add t22 o o;
  p256_add t3 o o;
  p256_add t4 o o;
  p256_sub o t5 o;
  p256_sub o t6 o;
  p256_sub o t7 o;
  p256_sub o t8 o;
    let h1 = ST.get() in 

  modulo_lemma (felem_seq_as_nat (as_seq h1 o)) prime;

  reduce_brackets (felem_seq_as_nat(as_seq h1 t0)) (felem_seq_as_nat(as_seq h1 t1)) (felem_seq_as_nat(as_seq h1 t2)) (felem_seq_as_nat(as_seq h1 t3)) (felem_seq_as_nat(as_seq h1 t4)) (felem_seq_as_nat(as_seq h1 t5)) (felem_seq_as_nat(as_seq h1 t6)) (felem_seq_as_nat(as_seq h1 t7)) (felem_seq_as_nat(as_seq h1 t8));
  solinas_reduction_mod (uint_v c0) (uint_v c1) (uint_v c2) (uint_v c3) (uint_v c4) (uint_v c5) (uint_v c6) (uint_v c7) (uint_v c8) (uint_v c9) (uint_v c10) (uint_v c11) (uint_v c12) (uint_v c13) (uint_v c14) (uint_v c15)
  (felem_seq_as_nat (as_seq h1 t0)) (felem_seq_as_nat (as_seq h1 t1)) (felem_seq_as_nat (as_seq h1 t2)) (felem_seq_as_nat (as_seq h1 t3))  (felem_seq_as_nat(as_seq h1 t4)) (felem_seq_as_nat(as_seq h1 t5)) (felem_seq_as_nat(as_seq h1 t6)) (felem_seq_as_nat(as_seq h1 t7)) (felem_seq_as_nat(as_seq h1 t8)) (felem_seq_as_nat (as_seq h1 o));
  
  admit();

    pop_frame() 

  
