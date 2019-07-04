module Hacl.Impl.SolinasReduction

open FStar.HyperStack.All
open FStar.HyperStack

open Lib.IntTypes 
open FStar.Math.Lemmas
open FStar.Math.Lib
open Lib.Buffer

open Hacl.Spec.P256.SolinasReduction
open Hacl.Impl.Gen
open Hacl.Spec.P256.Core

module Seq = Lib.Sequence

#reset-options "--z3refresh --z3rlimit  100"

inline_for_extraction noextract
val load_buffer: a0: uint64 -> a1: uint64 -> a2: uint64 -> a3: uint64 -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ 
      (
	let o = as_seq h1 o in  Seq.index o 0 == a0 /\ Seq.index o 1 == a1 /\ Seq.index o 2 == a2 /\ Seq.index o 3 == a3
      )
)
let load_buffer a0 a1 a2 a3 o = 
  upd o (size 0) a0;
  upd o (size 1) a1;
  upd o (size 2) a2;
  upd o (size 3) a3


val upl_zer_buffer: a0: uint32 -> a1: uint32 -> a2: uint32 -> a3: uint32 -> a4: uint32 -> 
  a5: uint32 -> a6: uint32 -> a7: uint32
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1)

let upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 o = 
    let b0 = store_high_low_u c1 c0 in 
    let b1 = store_high_low_u c3 c2 in 
    let b2 = store_high_low_u c5 c4 in 
    let b3 = store_high_low_u c7 c6 in 
    load_buffer b0 b1 b2 b3 o;
    reduction_prime_2prime_impl o o


val upl_fir_buffer: a0: uint32 -> a1: uint32 -> a2: uint32 -> a3: uint32 -> a4: uint32
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

let upl_fir_buffer c11 c12 c13 c14 c15 o = 
  let b0 = u64(0) in 
  let b1 = store_high_low_u c11 (u32 0) in 
  let b2 = store_high_low_u c13 c12 in 
  let b3 = store_high_low_u c15 c14 in 
  load_buffer b0 b1 b2 b3 o;
  reduction_prime_2prime_impl o o


val upl_sec_buffer: a0: uint32 -> a1: uint32 -> a2: uint32 -> a3: uint32 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

let upl_sec_buffer c12 c13 c14 c15 o = 
    let b0 = u64 (0) in 
    let b1 = store_high_low_u c12 (u32 0) in 
    let b2 = store_high_low_u c14 c13 in 
    let b3 = store_high_low_u (u32 0) c15 in
    load_buffer b0 b1 b2 b3 o;
    reduction_prime_2prime_impl o o


val upl_thi_buffer: a0: uint32 -> a1: uint32 -> a2: uint32 -> a3: uint32 -> a4: uint32 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

let upl_thi_buffer c8 c9 c10 c14 c15 o = 
   let b0 = store_high_low_u c9 c8 in 
   let b1 = store_high_low_u (u32 0) c10 in 
   let b2 = u64 0 in 
   let b3 = store_high_low_u c15 c14 in 
   load_buffer b0 b1 b2 b3 o;
   reduction_prime_2prime_impl o o


val upl_for_buffer: a0: uint32 -> a1: uint32 -> a2: uint32 -> a3: uint32 -> a4: uint32 -> 
  a5: uint32 -> a6: uint32 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

let upl_for_buffer c8 c9 c10 c11 c13 c14 c15 o = 
    let b0 = store_high_low_u c10 c9 in 
    let b1 = store_high_low_u c13 c11 in 
    let b2 = store_high_low_u c15 c14 in 
    let b3 = store_high_low_u c8 c13 in 
    load_buffer b0 b1 b2 b3 o;
    reduction_prime_2prime_impl o o


val upl_fif_buffer: a0: uint32 -> a1: uint32 -> a2: uint32 -> a3: uint32 -> a4: uint32 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

let upl_fif_buffer c8 c10 c11 c12 c13 o = 
    let b0 = store_high_low_u c12 c11 in 
    let b1 = store_high_low_u (u32 0) c13 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c10 c8 in 
    load_buffer b0 b1 b2 b3 o;
    reduction_prime_2prime_impl o o


val upl_six_buffer: a0: uint32 -> a1: uint32 -> a2: uint32 -> a3: uint32 -> a4: uint32 -> a5: uint32
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

let upl_six_buffer c9  c11 c12 c13 c14 c15 o = 
    let b0 = store_high_low_u c13 c12 in 
    let b1 = store_high_low_u c15 c14 in 
    let b2 = u64 0 in 
    let b3 = store_high_low_u c11 c9 in 
    load_buffer b0 b1 b2 b3 o;
    reduction_prime_2prime_impl o o


val upl_sev_buffer: a0: uint32 -> a1: uint32 -> a2: uint32 -> a3: uint32 -> a4: uint32 -> 
  a5: uint32 -> a6: uint32 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

let upl_sev_buffer c8 c9 c10 c12 c13 c14 c15 o = 
    let b0 = store_high_low_u c14 c13 in 
    let b1 = store_high_low_u c8 c15 in 
    let b2 = store_high_low_u c10 c9 in 
    let b3 = store_high_low_u c12 (u32 0) in 
    load_buffer b0 b1 b2 b3 o;
    reduction_prime_2prime_impl o o


val upl_eig_buffer: a0: uint32 -> a1: uint32 -> a2: uint32 -> a3: uint32 -> a4: uint32 -> 
  a5: uint32 -> a6: uint32 
  -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

let upl_eig_buffer c9 c10 c11 c12 c13 c14 c15 o = 
    let b0 = store_high_low_u c15 c14 in 
    let b1 = store_high_low_u c9 (u32 0) in 
    let b2 = store_high_low_u c11 c10 in 
    let b3 = store_high_low_u c13 (u32 0) in 
    load_buffer b0 b1 b2 b3 o;
    reduction_prime_2prime_impl o o

val solinas_reduction_impl: i: lbuffer uint64 (size 8) -> o: lbuffer uint64 (size 4) -> 
  Stack unit
    (requires fun h -> live h i /\ live h o)
    (ensures fun h0 _ h1 -> True)

let solinas_reduction_impl i o = 
  push_frame();
    let tempBuffer = create (size 36) (u64 0) in 
  let i0 = index i (size 0) in 
  let i1 = index i (size 1) in 
  let i2 = index i (size 2) in 
  let i3 = index i (size 3) in 
  let i4 = index i (size 4) in 
  let i5 = index i (size 5) in 
  let i6 = index i (size 6) in 
  let i7 = index i (size 7) in 

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
  
  upl_zer_buffer c0 c1 c2 c3 c4 c5 c6 c7 tempBuffer;
  upl_fir_buffer c8 c9 c10 c11 c12 tempBuffer;
  upl_sec_buffer c8 c9 c10 c11 tempBuffer;
  upl_thi_buffer c8 c9 c10 c11 c12  tempBuffer;
  upl_for_buffer c8 c9 c10 c11 c12 c13 c14  tempBuffer;
  upl_fif_buffer c8 c9 c10 c11 c12  tempBuffer;
  upl_six_buffer c8 c9 c10 c11 c12 c13  tempBuffer;
  upl_sev_buffer c8 c9 c10 c11 c12 c13 c14  tempBuffer;
  upl_eig_buffer c8 c9 c10 c11 c12 c13 c14  tempBuffer;

  let t0 = sub tempBuffer (size 0) (size 4) in 
  let t1 = sub tempBuffer (size 4) (size 4) in 
  let t2 = sub tempBuffer (size 8) (size 4) in 
  let t3 = sub tempBuffer (size 12) (size 4) in   
  let t4 = sub tempBuffer (size 16) (size 4) in   
  let t5 = sub tempBuffer (size 20) (size 4) in   
  let t6 = sub tempBuffer (size 24) (size 4) in   
  let t7 = sub tempBuffer (size 28) (size 4) in 
  let t8 = sub tempBuffer (size 32) (size 4) in 

  p256_double t0 o;
  p256_double t1 o;
  p256_add t0 t1 o;
  p256_add t2 o o;
  p256_add t3 o o;
  p256_add t4 o o;
  p256_sub o t5 o;
  p256_sub o t6 o;
  p256_sub o t7 o;
  p256_sub o t8 o;
 
    pop_frame()

  
