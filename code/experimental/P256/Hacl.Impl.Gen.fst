module Hacl.Impl.Gen

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Field64.Core
open Hacl.Spec.P256.Core
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
 
open FStar.Math.Lemmas


val add_carry: cin: uint64 -> x: uint64 -> y: uint64 -> result1: lbuffer uint64 (size 1) -> 
  Stack uint64 
    (requires fun h -> live h result1)
    (ensures fun h0 _ h1 -> True)

let add_carry cin x y result1 = 
  let res1 = x +. cin in 
  let c = if lt_u64 res1 cin then u64 1 else u64 0 in
  let res = res1 +. y in
  let c = if lt_u64 res res1 then c +. u64 1 else c in
  Lib.Buffer.upd result1 (size 0) res;
  c



val sub_borrow: cin: uint64 -> x: uint64 -> y: uint64 -> result1: lbuffer uint64 (size 1) -> 
  Stack uint64
    (requires fun h -> live h result1)
    (ensures fun h0 _ h1 -> True)

let sub_borrow cin x y result1 = 
  let open Hacl.Spec.Curve25519.Field64.Core in 
  let res = x -. y -. cin in
  let c =
    if eq_u64 cin (u64 1) then
      (if le_u64 x y then u64 1 else u64 0)
    else
      (if lt_u64 x y then u64 1 else u64 0) in
  Lib.Buffer.upd result1 (size 0) res;
  c



inline_for_extraction noextract
val shift_carry: x: uint64 -> cin: uint64{uint_v cin <=1} -> Tot (r: uint64)

let shift_carry x cin = 
  add (Lib.IntTypes.shift_left x (size 1)) cin



#set-options "--z3rlimit 500" 
val p256_add: arg1: felem -> arg2: felem ->  out: felem -> Stack unit 
  (requires (fun h0 ->  
    (let arg1_as_seq = as_seq h0 arg1 in let arg2_as_seq = as_seq h0 arg2 in 
    felem_seq_as_nat arg1_as_seq < prime /\ felem_seq_as_nat arg2_as_seq < prime /\
    live h0 out /\ live h0 arg1 /\ live h0 arg2))
  )
  (ensures (fun h0 _ h1 -> modifies1 out h0 h1 /\ 
    (let arg1_as_seq = as_seq h0 arg1 in let arg2_as_seq = as_seq h0 arg2 in 
    as_nat h1 out < prime (*/\ as_seq h1 out == felem_add_seq arg1_as_seq arg2_as_seq)) *) ))
  )

let p256_add arg1 arg2 out = 
    push_frame();
  let h0 = ST.get() in 

  let a0 = index arg1 (size 0) in 
  let a1 = index arg1 (size 1) in 
  let a2 = index arg1 (size 2) in 
  let a3 = index arg1 (size 3) in 

  let b0 = index arg2 (size 0) in 
  let b1 = index arg2 (size 1) in 
  let b2 = index arg2 (size 2) in 
  let b3 = index arg2 (size 3) in 

  let r0 = sub out (size 0) (size 1) in 
  let r1 = sub out (size 1) (size 1) in 
  let r2 = sub out (size 2) (size 1) in 
  let r3 = sub out (size 3) (size 1) in 
  
  let cc = add_carry (u64 0) a0 b0 r0 in 
  let cc = add_carry cc a1 b1 r1 in 
  let cc = add_carry cc a2 b2 r2 in 
  let cc = add_carry cc a3 b3 r3 in 

  let t = cc in 
  let cc = add_carry cc (index out (size 0)) (u64 0) r0 in 
  let cc = add_carry cc (index out (size 1)) ((u64 0) -. (t <<. (size 32))) r1 in 
  let cc = add_carry cc (index out (size 2)) ((u64 0) -. t) r2 in 
  let _  = add_carry cc (index out (size 3)) ((t <<. (size 32)) -. (t <<. (size 1))) r3 in 


  let h1 = ST.get() in 
  pop_frame();
  admit();
  (*assert(Lib.Sequence.equal (as_seq h1 out) (felem_add_seq (as_seq h0 arg1) (as_seq h0 arg2)));*)
  ()


val p256_sub: arg1: felem -> arg2: felem -> out: felem -> Stack unit 
  (requires 
    (fun h0 -> live h0 out /\ live h0 arg1 /\ live h0 arg2 /\ as_nat h0 arg1 < prime /\ as_nat h0 arg2 < prime))
  (ensures 
    (fun h0 _ h1 ->modifies1 out h0 h1 /\  as_nat h1 out < prime ))

let p256_sub arg1 arg2 out = 
  let h0 = ST.get() in 
        push_frame();
  let h0 = ST.get() in 

  let a0 = index arg1 (size 0) in 
  let a1 = index arg1 (size 1) in 
  let a2 = index arg1 (size 2) in 
  let a3 = index arg1 (size 3) in 

  let b0 = index arg2 (size 0) in 
  let b1 = index arg2 (size 1) in 
  let b2 = index arg2 (size 2) in 
  let b3 = index arg2 (size 3) in 

  let r0 = sub out (size 0) (size 1) in 
  let r1 = sub out (size 1) (size 1) in 
  let r2 = sub out (size 2) (size 1) in 
  let r3 = sub out (size 3) (size 1) in 


  let cc = sub_borrow (u64 0) a0 b0 r0 in 
  let cc = sub_borrow cc a1 b1 r1 in 
  let cc = sub_borrow cc a2 b2 r2 in 
  let cc = sub_borrow cc a3 b3 r3 in 

  let t = cc in 
  let cc = add_carry (u64 0) (index out (size 0)) ((u64 0) -. t) r0 in 
  let cc = add_carry cc (index out (size 1)) (((u64 0) -. t) >>. (size 32)) r1 in 
  let cc = add_carry cc (index out (size 2)) (u64 0) r2 in 
  let _ = add_carry cc (index out (size 3)) (t -. (t <<. (size 32))) r3 in 

admit();
    let h1 = ST.get() in 
    pop_frame();
  ()
