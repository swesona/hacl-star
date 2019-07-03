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
open Hacl.Spec.Curve25519.Field64.Core 
open Hacl.Impl.Curve25519.Field64.Core
open Hacl.Spec.Curve25519.Field64.Definition

open FStar.Math.Lemmas

module Seq = Lib.Sequence

inline_for_extraction
let prime_buffer: x: ilbuffer uint64 4ul = 
  createL_global p256_prime_list

open FStar.Mul

#reset-options "--z3refresh --z3rlimit 100"

val add_carry: cin: uint64 -> x: uint64 -> y: uint64 -> r: lbuffer uint64 (size 1) -> 
  Stack uint64 
    (requires fun h -> live h r)
    (ensures fun h0 c h1 -> modifies1 r h0 h1 /\ uint_v c <= 2 /\ 
      (
	let r = as_seq h1 r in 
	let r = Seq.index r 0 in 
	uint_v r + uint_v c * pow2 64 == uint_v x + uint_v y + uint_v cin)
    )

let add_carry cin x y result1 = 
  let res1 = x +. cin in 
  let c = if lt_u64 res1 cin then u64 1 else u64 0 in
  let res = res1 +. y in
  let c = if lt_u64 res res1 then c +. u64 1 else c in
  Lib.Buffer.upd result1 (size 0) res;
  c


val sub_borrow: cin: uint64{uint_v cin <= 1} -> x: uint64 -> y: uint64 -> r: lbuffer uint64 (size 1) -> 
  Stack uint64
    (requires fun h -> live h r)
    (ensures fun h0 c h1 -> modifies1 r h0 h1 /\ 
      (
	let r = as_seq h1 r in 
	let r = Seq.index r 0 in 
	v r - v c * pow2 64 == v x - v y - v cin)
)


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


val sub4: x: felem -> y: felem -> result: felem -> 
  Stack uint64
    (requires fun h -> live h result)
    (ensures fun h0 _ h1 -> True)

let sub4 x y result = 
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    let cc = sub_borrow (u64 0) x.(size 0) y.(size 0) r0 in 
    let cc = sub_borrow cc x.(size 1) y.(size 1) r1 in 
    let cc = sub_borrow cc x.(size 2) y.(size 2) r2 in 
    let cc = sub_borrow cc x.(size 3) y.(size 3) r3 in 
    cc


val cmovznz4: cin: uint64 -> x: felem -> y: felem -> result: felem ->
  Stack unit
    (requires fun h -> live h result)
    (ensures fun h0 _ h1 -> True)

let cmovznz4 cin x y r = 
  let mask = neq_mask cin (u64 0) in 
  let r0 = logor (logand y.(size 0) mask) (logand x.(size 0) (lognot mask)) in 
  let r1 = logor (logand y.(size 1) mask) (logand x.(size 1) (lognot mask)) in 
  let r2 = logor (logand y.(size 2) mask) (logand x.(size 2) (lognot mask)) in 
  let r3 = logor (logand y.(size 3) mask) (logand x.(size 3) (lognot mask)) in 
  upd r (size 0) r0;
  upd r (size 1) r1;
  upd r (size 2) r2;
  upd r (size 3) r3


val reduction_prime_2prime_impl: x: felem -> result: felem -> 
  Stack unit
    (requires fun h -> live h result)
    (ensures fun h0 _ h1 -> True)

let reduction_prime_2prime_impl x result = 
  push_frame();
  let tempBuffer = create (size 4) (u64 0) in 
    let c = sub4 x prime_buffer tempBuffer in 
    cmovznz4 c x tempBuffer result;
  pop_frame()  



inline_for_extraction noextract
val shift_carry: x: uint64 -> cin: uint64{uint_v cin <=1} -> Tot (r: uint64)

let shift_carry x cin = 
  add (Lib.IntTypes.shift_left x (size 1)) cin


val shift_256_impl: i: felem -> o: lbuffer uint64 (size 8) -> 
  Stack unit 
    (requires fun h -> True)
    (ensures fun h0 _ h1 -> True)

let shift_256_impl i o = 
  upd o (size 4) i.(size 0);
  upd o (size 5) i.(size 1);
  upd o (size 6) i.(size 2);
  upd o (size 7) i.(size 3)


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

  let r0 = sub out (size 0) (size 1) in 
  let r1 = sub out (size 1) (size 1) in 
  let r2 = sub out (size 2) (size 1) in 
  let r3 = sub out (size 3) (size 1) in 
  
  let cc = add_carry (u64 0) arg1.(0ul) arg2.(0ul) r0 in 
  let cc = add_carry cc arg1.(1ul) arg2.(1ul)  r1 in 
  let cc = add_carry cc arg1.(2ul) arg2.(2ul)  r2 in 
  let cc = add_carry cc arg1.(3ul) arg2.(3ul)  r3 in 

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


#set-options "--z3rlimit 500" 
val p256_double: arg1: felem ->  out: felem -> Stack unit 
  (requires (fun h0 ->  True)
  )
  (ensures (fun h0 _ h1 -> True))

let p256_double arg1 out = 
    push_frame();
  let h0 = ST.get() in 

  let r0 = sub out (size 0) (size 1) in 
  let r1 = sub out (size 1) (size 1) in 
  let r2 = sub out (size 2) (size 1) in 
  let r3 = sub out (size 3) (size 1) in 
  
  let cc = add_carry (u64 0) arg1.(0ul) arg1.(0ul) r0 in 
  let cc = add_carry cc arg1.(1ul) arg1.(1ul)  r1 in 
  let cc = add_carry cc arg1.(2ul) arg1.(2ul)  r2 in 
  let cc = add_carry cc arg1.(3ul) arg1.(3ul)  r3 in 

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

  let r0 = sub out (size 0) (size 1) in 
  let r1 = sub out (size 1) (size 1) in 
  let r2 = sub out (size 2) (size 1) in 
  let r3 = sub out (size 3) (size 1) in 


  let cc = sub_borrow (u64 0) arg1.(0ul) arg2.(0ul)  r0 in 
  let cc = sub_borrow cc arg1.(1ul) arg2.(1ul)  r1 in 
  let cc = sub_borrow cc arg1.(2ul) arg2.(2ul)  r2 in 
  let cc = sub_borrow cc arg1.(3ul) arg2.(3ul)  r3 in 

  let t = cc in 
  let cc = add_carry (u64 0) (index out (size 0)) ((u64 0) -. t) r0 in 
  let cc = add_carry cc (index out (size 1)) (((u64 0) -. t) >>. (size 32)) r1 in 
  let cc = add_carry cc (index out (size 2)) (u64 0) r2 in 
  let _ = add_carry cc (index out (size 3)) (t -. (t <<. (size 32))) r3 in 

admit();
    let h1 = ST.get() in 
    pop_frame();
  ()



val mm_round1: a: felem -> t4: uint64 -> tempBuffer: lbuffer uint64 (size 16) -> 
  Stack uint64
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let mm_round1 a t4 tempBuffer =  
  let open Lib.Buffer in 
  push_frame();

  let tempBufferLocal = create (size 2) (u64 0) in 
  let temp_zl = sub tempBufferLocal (size 0) (size 1) in 
  let temp_zh = sub tempBufferLocal (size 1) (size 1) in 

  let x = a.(1ul) in 

  let t0_b = sub tempBuffer (size 0) (size 1) in 
  let t1_b = sub tempBuffer (size 1) (size 1) in 
  let t2_b = sub tempBuffer (size 2) (size 1) in 
  let t3_b = sub tempBuffer (size 3) (size 1) in 

  let k = add_carry (u64 0) tempBuffer.(4ul) tempBuffer.(0ul) temp_zl in 
  let f = index temp_zl (size 0) in 
  let _ = add_carry k tempBuffer.(5ul) (u64 0) t0_b in

  let zl, zh = mul64 x x in 
  let k = add_carry (u64 0) zl tempBuffer.(0ul) temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) tempBuffer.(1ul) t0_b in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) t1_b in

  let zl, zh = mul64 x a.(2ul) in 
  upd tempBuffer (size 10) zl;
  upd tempBuffer (size 11) zh;

  let k = add_carry (u64 0) zl tempBuffer.(1ul) temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) tempBuffer.(2ul) t1_b in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) t2_b in

  let zl, zh = mul64 x a.(3ul) in 
  upd tempBuffer (size 12) zl;
  upd tempBuffer (size 13) zh;

  let k = add_carry (u64 0) zl tempBuffer.(2ul) temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) tempBuffer.(3ul) t2_b in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) t3_b in
  
  let t4 = add_carry (u64 0) tempBuffer.(3ul) t4 t3_b in 
  let k = add_carry (u64 0) tempBuffer.(0ul) (f <<. (size 32)) t0_b in 
  let k = add_carry k tempBuffer.(1ul) (f >>. (size 32)) t1_b in 

  let m = sub_borrow (u64 0) f (f <<. (size 32)) temp_zl in 
  let _ = sub_borrow m f (f >>. (size 32)) temp_zh in 

  let k = add_carry k tempBuffer.(2ul) (index temp_zl (size 0)) t2_b in 
  let k = add_carry k tempBuffer.(3ul) (index temp_zh (size 0)) t3_b in 
  let _ = add_carry k t4 (u64 0) temp_zl in 
  let t4 = index temp_zl (size 0) in 


   pop_frame();
   admit();
   t4


val mm_round2: a: felem -> t4: uint64 -> result: felem -> 
  Stack uint64
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let mm_round2 a t4 tempBuffer =  
  let open Lib.Buffer in 
  push_frame();

  let tempBufferLocal = create (size 2) (u64 0) in 
  let temp_zl = sub tempBufferLocal (size 0) (size 1) in 
  let temp_zh = sub tempBufferLocal (size 1) (size 1) in 
  let temp_zl_el = index temp_zl (size 0) in 
  let temp_zh_el = index temp_zh (size 0) in 

  let x = index a (size 2) in 
  let a3 = index a (size 3) in 
  
  let t0 = index tempBuffer (size 0) in 
  let t1 = index tempBuffer (size 1) in 
  let t2 = index tempBuffer (size 2) in 
  let t3 = index tempBuffer (size 3) in 

  let t0_b = sub tempBuffer (size 0) (size 1) in 
  let t1_b = sub tempBuffer (size 1) (size 1) in 
  let t2_b = sub tempBuffer (size 2) (size 1) in 
  let t3_b = sub tempBuffer (size 3) (size 1) in 

  let zl = index tempBuffer (size 6) in 
  let zh = index tempBuffer (size 7) in
  
  let k = add_carry (u64 0) zl t0 temp_zl in 
  let f = index temp_zl (size 0) in 
  let _ = add_carry k zh (u64 0) t0_b in

  let zl = index tempBuffer (size 10) in 
  let zh = index tempBuffer (size 11) in


    let t0 = index t0_b (size 0) in 
  let k = add_carry (u64 0) zl t0 temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) t1 t0_b in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) t1_b in


  let zl, zh = mul64 x x in 
     let t1 = index t1_b (size 0) in         
  let k = add_carry (u64 0) zl t1 temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) t2 t1_b in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) t2_b in


  let zl, zh = mul64 x a3 in 
  upd tempBuffer (size 14) zl;
  upd tempBuffer (size 15) zh;


     let t2 = index t2_b (size 0) in 
  let k = add_carry (u64 0) zl t2 temp_zl in 
   let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) t3 t2_b in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) t3_b in

    let t3 = index t3_b (size 0) in 
    let t0 = index t0_b (size 0) in 
    let t1 = index t1_b (size 0) in 
  
  let t4 = add_carry (u64 0) t3 t4 t3_b in 
  let k = add_carry (u64 0) t0 (f <<. (size 32)) t0_b in 
  let k = add_carry k t1 (f >>. (size 32)) t1_b in 


  let m = sub_borrow (u64 0) f (f <<. (size 32)) temp_zl in 
  let _ = sub_borrow m f (f >>. (size 32)) temp_zh in 
    let t2 = index t2_b (size 0) in 
    let t3 = index t3_b (size 0) in 
  
  let k = add_carry k t2 (index temp_zl (size 0)) t2_b in 
  let k = add_carry k t3 (index temp_zh (size 0)) t3_b in 
  let _ = add_carry k t4 (u64 0) temp_zl in 
  let t4 = index temp_zl (size 0) in 


   pop_frame();
   admit();
   t4


val mm_round3: a: felem -> t4: uint64 -> tempBuffer: lbuffer uint64 (size 16) -> 
  Stack uint64
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)


let mm_round3 a t4 tempBuffer =  
  let open Lib.Buffer in 
  push_frame();

  let tempBufferLocal = create (size 2) (u64 0) in 
  let temp_zl = sub tempBufferLocal (size 0) (size 1) in 
  let temp_zh = sub tempBufferLocal (size 1) (size 1) in 
  let temp_zl_el = index temp_zl (size 0) in 
  let temp_zh_el = index temp_zh (size 0) in 

  let x = index a (size 3) in 

  let t0 = index tempBuffer (size 0) in 
  let t1 = index tempBuffer (size 1) in 
  let t2 = index tempBuffer (size 2) in 
  let t3 = index tempBuffer (size 3) in 

  let t0_b = sub tempBuffer (size 0) (size 1) in 
  let t1_b = sub tempBuffer (size 1) (size 1) in 
  let t2_b = sub tempBuffer (size 2) (size 1) in 
  let t3_b = sub tempBuffer (size 3) (size 1) in 

  let zl = index tempBuffer (size 8) in 
  let zh = index tempBuffer (size 9) in 


  let k = add_carry (u64 0) zl t0 temp_zl in 
  let f = index temp_zl (size 0) in 
  let _ = add_carry k zh (u64 0) t0_b in


  let zl = index tempBuffer (size 12) in 
  let zh = index tempBuffer (size 13) in 
  

    let t0 = index t0_b (size 0) in 
  let k = add_carry (u64 0) zl t0 temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) t1 t0_b in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) t1_b in


  let zl = index tempBuffer (size 14) in 
  let zh = index tempBuffer (size 15) in 
  
     let t1 = index t1_b (size 0) in         
  let k = add_carry (u64 0) zl t1 temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) t2 t1_b in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) t2_b in


  let zl, zh = mul64 x x in 
     let t2 = index t2_b (size 0) in 
  let k = add_carry (u64 0) zl t2 temp_zl in 
   let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) t3 t2_b in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) t3_b in

    let t3 = index t3_b (size 0) in 
    let t0 = index t0_b (size 0) in 
    let t1 = index t1_b (size 0) in 
  
  let t4 = add_carry (u64 0) t3 t4 t3_b in 
  let k = add_carry (u64 0) t0 (f <<. (size 32)) t0_b in 
  let k = add_carry k t1 (f >>. (size 32)) t1_b in 


  let m = sub_borrow (u64 0) f (f <<. (size 32)) temp_zl in 
  let _ = sub_borrow m f (f >>. (size 32)) temp_zh in 
    let t2 = index t2_b (size 0) in 
    let t3 = index t3_b (size 0) in 
  
  let k = add_carry k t2 (index temp_zl (size 0)) t2_b in 
  let k = add_carry k t3 (index temp_zh (size 0)) t3_b in 
  let _ = add_carry k t4 (u64 0) temp_zl in 
  let t4 = index temp_zl (size 0) in 


   pop_frame();
   admit();
   t4





   
val montgomery_square: a: felem ->  tempBuffer: lbuffer uint64 (size 16)->  Stack unit
  (requires (fun h ->  True)) 
  (ensures (fun h0 _ h1 -> True))



let montgomery_square a result = 
  let open Lib.Buffer in 

    push_frame();
    let tempBuffer = create (size 20) (u64 0) in 
      let temp_zl = sub tempBuffer (size 0) (size 1) in 
      let temp_zh = sub tempBuffer (size 1) (size 1) in 
      let t0_buffer = sub tempBuffer (size 2) (size 1) in 
      let t1_buffer = sub tempBuffer (size 3) (size 1) in 
      let t2_buffer = sub tempBuffer (size 4) (size 1) in 
      let t3_buffer = sub tempBuffer (size 5) (size 1) in 
      let t_buffer = sub tempBuffer (size 2) (size 18) in 

  let x  = index a (size 0) in 
  let a1 = index a (size 1) in 
  let a2 = index a (size 2) in 
  let a3 = index a (size 3) in 

  let f, t0 = mul64 x x in  


  let zl, zh = mul64 a1 x in 
  upd tempBuffer (size 6) zl;
  upd tempBuffer (size 7) zh;

  let k = add_carry (u64 0)  zl t0 temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in  
  let k = add_carry (u64 0) (index temp_zl (size 0)) (f <<. (size 32)) temp_zl in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) temp_zh in 
  let t0 = index temp_zl (size 0) in 
  let t1 = index temp_zh (size 0) in 


  let zl, zh = mul64 a2 x in 
  upd tempBuffer (size 8) zl;
  upd tempBuffer (size 9) zh;

  let k = add_carry  (u64 0)  zl t1 temp_zl  in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry  (u64 0) (index temp_zl (size 0)) (f >>. (size 32)) temp_zl in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) temp_zh in 
  let t1 = (index temp_zl (size 0)) in 
  let t2 = (index temp_zh (size 0)) in 


  let zl, zh = mul64 a3 x in 
  upd tempBuffer (size 10) zl;
  upd tempBuffer (size 11) zh;
  

  let k = add_carry (u64 0) zl t2 temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) f temp_zl in 
  let _  = add_carry k (index temp_zh (size 0)) (u64 0) temp_zh in 
  let t2 = index temp_zl (size 0) in 
  let t3 = index temp_zh (size 0) in 

  let t4 = add_carry (u64 0) t3 f temp_zl in 
  let k  = sub_borrow (u64 0) t2 (f <<. (size 32)) temp_zh in 
    let t3 = index temp_zl (size 0) in 
    let t2 = index temp_zh (size 0) in 
  let k = sub_borrow k t3 (f >>. (size 32)) temp_zl in 
    let t3 = index temp_zl (size 0) in 
  let _ = sub_borrow k t4 (u64 0) temp_zh in  
    let t4 = (index temp_zh (size 0)) in  

  upd t_buffer (size 0) t0;
  upd t_buffer (size 1) t1; 
  upd t_buffer (size 2) t2;
  upd t_buffer (size 3) t3;

  let t4 = mm_round1 a t4 t_buffer in 
  let t4 = mm_round2 a t4 t_buffer in 
  let t4 = mm_round3 a t4 t_buffer in 

  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in  
  let r2 = sub result (size 2) (size 1) in 
  let r3 = sub result (size 3) (size 1) in 

  let t0 = index t_buffer (size 0) in 
  let t1 = index t_buffer (size 1) in 
  let t2 = index t_buffer (size 2) in 
  let t3 = index t_buffer (size 3) in 


  let k = add_carry  (u64 0) t0 t4 r0 in 
  let k = add_carry k t1 ((u64 0) -.(t4 <<. (size 32))) r1 in 
  let k = add_carry k t2 ((u64 0) -. t4) r2 in 
  let _ = add_carry k t3 ((t4 <<. (size 32)) -. (t4 <<. (size 1))) r3 in

  admit();
  pop_frame() 

