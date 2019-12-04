module Hacl.Impl.LowLevel

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Basic
open Hacl.Spec.ECDSA

open FStar.Math.Lemmas
open FStar.Mul

open FStar.Tactics
open FStar.Tactics.Canon 

#reset-options "--z3rlimit 100"

inline_for_extraction noextract
val load_buffer8: 
  a0: uint64 -> a1: uint64 -> 
  a2: uint64 -> a3: uint64 -> 
  a4: uint64 -> a5: uint64 -> 
  a6: uint64 -> a7: uint64 ->  
  o: lbuffer uint64 (size 8) -> 
  Stack unit
    (requires fun h -> live h o)
    (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ wide_as_nat h1 o == wide_as_nat4 (a0, a1, a2, a3, a4, a5, a6, a7))


let load_buffer8 a0 a1 a2 a3 a4 a5 a6 a7  o = 
    let h0 = ST.get() in 
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (5 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 (7 * 64));

  upd o (size 0) a0;
  upd o (size 1) a1;
  upd o (size 2) a2;
  upd o (size 3) a3;
  
  upd o (size 4) a4;
  upd o (size 5) a5;
  upd o (size 6) a6;
  upd o (size 7) a7


val add_carry: cin: uint64 -> x: uint64 -> y: uint64 -> r: lbuffer uint64 (size 1) -> 
  Stack uint64 
    (requires fun h -> live h r) 
    (ensures fun h0 c h1 -> modifies1 r h0 h1 /\ uint_v c <= 2 /\ 
      (
	let r = Seq.index (as_seq h1 r) 0 in 
	uint_v r + uint_v c * pow2 64 == uint_v x + uint_v y + uint_v cin)
    )

let add_carry cin x y result1 = 
  let res1 = x +. cin in 
  let c = if lt_u64 res1 cin then u64 1 else u64 0 in
  let res = res1 +. y in
  let c = if lt_u64 res res1 then c +. u64 1 else c in
  Lib.Buffer.upd result1 (size 0) res;
  c


val add4: x: felem -> y: felem -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ 
      as_nat h1 result + v c * pow2 256 == as_nat h0 x + as_nat h0 y)   

let add4 x y result =    
  let h0 = ST.get() in
  
  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 
  let r3 = sub result (size 3) (size 1) in 
    
  let cc = add_carry (u64 0) x.(0ul) y.(0ul) r0 in 
  let cc = add_carry cc x.(1ul) y.(1ul) r1 in 
  let cc = add_carry cc x.(2ul) y.(2ul) r2 in 
  let cc = add_carry cc x.(3ul) y.(3ul) r3 in   
  
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);   
    
  cc


val add4_with_carry: c: uint64 ->  x: felem -> y: felem -> result: felem -> 
  Stack uint64
    (requires fun h -> uint_v c <= 1 /\ live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ 
      eq_or_disjoint y result)
    (ensures fun h0 carry h1 -> modifies (loc result) h0 h1 /\ uint_v carry <= 1 /\ 
      as_nat h1 result + v carry * pow2 256 == as_nat h0 x + as_nat h0 y + uint_v c)   

let add4_with_carry c x y result =    
    let h0 = ST.get() in
  
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 
    
    let cc = add_carry c x.(0ul) y.(0ul) r0 in 
    let cc = add_carry cc x.(1ul) y.(1ul) r1 in 
    let cc = add_carry cc x.(2ul) y.(2ul) r2 in 
    let cc = add_carry cc x.(3ul) y.(3ul) r3 in   

      assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
      assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
      assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);
    
    cc


val add8: x: widefelem -> y: widefelem -> result: widefelem -> Stack uint64 
  (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\ 
    wide_as_nat h1 result + v c * pow2 512 == wide_as_nat h0 x + wide_as_nat h0 y)

let add8 x y result = 
    let a0 = sub x (size 0) (size 4) in 
    let a1 = sub x (size 4) (size 4) in 
    let b0 = sub y (size 0) (size 4) in 
    let b1 = sub y (size 4) (size 4) in 

    let c0 = sub result (size 0) (size 4) in 
    let c1 = sub result (size 4) (size 4) in 

    let carry0 = add4 a0 b0 c0 in
    let carry1 = add4_with_carry carry0 a1 b1 c1 in 
      
      assert_norm (pow2 256 * pow2 256 = pow2 512); 
    
    carry1


val add4_variables: x: felem -> cin: uint64 {uint_v cin <=1} ->  y0: uint64 -> y1: uint64 -> y2: uint64 -> y3: uint64 -> 
  result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h result /\ eq_or_disjoint x result)
    (ensures fun h0 c h1 -> modifies (loc result) h0 h1 /\ v c <= 1 /\  
      as_nat h1 result  + uint_v c * pow2 256 == as_nat h0 x + uint_v y0 + uint_v y1 * pow2 64 + uint_v y2 * pow2 128 + uint_v y3 * pow2 192 + uint_v cin)   

let add4_variables x cin y0 y1 y2 y3 result = 
    let h0 = ST.get() in 
    
    let r0 = sub result (size 0) (size 1) in      
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    let cc = add_carry cin x.(0ul) y0 r0 in 
    let cc = add_carry cc x.(1ul) y1 r1 in 
    let cc = add_carry cc x.(2ul) y2 r2 in 
    let cc = add_carry cc x.(3ul) y3 r3 in 
      
    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);
    cc


val sub_borrow: cin: uint64{uint_v cin <= 1} -> x: uint64 -> y: uint64 -> r: lbuffer uint64 (size 1) -> 
  Stack uint64
    (requires fun h -> live h r)
    (ensures fun h0 c h1 -> modifies1 r h0 h1 /\ 
      (let r = Seq.index (as_seq h1 r) 0 in v r - v c * pow2 64 == v x - v y - v cin))

let sub_borrow cin x y result1 = 
  let res = x -. y -. cin in
  let c =
    if eq_u64 cin (u64 1) then
      (if le_u64 x y then u64 1 else u64 0)
    else
      (if lt_u64 x y then u64 1 else u64 0) in
  Lib.Buffer.upd result1 (size 0) res;
  c


val sub4_il: x: felem -> y: ilbuffer uint64 (size 4) -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ disjoint y result)
    (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ v c <= 1 /\
      (
	let y = as_seq h0 y in 
 	as_nat h1 result - v c * pow2 256 == as_nat h0 x  - felem_seq_as_nat y /\
	(if uint_v c = 0 then as_nat h0 x >= felem_seq_as_nat y else as_nat h0 x < felem_seq_as_nat y)
      )
   )

let sub4_il x y result = 
    let r0 = sub result (size 0) (size 1) in 
    let r1 = sub result (size 1) (size 1) in 
    let r2 = sub result (size 2) (size 1) in 
    let r3 = sub result (size 3) (size 1) in 

    let cc = sub_borrow (u64 0) x.(size 0) y.(size 0) r0 in 
    let cc = sub_borrow cc x.(size 1) y.(size 1) r1 in 
    let cc = sub_borrow cc x.(size 2) y.(size 2) r2 in 
    let cc = sub_borrow cc x.(size 3) y.(size 3) r3 in 
    
    cc


val sub4: x: felem -> y:felem -> result: felem -> 
  Stack uint64
    (requires fun h -> live h x /\ live h y /\ live h result /\ eq_or_disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 c h1 -> modifies1 result h0 h1 /\ v c <= 1 /\ as_nat h1 result - v c * pow2 256 == as_nat h0 x - as_nat h0 y)

let sub4 x y result = 
  let h0 = ST.get() in 
	
  let r0 = sub result (size 0) (size 1) in 
  let r1 = sub result (size 1) (size 1) in 
  let r2 = sub result (size 2) (size 1) in 
  let r3 = sub result (size 3) (size 1) in 
      
  let cc = sub_borrow (u64 0) x.(size 0) y.(size 0) r0 in 
  let cc = sub_borrow cc x.(size 1) y.(size 1) r1 in 
  let cc = sub_borrow cc x.(size 2) y.(size 2) r2 in 
  let cc = sub_borrow cc x.(size 3) y.(size 3) r3 in 
    
    assert(let r1_0 = as_seq h0 r1 in let r0_ = as_seq h0 result in Seq.index r0_ 1 == Seq.index r1_0 0);
    assert(let r2_0 = as_seq h0 r2 in let r0_ = as_seq h0 result in Seq.index r0_ 2 == Seq.index r2_0 0);
    assert(let r3_0 = as_seq h0 r3 in let r0_ = as_seq h0 result in Seq.index r0_ 3 == Seq.index r3_0 0);
    
  cc


val mul64: x: uint64 -> y: uint64 -> result: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) ->
  Stack unit
    (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> modifies (loc result |+| loc temp) h0 h1 /\ 
    (
      let h0 = Seq.index (as_seq h1 temp) 0 in 
      let result = Seq.index (as_seq h1 result) 0 in 
      uint_v result + uint_v h0 * pow2 64 = uint_v x * uint_v y     
      )
    )

let mul64 x y result temp = 
  let res = mul64_wide x y in 
  let l0, h0 = to_u64 res, to_u64 (res >>. 64ul) in 
  upd result (size 0) l0;
  upd temp (size 0) h0


val mult64_0: x: felem -> u: uint64 -> result:  lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack unit 
  (requires fun h -> live h x /\ live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> 
    let result_ = Seq.index (as_seq h1 result) 0 in 
    let c = Seq.index (as_seq h1 temp) 0 in 
    let f0 = Seq.index (as_seq h0 x) 0 in 
    uint_v result_ + uint_v c * pow2 64 = uint_v f0 * uint_v u /\ modifies (loc result |+| loc temp) h0 h1)

let mult64_0 x u result temp = 
  let f0 = index x (size 0) in 
  mul64 f0 u result temp

 val mult64_0il: x: ilbuffer uint64 (size 4) -> u: uint64 -> result:  lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack unit 
  (requires fun h -> live h x /\ live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 _ h1 -> 
    let result_ = Seq.index (as_seq h1 result) 0 in 
    let c = Seq.index (as_seq h1 temp) 0 in 
    let f0 = Seq.index (as_seq h0 x) 0 in 
    uint_v result_ + uint_v c * pow2 64 = uint_v f0 * uint_v u /\ modifies (loc result |+| loc temp) h0 h1)


let mult64_0il x u result temp = 
  let f0 = index x (size 0) in 
  mul64 f0 u result temp


val mult64_c: x: uint64 -> u: uint64 -> cin: uint64 -> result: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 1) -> Stack uint64 
  (requires fun h -> live h result /\ live h temp /\ disjoint result temp)
  (ensures fun h0 c2 h1 -> modifies (loc result |+| loc temp) h0 h1 /\ uint_v c2 <= 2 /\
    (
      let r = Seq.index (as_seq h1 result) 0 in 
      let h1 = Seq.index (as_seq h1 temp) 0 in 
      let h0 = Seq.index (as_seq h0 temp) 0 in 
      uint_v r + uint_v c2 * pow2 64 == uint_v x * uint_v u - uint_v h1 * pow2 64 + uint_v h0 + uint_v cin)
)

let mult64_c x u cin result temp = 
  let h = index temp (size 0) in 
  mul64 x u result temp;
  let l = index result (size 0) in     
  add_carry cin l h result



#reset-options "--z3rlimit 200"

val l1: o0: nat -> o1: nat -> o2: nat -> o3: nat -> f0: nat  ->  f1: nat -> f2: nat -> 
  f3: nat {f0 + f1 * pow2 64 + f2 * pow2 128  + f3 * pow2 192 < pow2 256} -> 
  u: nat {u < pow2 64} -> h2: nat -> c1: nat -> c2: nat -> c3: nat -> h3: nat -> h4: nat ->
  Lemma
  (requires (
    h2 * pow2 64 * pow2 64 +  o0 + o1 * pow2 64 + c1 * pow2 64 * pow2 64 ==  f0 * u + f1 * u * pow2 64 /\
    o2 + c2 * pow2 64 + h3 * pow2 64 - h2 - c1  == f2 * u /\
    o3 + c3 * pow2 64 + h4 * pow2 64 - h3 - c2 == f3 * u)
  )
  (ensures 
    (o0 + o1 * pow2 64 + o2 * pow2 128 +  o3 * pow2 192 + (c3 + h4) * pow2 256  == (f0  + f1 * pow2 64 + f2  * pow2 128  + f3 * pow2 192) * u /\
    f0 * u + f1 * u * pow2 64 + f2 * u * pow2 128  + f3 * u * pow2 192 < pow2 320 /\
  (c3 + h4) < pow2 64)
)
    

let l1 o0 o1 o2 o3 f0 f1 f2 f3 u h2 c1 c2 c3 h3 h4 = 
  assert_norm (pow2 64 * pow2 64 = pow2 128);
  assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);  
  assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 320);  
  assert(h2 * pow2 64 * pow2 64 +  o0 + o1 * pow2 64 + c1 * pow2 64 * pow2 64 + o2 + c2 * pow2 64 + h3 * pow2 64 - h2 - c1 + 
    o3 + c3 * pow2 64 + h4 * pow2 64 - h3 - c2 == f0 * u + f1 * u * pow2 64 + f2 * u  + f3 * u);
  assert(h2 * pow2 64 * pow2 64 +  o0 + o1 * pow2 64 + c1 * pow2 64 * pow2 64 + o2 * pow2 128 + c2 * pow2 64 * pow2 128 + h3 * pow2 64 * pow2 128 - h2 * pow2 128- c1 * pow2 128 + o3 * pow2 192 + c3 * pow2 64 * pow2 192 + h4 * pow2 64 * pow2 192 - h3 * pow2 192 - c2 * pow2 192 == f0 * u + f1 * u * pow2 64 + f2 * u * pow2 128  + f3 * u * pow2 192);
  assert(o0 + o1 * pow2 64 + o2 * pow2 128 +  o3 * pow2 192 + (c3 + h4) * pow2 256  == f0 * u + f1 * u * pow2 64 + f2 * u * pow2 128  + f3 * u * pow2 192);
  assert(f0 * u + f1 * u * pow2 64 + f2 * u * pow2 128  + f3 * u * pow2 192 == (f0 + f1 * pow2 64 + f2 * pow2 128 + f3 * pow2 192) * u);
  mul_lemma_3  (f0 + f1 * pow2 64 + f2 * pow2 128 + f3 * pow2 192) (pow2 256) u (pow2 64);
  assert((f0 + f1 * pow2 64 + f2 * pow2 128 + f3 * pow2 192) * u < pow2 320);
  assert((c3 + h4) * pow2 256 < pow2 320);
  assert(c3 + h4 < pow2 64)


val mul1_il: f:  ilbuffer uint64 (size 4) -> u: uint64 -> result: lbuffer uint64 (size 4) -> Stack uint64
  (requires fun h -> live h result /\ live h f)
  (ensures fun h0 c h1 -> 
    modifies (loc result) h0 h1 /\ 
    as_nat_il h0 f * uint_v u = uint_v c * pow2 256 + as_nat h1 result /\ 
    as_nat_il h0 f * uint_v u < pow2 320 /\
    uint_v c < pow2 64 - 1 
  )


let mul1_il f u result = 
  push_frame();

    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);  
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 320); 

  let temp = create (size 1) (u64 0) in 

  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 
    
  let o0 = sub result (size 0) (size 1) in 
  let o1 = sub result (size 1) (size 1) in 
  let o2 = sub result (size 2) (size 1) in 
  let o3 = sub result (size 3) (size 1) in 
    
    let h0 = ST.get() in 
  mult64_0il f u o0 temp;
    let h1 = ST.get() in 
  let c1 = mult64_c f1 u (u64 0) o1 temp in 
    let h2 = ST.get() in 
  let c2 = mult64_c f2 u c1 o2 temp in 
    let h3 = ST.get() in 
  let c3 = mult64_c f3 u c2 o3 temp in 
    let h4 = ST.get() in 
  let temp0 = index temp (size 0) in 
    l1 (uint_v(Seq.index (as_seq h1 o0) 0)) (uint_v (Seq.index (as_seq h2 o1) 0)) (uint_v (Seq.index (as_seq h3 o2) 0)) (uint_v (Seq.index (as_seq h4 o3) 0)) (uint_v f0) (uint_v f1) (uint_v f2) (uint_v f3) (uint_v u) (uint_v (Seq.index (as_seq h2 temp) 0)) (uint_v c1) (uint_v c2) (uint_v c3) (uint_v (Seq.index (as_seq h3 temp) 0)) (uint_v temp0); 
    
  mul_lemma_4 (as_nat_il h0 f) (uint_v u) (pow2 256 - 1) (pow2 64 - 1);
  assert_norm((pow2 256 - 1) * (pow2 64 - 1) == pow2 320 - pow2 256 - pow2 64 + 1);
  assert_norm((pow2 320 - pow2 256) / pow2 256 == pow2 64 - 1);

  pop_frame();  
  c3 +! temp0




val mul1: f:  lbuffer uint64 (size 4) -> u: uint64 -> result: lbuffer uint64 (size 4) -> Stack uint64
  (requires fun h -> live h result /\ live h f)
  (ensures fun h0 c h1 -> 
    modifies (loc result) h0 h1 /\ 
    as_nat h0 f * uint_v u = uint_v c * pow2 256 + as_nat h1 result /\ 
    as_nat h0 f * uint_v u < pow2 320 /\
    uint_v c < pow2 64 - 1
  )


let mul1 f u result = 
  push_frame();

    assert_norm (pow2 64 * pow2 64 = pow2 128);
    assert_norm (pow2 64 * pow2 64 * pow2 64 = pow2 192);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);  
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 320); 

  let temp = create (size 1) (u64 0) in 

  let f0 = index f (size 0) in 
  let f1 = index f (size 1) in 
  let f2 = index f (size 2) in 
  let f3 = index f (size 3) in 
    
  let o0 = sub result (size 0) (size 1) in 
  let o1 = sub result (size 1) (size 1) in 
  let o2 = sub result (size 2) (size 1) in 
  let o3 = sub result (size 3) (size 1) in 
    
    let h0 = ST.get() in 
  mult64_0 f u o0 temp;
    let h1 = ST.get() in 
  let c1 = mult64_c f1 u (u64 0) o1 temp in 
    let h2 = ST.get() in 
  let c2 = mult64_c f2 u c1 o2 temp in 
    let h3 = ST.get() in 
  let c3 = mult64_c f3 u c2 o3 temp in 
    let h4 = ST.get() in 
  let temp0 = index temp (size 0) in 
    l1 (uint_v(Seq.index (as_seq h1 o0) 0)) (uint_v (Seq.index (as_seq h2 o1) 0)) (uint_v (Seq.index (as_seq h3 o2) 0)) (uint_v (Seq.index (as_seq h4 o3) 0)) (uint_v f0) (uint_v f1) (uint_v f2) (uint_v f3) (uint_v u) (uint_v (Seq.index (as_seq h2 temp) 0)) (uint_v c1) (uint_v c2) (uint_v c3) (uint_v (Seq.index (as_seq h3 temp) 0)) (uint_v temp0); 
    
  mul_lemma_4 (as_nat h0 f) (uint_v u) (pow2 256 - 1) (pow2 64 - 1);
  assert_norm((pow2 256 - 1) * (pow2 64 - 1) == pow2 320 - pow2 256 - pow2 64 + 1);
  assert_norm((pow2 320 - pow2 256) / pow2 256 == pow2 64 - 1);

  pop_frame();  
  c3 +! temp0


val mul1_add: f1: felem -> u2: uint64 -> f3: felem -> result: felem -> 
  Stack uint64 
  (requires fun h -> live h f1 /\ live h f3 /\ live h result /\ eq_or_disjoint f3 result /\ disjoint f1 result)
  (ensures fun h0 c h1 -> modifies (loc result) h0 h1  /\
    as_nat h1 result + uint_v c * pow2 256 == as_nat h0 f1 * uint_v u2 + as_nat h0 f3 )

let mul1_add f1 u2 f3 result = 
  push_frame();
    let temp = create (size 4) (u64 0) in 
  let c = mul1 f1 u2 temp in 
  let c3 = add4 temp f3 result in 
  pop_frame();  
  c +! c3


val mul: f: felem -> r: felem -> out: widefelem
  -> Stack unit
    (requires fun h -> live h out /\ live h f /\ live h r)
    (ensures  fun h0 _ h1 -> modifies(loc out) h0 h1 /\ wide_as_nat h1 out =  as_nat h0 r * as_nat h0 f )
      
let mul f r out =
  push_frame();
    let temp = create (size 8) (u64 0) in 
    
  let f0 = f.(0ul) in
  let f1 = f.(1ul) in
  let f2 = f.(2ul) in
  let f3 = f.(3ul) in

    let h0 = ST.get() in 
  let b0 = sub temp (size 0) (size 4) in 
  let c0 = mul1 r f0 b0 in 
    upd temp (size 4) c0;

    let h1 = ST.get() in 
    let bk0 = sub temp (size 0) (size 1) in 
  let b1 = sub temp (size 1) (size 4) in   
  let c1 = mul1_add r f1 b1 b1 in 
      upd temp (size 5) c1; 
    let h2 = ST.get() in
      assert(Lib.Sequence.index (as_seq h1 bk0) 0 == Lib.Sequence.index (as_seq h1 temp) 0);

      let bk1 = sub temp (size 0) (size 2) in 
  let b2 = sub temp (size 2) (size 4) in 
  let c2 = mul1_add r f2 b2 b2 in 
    upd temp (size 6) c2;
    
    let h3 = ST.get() in 

    assert(Lib.Sequence.index (as_seq h2 bk1) 0 == Lib.Sequence.index (as_seq h2 temp) 0);
    assert(Lib.Sequence.index (as_seq h2 bk1) 1 == Lib.Sequence.index (as_seq h2 temp) 1);
    assert_norm (pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);

     let bk2 = sub temp (size 0) (size 3) in 
  let b3 = sub temp (size 3) (size 4) in 
  let c3 = mul1_add r f3 b3 b3 in 
    upd temp (size 7) c3;

    assert(Lib.Sequence.index (as_seq h3 bk2) 0 == Lib.Sequence.index (as_seq h3 temp) 0);
    assert(Lib.Sequence.index (as_seq h3 bk2) 1 == Lib.Sequence.index (as_seq h3 temp) 1);
    assert(Lib.Sequence.index (as_seq h3 bk2) 2 == Lib.Sequence.index (as_seq h3 temp) 2);

  assert_by_tactic (as_nat h0 r * (uint_v f2 * pow2 64 * pow2 64) == as_nat h0 r * uint_v f2 * pow2 64 * pow2 64) canon;
  assert_by_tactic (as_nat h0 r * (uint_v f0) == as_nat h0 r * uint_v f0) canon;
  assert_by_tactic (as_nat h0 r * (uint_v f1 * pow2 64) == as_nat h0 r * uint_v f1 * pow2 64) canon;
  assert_by_tactic (as_nat h0 r * (uint_v f3 * pow2 64 * pow2 64 * pow2 64) == as_nat h0 r * uint_v f3 * pow2 64 * pow2 64 * pow2 64) canon;

  dist_lemma_0 (as_nat h0 r) (uint_v f2 * pow2 64 * pow2 64) (uint_v f1 * pow2 64) (uint_v f0) (uint_v f3 * pow2 64 * pow2 64 * pow2 64);

  copy out temp; 
  pop_frame()


val cmovznz4: cin: uint64 -> x: felem -> y: felem -> result: felem ->
  Stack unit
    (requires fun h -> live h x /\ live h y /\ live h result /\ disjoint x result /\ eq_or_disjoint y result)
    (ensures fun h0 _ h1 -> modifies1 result h0 h1 /\ 
      (if uint_v cin = 0 then as_nat h1 result == as_nat h0 x else as_nat h1 result == as_nat h0 y))

let cmovznz4 cin x y r =  
  let h0 = ST.get() in 
  let mask = neq_mask cin (u64 0) in 
  let r0 = logor (logand y.(size 0) mask) (logand x.(size 0) (lognot mask)) in 
  let r1 = logor (logand y.(size 1) mask) (logand x.(size 1) (lognot mask)) in 
  let r2 = logor (logand y.(size 2) mask) (logand x.(size 2) (lognot mask)) in 
  let r3 = logor (logand y.(size 3) mask) (logand x.(size 3) (lognot mask)) in 
  
  upd r (size 0) r0;
  upd r (size 1) r1;
  upd r (size 2) r2;
  upd r (size 3) r3;

    let x = as_seq h0 x in 
    let y = as_seq h0 y in 
    
    cmovznz4_lemma cin (Seq.index x 0) (Seq.index y 0);
    cmovznz4_lemma cin (Seq.index x 1) (Seq.index y 1);
    cmovznz4_lemma cin (Seq.index x 2) (Seq.index y 2);
    cmovznz4_lemma cin (Seq.index x 3) (Seq.index y 3)


val shift_256_impl: i: felem -> o: lbuffer uint64 (size 8) -> 
  Stack unit 
    (requires fun h -> live h i /\ live h o /\ disjoint i o)
    (ensures fun h0 _ h1 -> modifies1 o h0 h1 /\ 
      (
	let o = as_seq h1 o in 
	felem_seq_as_nat_8 o == as_nat h0 i * pow2 256 
      )
    )

let shift_256_impl i o = 
  upd o (size 0) (u64 0);
  upd o (size 1) (u64 0);
  upd o (size 2) (u64 0);
  upd o (size 3) (u64 0);
  upd o (size 4) i.(size 0);
  upd o (size 5) i.(size 1);
  upd o (size 6) i.(size 2);
  upd o (size 7) i.(size 3);

  assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
  assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 (5 * 64));
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
  assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 * pow2 64 = pow2 (8 * 64))

inline_for_extraction noextract
val mod64: a: widefelem -> Stack uint64 
  (requires fun h -> live h a) 
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\  wide_as_nat h1 a % pow2 64 = uint_v r)

let mod64 a = index a (size 0)

inline_for_extraction noextract
val shortened_mul_tuple: a: felem4 -> b: uint64 -> Tot (r: felem8 {as_nat4 a * uint_v b = wide_as_nat4 r /\ wide_as_nat4 r < pow2 320})

let shortened_mul_tuple (a0, a1, a2, a3) b = 
  admit()
  (*let (c, (f0, f1, f2, f3)) = mul1 (a0, a1, a2, a3) b in 
   assert_norm(pow2 64 * pow2 64 = pow2 128);
   assert_norm(pow2 64 * pow2 64 * pow2 64 = pow2 192);
   assert_norm(pow2 64 * pow2 64 * pow2 64 * pow2 64 = pow2 256);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64= pow2 320);
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64 * pow2 64 = pow2 (6 * 64));
   assert_norm(pow2 64 * pow2 64 * pow2 64  * pow2 64 * pow2 64* pow2 64 * pow2 64 = pow2 (7 * 64));
  f0, f1, f2, f3, c, (u64 0), (u64 0), u64(0)   *)


val shortened_mul: a: ilbuffer uint64 (size 4) -> b: uint64 -> result: widefelem -> Stack unit
  (requires fun h -> live h a /\ live h result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\ 
    felem_seq_as_nat (as_seq h0 a) * uint_v b = wide_as_nat h1 result /\ wide_as_nat h1 result < pow2 320)

let shortened_mul a b result = 
    let result04 = sub result (size 0) (size 4) in 
    let c = mul1_il a b result04 in 
    admit();
  upd result (size 4) c
   
  
  (*
*
  let a0 = index a (size 0) in 
  let a1 = index a (size 1) in 
  let a2 = index a (size 2) in 
  let a3 = index a (size 3) in 
  let (f0, f1, f2, f3, f4, f5, f6, f7) = shortened_mul_tuple (a0, a1, a2, a3) b in 
  load_buffer8 f0 f1 f2 f3 f4 f5 f6 f7 result *)


(*wide_as_nat h0 t / pow2 64 = wide_as_nat h1 t1 *)
val shift8: t: widefelem -> t1: widefelem -> Stack unit 
  (requires fun h -> live h t /\ live h t1 /\ eq_or_disjoint t t1)
  (ensures fun h0 _ h1 -> modifies (loc t1) h0 h1 /\ wide_as_nat h0 t / pow2 64 = wide_as_nat h1 t1)

let shift8 t out = 
  let t1 = index t (size 1) in 
  let t2 = index t (size 2) in 
  let t3 = index t (size 3) in 
  let t4 = index t (size 4) in 
  let t5 = index t (size 5) in 
  let t6 = index t (size 6) in 
  let t7 = index t (size 7) in 

  upd out (size 0) t1;
  upd out (size 1) t2;
  upd out (size 2) t3;
  upd out (size 3) t4;
  upd out (size 4) t5;
  upd out (size 5) t6;
  upd out (size 6) t7;
  upd out (size 7) (u64 0)

(* this piece of code is taken from Hacl.Curve25519 *)
inline_for_extraction noextract
val scalar_bit:
    #buf_type: buftype -> 
    s:lbuffer_t buf_type uint8 (size 32)
  -> n:size_t{v n < 256}
  -> Stack uint64
    (requires fun h0 -> live h0 s)
    (ensures  fun h0 r h1 -> h0 == h1 /\
      r == ith_bit (as_seq h0 s) (v n) /\ v r <= 1)
      
let scalar_bit #buf_type s n =
  let h0 = ST.get () in
  mod_mask_lemma ((Lib.Sequence.index (as_seq h0 s) (v n / 8)) >>. (n %. 8ul)) 1ul;
  assert_norm (1 = pow2 1 - 1);
  assert (v (mod_mask #U8 #SEC 1ul) == v (u8 1));
  to_u64 ((s.(n /. 8ul) >>. (n %. 8ul)) &. u8 1)

