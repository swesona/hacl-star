
module Hacl.Impl.ECDSA.P256SHA256.Common

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Impl.LowLevel
open Hacl.Impl.P256
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MM.Exponent

open Hacl.Spec.ECDSAP256.Definition
open Hacl.Spec.ECDSA
open Hacl.Spec.P256 
open Hacl.Spec.P256.Ladder
open Hacl.Spec.P256.Lemmas

open Hacl.Impl.P256.PointAdd
open Hacl.Impl.P256.LowLevel

open Hacl.Hash.SHA2


val changeEndian: i: felem -> Stack unit 
  (requires fun h -> live h i)
  (ensures fun h0 _ h1 -> modifies1 i h0 h1 /\ as_seq h1 i == Hacl.Spec.ECDSA.changeEndian (as_seq h0 i)) 

let changeEndian i = 
  let zero = index i (size 0) in 
  let one = index i (size 1) in 
  let two = index i (size 2) in 
  let three = index i (size 3) in 
  upd i (size 0) three;
  upd i (size 1) two; 
  upd i (size 2) one;
  upd i (size 3) zero



open Lib.ByteBuffer 


val toUint64ChangeEndian: i: lbuffer uint8 (32ul) -> o: felem ->  Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 
    /\ as_seq h1 o == Hacl.Spec.ECDSA.changeEndian(Lib.ByteSequence.uints_from_bytes_be #_ #_ #4 (as_seq h0 i))
   )

let toUint64ChangeEndian i o = 
  uints_from_bytes_be o i;
  changeEndian o


val toUint8: i: felem ->  o: lbuffer uint8 (32ul) -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> modifies (loc o) h0 h1 /\ 
    as_seq h1 o == Lib.ByteSequence.uints_to_bytes_le #_ #_ #4 (as_seq h0 i))

let toUint8 i o = 
  uints_to_bytes_le (size 4) o i



inline_for_extraction noextract
val equalZeroBuffer: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 r h1 -> modifies0 h0 h1 /\ (if as_nat h0 f = 0 then r == true else r == false ))

let equalZeroBuffer f =        
    let f0 = index f (size 0) in  
    let f1 = index f (size 1) in 
    let f2 = index f (size 2) in 
    let f3 = index f (size 3) in 

    let z0_zero = eq_0_u64 f0 in 
    let z1_zero = eq_0_u64 f1 in 
    let z2_zero = eq_0_u64 f2 in 
    let z3_zero = eq_0_u64 f3 in 
  
    z0_zero && z1_zero && z2_zero && z3_zero
  


(* checks whether the intefer f is between 1 and (n- 1) (incl).  *)
(* [1, n - 1] <==> a > 0 /\ a < n) *)

val isMoreThanZeroLessThanOrderMinusOne: f: felem -> Stack bool
  (requires fun h -> live h f)
  (ensures fun h0 result h1 -> modifies0 h0 h1 /\
    (
      if as_nat h0 f > 0 && as_nat h0 f < prime_p256_order then result == true else result == false
    )  
  )

let isMoreThanZeroLessThanOrderMinusOne f = 
  push_frame();
    let h0 = ST.get() in 
    let tempBuffer = create (size 4) (u64 0) in 
        recall_contents prime256order_buffer (Lib.Sequence.of_list p256_order_prime_list);
  let h0 = ST.get() in 
    let carry = sub4_il f prime256order_buffer tempBuffer in  
      assert(if uint_v carry = 1 then as_nat h0 f < prime_p256_order else True);
  let h1 = ST.get() in 
  assert(modifies1 tempBuffer h0 h1);
    let less = eq_u64 carry (u64 1) in
      assert(less == true ==> as_nat h0 f < prime_p256_order);
  let h2 = ST.get() in 
    let more = equalZeroBuffer f in 
      assert(not more == true ==> as_nat h0 f > 0);
    let result = less &&  not more in 
      assert(less && not more ==> as_nat h0 f > 0 && as_nat h0 f < prime_p256_order);
  pop_frame();  
    result