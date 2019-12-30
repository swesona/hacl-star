
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


val toUint64: i: lbuffer uint8 (32ul) -> o: felem -> Stack unit
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures 
    fun h0 _ h1 -> modifies (loc o) h0 h1 /\ 
      as_seq h1 o == Lib.ByteSequence.uints_from_bytes_le (as_seq h0 i))

let toUint64 i o = 
    Lib.ByteBuffer.uints_from_bytes_le o i


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


val lemma_core_0: a: lbuffer uint64 (size 4) -> h: mem -> 
  Lemma (Lib.ByteSequence.nat_from_intseq_le (as_seq h a) == as_nat h a)

let lemma_core_0 a h = 
  let open Lib.ByteSequence in 
  
    let k = as_seq h a in 
    let z = nat_from_intseq_le k in 
    
    nat_from_intseq_le_slice_lemma k 1;
    nat_from_intseq_le_lemma0 (Seq.slice k 0 1);

    let k1 = Seq.slice k 1 4 in 
      nat_from_intseq_le_slice_lemma #_ #_ #3 k1 1;
      nat_from_intseq_le_lemma0 (Seq.slice k1 0 1);
      
    let k2 = Seq.slice k1 1 3 in 
      nat_from_intseq_le_slice_lemma #_ #_ #2 k2 1;
      nat_from_intseq_le_lemma0 (Seq.slice k2 0 1);
      nat_from_intseq_le_lemma0 (Seq.slice k2 1 2)


val lemma_core_1: a: lbuffer uint64 (size 4) -> h: mem -> 
  Lemma (Lib.ByteSequence.nat_from_bytes_le (Lib.ByteSequence.uints_to_bytes_le (as_seq h a)) == as_nat h a)

let lemma_core_1 a h= 
  let open Lib.ByteSequence in 
  let k = as_seq h a in 
  let z = Lib.ByteSequence.uints_to_bytes_le (as_seq h a) in 
  let maint = Lib.ByteSequence.nat_from_bytes_le (Lib.ByteSequence.uints_to_bytes_le (as_seq h a)) in 
  lemma_core_0 a h;
  lemma_nat_from_to_intseq_le_preserves_value #U64 #SEC 4 (as_seq h a);
  let n = nat_from_intseq_le k in 
  uints_to_bytes_le_nat_lemma #U64 #SEC 4 n;
  lemma_nat_to_from_bytes_le_preserves_value #SEC (uints_to_bytes_le #U64 #SEC #4 (as_seq h a)) 32 (as_nat h a)
