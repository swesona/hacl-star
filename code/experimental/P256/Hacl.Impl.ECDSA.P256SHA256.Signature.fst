module Hacl.Impl.ECDSA.P256SHA256.Signature

open FStar.HyperStack.All
open FStar.HyperStack
module ST = FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

open Hacl.Hash.SHA2
open Hacl.Spec.P256.Definitions

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.ECDSAP256.Definition
open Hacl.Impl.LowLevel

open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.P256.LowLevel
open Hacl.Impl.LowLevel
open Hacl.Impl.P256

open Hacl.Spec.P256

open Hacl.Spec.ECDSAP256.Definition

open FStar.Mul

#set-options "--z3rlimit 100"

(* yes, I know that it's a bad idea to include the full module, I will divide it at some point *)
open Hacl.Impl.ECDSA.P256SHA256.Verification

val ecdsa_signature_step12: mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < pow2 61} -> hashAsFelem: felem -> 
  Stack unit 
    (requires fun h -> live h m /\ live h hashAsFelem)
    (ensures fun h0 _ h1 -> modifies (loc hashAsFelem) h0 h1) 

let ecdsa_signature_step12 mLen m hashAsFelem  = 
  push_frame(); 
    let mHash = create (size 32) (u8 0) in  
      let h0 = ST.get() in 
    hash_256 m mLen mHash;
      let h1 = ST.get() in 
      assert(Seq.equal (as_seq h1 mHash) (Spec.Hash.hash Spec.Hash.Definitions.SHA2_256 (as_seq h0 m)));
    toUint64 mHash hashAsFelem;
    reduction_prime_2prime_order hashAsFelem hashAsFelem;
  pop_frame()


assume val ecdsa_signature_step4: k: lbuffer uint8 (size 32) -> result: point -> tempBuffer: lbuffer uint64 (size 100) -> 
  Stack unit 
    (requires fun h -> 
      live h k /\ live h result /\ live h tempBuffer /\
      LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc k; loc result]
    )
    (
    ensures fun h0 _ h1 -> modifies (loc result |+| loc tempBuffer) h0 h1 /\
      as_nat h1 (gsub result (size 0) (size 4)) < prime /\ 
      as_nat h1 (gsub result (size 4) (size 4)) < prime /\ 
      as_nat h1 (gsub result (size 8) (size 4)) < prime /\
      (
	let x3, y3, z3 = as_nat h1 (gsub result (size 0) (size 4)), as_nat h1 (gsub result (size 0) (size 4)), as_nat h1 (gsub result (size 0) (size 4)) in 
	let (xN, yN, zN) = secret_to_public (as_seq h0 k)  in 
	x3 == xN /\ y3 == yN /\ z3 == zN 
    )
  )

(*
let ecdsa_signature_step4 k result tempBuffer = 
  secretToPublicWithPartialNorm result scalar tempBuffer
*)

val ecdsa_signature_step6: kFelem: felem -> z: felem -> r: felem -> da: felem ->result: felem -> Stack unit
  (requires fun h -> live h kFelem /\ live h z /\ live h r /\ live h da /\ as_nat h z < prime /\ as_nat h r < prime /\ as_nat h da < prime /\ as_nat h kFelem < prime /\ live h result)
  (ensures fun h0 _ h1 -> True)

let ecdsa_signature_step6 kFelem z r da result = 
  push_frame();
    let rda = create (size 4) (u64 0) in 
    let zBuffer = create (size 4) (u64 0) in 
    let kInv = create (size 4) (u64 0) in 

	let h0 = ST.get() in 
      montgomery_multiplication_ecdsa_module r da rda;
	let h1 = ST.get() in 
	lemmaFromDomain (as_nat h0 r * as_nat h0 da); 
	assert(as_nat h1 rda = fromDomain_ (as_nat h0 r * as_nat h0 da));
     fromDomainImpl z zBuffer;
       let h2 = ST.get() in 
       assert(as_nat h2 zBuffer = fromDomain_ (as_nat h0 z));
     felem_add rda zBuffer zBuffer;  
       let h3 = ST.get() in 
     lemma_felem_add (as_nat h0 r * as_nat h0 da) (as_nat h0 z);
     
     assert(as_nat h3 zBuffer = fromDomain_ (as_nat h0 z + as_nat h0 r * as_nat h0 da));
     copy kInv kFelem;
       let h4 = ST.get() in 
       assert(as_nat h4 kInv = as_nat h0 kFelem);
     montgomery_ladder_exponent kInv;
       let h5 = ST.get() in 
       assert(fromDomain_ (as_nat h5 kInv) == Hacl.Spec.ECDSA.exponent_spec (fromDomain_ (as_nat h0 kFelem)));
     montgomery_multiplication_ecdsa_module zBuffer kInv result;
       let h6 = ST.get() in 
       assert(as_nat h6 result = toDomain_ (fromDomain_ ((fromDomain_ (as_nat h0 z + as_nat h0 r * as_nat h0 da))) * Hacl.Spec.ECDSA.exponent_spec (fromDomain_ (as_nat h0 kFelem)) % prime_p256_order));
     admit();
     
  pop_frame()


val ecdsa_signature_core: mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < pow2 61} ->  privKey: felem  -> k: felem -> result: point -> Stack unit
  (requires fun h -> live h m )
  (ensures fun h0 _ h1 -> True)


let ecdsa_signature_core mLen m privKey k result = 
  push_frame();
    let hashAsFelem = create (size 4) (u64 0) in     
    ecdsa_signature_step12 mLen m hashAsFelem;
  pop_frame()

val ecdsa_signature:  mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < pow2 61} ->   privKey: felem -> k: felem -> result: point -> Stack bool
  (requires fun h -> live h privKey /\ live h k /\ live h result /\ live h m)
  (ensures fun h0 _ h1 -> True)

let ecdsa_signature mLen m privKey k result = 
  let f = isMoreThanZeroLessThanOrderMinusOne privKey in 
  let s = isMoreThanZeroLessThanOrderMinusOne k in 

  ecdsa_signature_core mLen m privKey k result; 
  f && s
