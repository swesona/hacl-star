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
open Hacl.Spec.P256.Basic
open Hacl.Spec.P256.Core

open Hacl.Impl.ECDSA.MontgomeryMultiplication
open Hacl.Impl.ECDSA.MM.Exponent
open Hacl.Impl.P256.LowLevel
open Hacl.Impl.LowLevel

open Hacl.Spec.ECDSAP256.Definition

open FStar.Mul

#set-options "--z3rlimit 100"

(* yes, I know that it's a bad idea to include the full module, I will divide it at some point *)
open Hacl.Impl.ECDSA.P256SHA256.Verification

val ecdsa_signature_step01: mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < pow2 61} -> hashAsFelem: felem -> 
  Stack unit 
    (requires fun h -> live h m /\ live h hashAsFelem)
    (ensures fun h0 _ h1 -> modifies (loc hashAsFelem) h0 h1) 

let ecdsa_signature_step01 mLen m hashAsFelem  = 
  push_frame(); 
    let mHash = create (size 32) (u8 0) in  
      let h0 = ST.get() in 
    hash_256 m mLen mHash;
      let h1 = ST.get() in 
      assert(Seq.equal (as_seq h1 mHash) (Spec.Hash.hash Spec.Hash.Definitions.SHA2_256 (as_seq h0 m)));
    toUint64 mHash hashAsFelem;
    reduction_prime_2prime_order hashAsFelem hashAsFelem;
  pop_frame()


val ecdsa_signature_step6: kFelem: felem -> z: felem -> r: felem -> da: felem -> Stack unit
  (requires fun h -> live h kFelem /\ live h z /\ live h r /\ live h da /\ as_nat h z < prime /\ as_nat h r < prime /\ as_nat h da < prime)
  (ensures fun h0 _ h1 -> True)

let ecdsa_signature_step6 kFelem z r da = 
  push_frame();
    let rda = create (size 4) (u64 0) in 
    let zInv = create (size 4) (u64 0) in 
	let h0 = ST.get() in 
      montgomery_multiplication_ecdsa_module r da rda;
	let h1 = ST.get() in 
	(*lemmaFromDomain (as_nat h0 r * as_nat h0 da); *)
	assert(as_nat h1 rda = fromDomain_ (as_nat h0 r * as_nat h0 da));
     fromDomainImpl z zInv;
       let h2 = ST.get() in 
       assert(as_nat h2 zInv = fromDomain_ (as_nat h0 z));
     felem_add rda zInv zInv;  
     
  pop_frame()


val ecdsa_signature_core: mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < pow2 61} ->  privKey: felem  -> k: felem -> result: point -> Stack unit
  (requires fun h -> live h m )
  (ensures fun h0 _ h1 -> True)


let ecdsa_signature_core mLen m privKey k result = 
  push_frame();
    let hashAsFelem = create (size 4) (u64 0) in     
    ecdsa_signature_step01 mLen m hashAsFelem;
  pop_frame()

val ecdsa_signature:  mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < pow2 61} ->   privKey: felem -> k: felem -> result: point -> Stack bool
  (requires fun h -> live h privKey /\ live h k /\ live h result /\ live h m)
  (ensures fun h0 _ h1 -> True)

let ecdsa_signature mLen m privKey k result = 
  let f = isMoreThanZeroLessThanOrderMinusOne privKey in 
  let s = isMoreThanZeroLessThanOrderMinusOne k in 

  ecdsa_signature_core mLen m privKey k result; 
  f && s
