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
open FStar.Math.Lemmas

open Hacl.Impl.ECDSA.P256SHA256.Common
open FStar.Mul

#set-options "--z3rlimit 100"

val ecdsa_signature_step12: mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < pow2 61} -> hashAsFelem: felem -> 
  Stack unit 
    (requires fun h -> live h m /\ live h hashAsFelem)
    (ensures fun h0 _ h1 -> modifies (loc hashAsFelem) h0 h1 /\
      (
	let hashOfMessage = Spec.Hash.hash Spec.Hash.Definitions.SHA2_256 (as_seq h0 m) in 
	let changedEndianHash = Hacl.Spec.ECDSA.changeEndian (Lib.ByteSequence.uints_from_bytes_be hashOfMessage) in 
	as_nat h1 hashAsFelem == felem_seq_as_nat changedEndianHash % prime_p256_order
      )
  ) 

let ecdsa_signature_step12 mLen m hashAsFelem  = 
  push_frame(); 
    let mHash = create (size 32) (u8 0) in  
      let h0 = ST.get() in 
    hash_256 m mLen mHash;
    toUint64ChangeEndian mHash hashAsFelem;
      let h2 = ST.get() in 
      lemma_eq_funct (as_seq h2 hashAsFelem) (Hacl.Spec.ECDSA.changeEndian 
	(Lib.ByteSequence.uints_from_bytes_be (Spec.Hash.hash Spec.Hash.Definitions.SHA2_256 (as_seq h0 m))));
    reduction_prime_2prime_order hashAsFelem hashAsFelem;
  pop_frame()


val ecdsa_signature_step45: k: lbuffer uint8 (size 32) -> 
  tempBuffer: lbuffer uint64 (size 100) -> 
  x: felem -> 
  Stack bool 
    (requires fun h -> 
      live h k /\ live h x /\ live h tempBuffer /\ 
      LowStar.Monotonic.Buffer.all_disjoint [loc tempBuffer; loc k; loc x]
    )
    (ensures fun h0 r h1 -> modifies (loc x |+| loc tempBuffer) h0 h1 /\
      (
	let basePoint = (0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296, 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5, 1) in
	let (rxN, ryN, rzN), _ = montgomery_ladder_spec (as_seq h0 k) ((0,0,0), basePoint) in 
	let (xN, _, _) = _norm (rxN, ryN, rzN) in 
	let x = xN % prime_p256_order in 
	if x = 0 then r == true else r == false
      )
    )

let ecdsa_signature_step45 k tempBuffer x = 
  push_frame();
      let result = create (size 12) (u64 0) in 
      let tempForNorm = sub tempBuffer (size 0) (size 88) in 
    secretToPublicWithoutNorm result k tempBuffer; 
    normX result x tempForNorm;
    reduction_prime_2prime_order x x;
  pop_frame();
    isZero_bool x


val lemma_power_step6: kInv: nat  -> Lemma 
  (Hacl.Spec.ECDSA.exponent_spec (fromDomain_ kInv)  == toDomain_ (pow kInv (prime_p256_order - 2)))

let lemma_power_step6 kInv = 
  let a = Hacl.Spec.ECDSA.exponent_spec (fromDomain_ kInv) in 
  lemmaFromDomain kInv;

  power_distributivity (kInv * modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2) prime_p256_order;
  power_distributivity_2 kInv (modp_inv2_prime (pow2 256) prime_p256_order % prime_p256_order) (prime_p256_order - 2);
  lemma_mod_mul_distr_r (pow kInv (prime_p256_order - 2)) (pow (modp_inv2_prime (pow2 256) prime_p256_order) (prime_p256_order - 2)) prime_p256_order;


  lemma_pow_mod_n_is_fpow prime_p256_order (pow2 256 % prime_p256_order) (prime_p256_order - 2);
  assert_norm(modp_inv2_prime (pow2 256) prime_p256_order = 43790243014242295660885426880012836369732278457577312309071968676491870960761); 

  lemma_pow_mod_n_is_fpow prime_p256_order 43790243014242295660885426880012836369732278457577312309071968676491870960761 (prime_p256_order - 2);
  assert_norm(exp #prime_p256_order 43790243014242295660885426880012836369732278457577312309071968676491870960761 (prime_p256_order - 2) == pow2 256 % prime_p256_order);

  lemma_mod_mul_distr_r (pow kInv (prime_p256_order - 2)) (pow2 256) prime_p256_order;
   lemmaToDomain (pow kInv (prime_p256_order - 2))



val ecdsa_signature_step6: kFelem: felem -> z: felem -> r: felem -> da: felem ->result: felem -> Stack unit
  (requires fun h -> live h kFelem /\ live h z /\ live h r /\ live h da /\ 
    as_nat h z < prime_p256_order /\ as_nat h r < prime_p256_order /\ as_nat h da < prime_p256_order /\ 
    as_nat h kFelem < prime_p256_order /\ live h result)
  (ensures fun h0 _ h1 -> modifies (loc result) h0 h1 /\
    as_nat h1 result = (as_nat h0 z + as_nat h0 r * as_nat h0 da) * pow (as_nat h0 kFelem) (prime_p256_order - 2) % prime_p256_order)


let ecdsa_signature_step6 kFelem z r da result = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  push_frame();
    let rda = create (size 4) (u64 0) in 
    let zBuffer = create (size 4) (u64 0) in 
    let kInv = create (size 4) (u64 0) in 
	let h0 = ST.get() in 
    montgomery_multiplication_ecdsa_module r da rda;
    fromDomainImpl z zBuffer;
    felem_add rda zBuffer zBuffer;  
    copy kInv kFelem;
    montgomery_ladder_exponent kInv;
    montgomery_multiplication_ecdsa_module zBuffer kInv result;
       pop_frame();

       let br0 = as_nat h0 z + as_nat h0 r * as_nat h0 da in
       let br1 = pow (as_nat h0 kFelem) (prime_p256_order - 2) in 
       
       lemmaFromDomain (as_nat h0 r * as_nat h0 da); 
       lemma_felem_add (as_nat h0 r * as_nat h0 da) (as_nat h0 z);
       lemma_power_step6 (as_nat h0 kFelem);

       lemmaFromDomain (fromDomain_ br0);
       lemmaToDomain br1;
       assert_norm ((modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) % prime_p256_order = 1);
       
       lemma_mod_mul_distr_l (fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order) (br1 * pow2 256 % prime_p256_order) prime_p256_order;
       lemma_mod_mul_distr_r (fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order) (br1 * pow2 256) prime_p256_order;
       
       assert_by_tactic (fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order * (br1 * pow2 256) == fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order * br1 * pow2 256) canon;
       assert_by_tactic (fromDomain_ br0 * br1 * (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) == fromDomain_ br0 * modp_inv2_prime (pow2 256) prime_p256_order * br1 * pow2 256) canon;
       
       lemma_mod_mul_distr_r (fromDomain_ br0 * br1) (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) prime_p256_order;
       lemmaToDomain ((fromDomain_ br0 * br1) % prime_p256_order);
       lemmaFromDomain br0;
       
       lemma_mod_mul_distr_l (br0 * modp_inv2_prime (pow2 256) prime_p256_order) br1 prime_p256_order;
       lemma_mod_mul_distr_l (br0 * modp_inv2_prime (pow2 256) prime_p256_order * br1) (pow2 256) prime_p256_order;
       
       assert_by_tactic (br0 * modp_inv2_prime (pow2 256) prime_p256_order * br1 * pow2 256 = br0 * br1 * (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256)) canon;
       lemma_mod_mul_distr_r (br0 * br1) (modp_inv2_prime (pow2 256) prime_p256_order * pow2 256) prime_p256_order;
       lemma_mod_mul_distr_r br0 br1 prime_p256_order

open Lib.ByteBuffer 


assume val toUint64: i: lbuffer uint8 (size 32) -> o: felem -> Stack unit 
  (requires fun h -> live h i /\ live h o /\ disjoint i o)
  (ensures fun h0 _ h1 -> True)


val ecdsa_signature_core: mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < pow2 61} ->  
  privKey: lbuffer uint8 (size 32)  -> 
  k: lbuffer uint8 (size 32) -> 
  result: lbuffer uint8 (size 64) -> Stack bool  
  (requires fun h -> live h m /\ live h privKey /\ live h k /\ live h result /\ 
    LowStar.Monotonic.Buffer.all_disjoint [loc m |+| loc privKey |+| loc result]
  )
  (ensures fun h0 _ h1 -> True)


let ecdsa_signature_core mLen m privKey k result = 
  push_frame();
    let hashAsFelem = create (size 4) (u64 0) in     
    let r = create (size 4) (u64 0) in 
    let s = create (size 4) (u64 0) in 
    let tempBuffer = create (size 100) (u64 0) in 
    let kAsFelem = create (size 4) (u64 0) in 


    ecdsa_signature_step12 mLen m hashAsFelem;
    let step5Flag = ecdsa_signature_step45 k tempBuffer r in 
      if not step5Flag then begin
      admit();
      ecdsa_signature_step6 k hashAsFelem r privKey s end;
    admit();
    let step6Flag = isZero_bool s in 
  pop_frame();
    step6Flag
  
val ecdsa_signature:  mLen: size_t -> m: lbuffer uint8 mLen {uint_v mLen < pow2 61} ->   privKey: felem -> k: felem -> result: point -> Stack bool
  (requires fun h -> live h privKey /\ live h k /\ live h result /\ live h m)
  (ensures fun h0 _ h1 -> True)

let ecdsa_signature mLen m privKey k result = 
  let f = isMoreThanZeroLessThanOrderMinusOne privKey in 
  let s = isMoreThanZeroLessThanOrderMinusOne k in 

  let r = ecdsa_signature_core mLen m privKey k result in 
  f && s && r
