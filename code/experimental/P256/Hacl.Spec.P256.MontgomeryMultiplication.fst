module Hacl.Spec.P256.MontgomeryMultiplication

open FStar.Math.Lemmas
open FStar.Math.Lib
open FStar.Mul

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST
module ST = FStar.HyperStack.ST

open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.Core

open Hacl.Impl.Curve25519.Field64.Core
open Hacl.Spec.Curve25519.Field64.Definition
open Hacl.Spec.Curve25519.Field64.Core 

open Hacl.Impl.Gen

open Lib.IntTypes
open Lib.Buffer
open Lib.Sequence
open Lib.Loops

#reset-options "--z3rlimit 300"


let fromDomain_ a = (a * modp_inv2 (pow2 256)) % prime

let fromDomainPoint a = 
  let x, y, z = a in 
  fromDomain_ x, fromDomain_ y, fromDomain_ z


assume val fromDomain: a: felem4{as_nat4 a < prime} -> Tot (result: felem4 {as_nat4 result = fromDomain_ (as_nat4 a)})

(*let fromDomain a =  
  let one = ((u64 1), (u64 0), u64 0, u64 0) in
    assert_norm (as_nat4 one = 1);
  Core.montgomery_multiplication one a
*)

let toDomain_ a = (a * pow2 256) % prime


assume val toDomain: a: felem4{as_nat4 a < prime} -> Tot (result: felem4 {as_nat4 result = toDomain_ (as_nat4 a)})
(*
let toDomain a = 
  let open Hacl.Spec.P256.SolinasReduction  in 
  let multiplied = Core.shift_256 a in 
  solinas_reduction multiplied
*)

let lemmaFromDomain a = ()

let lemmaToDomain a = ()


let lemmaToDomainAndBackIsTheSame a = 
  let to = toDomain_ a in 
  let from = fromDomain_ to in 
  lemma_mod_mul_distr_l (a * pow2 256) (modp_inv2 (pow2 256)) prime;
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 (pow2 256)) prime


let lemmaFromDomainToDomain a = 
  let from = fromDomain_ a in 
  let to = toDomain_ from in 
  lemma_mod_mul_distr_l (a * modp_inv2 (pow2 256)) (pow2 256)  prime;
  assert_norm (modp_inv2 (pow2 256) * (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (modp_inv2 (pow2 256)) (pow2 256) prime


val lemmaFromDomainToDomainModuloPrime: a: int -> Lemma (a % prime == fromDomain_(toDomain_ a))

let lemmaFromDomainToDomainModuloPrime a = 
  lemma_mod_mul_distr_l (a*pow2 256) (modp_inv2 (pow2 256)) prime;
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime = 1);
  modulo_distributivity_mult_last_two a 1 1 (pow2 256) (modp_inv2 (pow2 256)) prime

val lemmaMontgomeryMultiplicationCorrect: a: felem4{as_nat4 a < prime} -> b: felem4{as_nat4 b < prime} -> Lemma (
  let aDomain = toDomain a in 
  let bDomain = toDomain b in 
  let multInDomain = Core.montgomery_multiplication aDomain bDomain in 
  let multResultFromDomain = fromDomain multInDomain in 
  as_nat4 a * as_nat4 b % prime == as_nat4 multResultFromDomain)


let lemmaMontgomeryMultiplicationCorrect a b = 
  let aDomain = toDomain a in 
  let bDomain = toDomain b in 
  let multInDomain = montgomery_multiplication aDomain bDomain in 
  assert_norm (prime > 0);
  modulo_distributivity_mult2 (as_nat4 a * pow2 256) (as_nat4 b * pow2 256) (modp_inv2 (pow2 256)) prime;  
  lemma_brackets_l (as_nat4 a * pow2 256) ((as_nat4 b * pow2 256) * modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
  lemma_twice_brackets (as_nat4 a) (pow2 256) 1 (as_nat4 b) (pow2 256) 1 (modp_inv2 (pow2 256));
  modulo_distributivity_mult2 (as_nat4 a * pow2 256) (as_nat4 b * pow2 256) (modp_inv2 (pow2 256)) prime;
  modulo_distributivity_mult_last_two (as_nat4 a) (pow2 256) (as_nat4 b) (pow2 256) (modp_inv2 (pow2 256)) prime;
  assert_norm((pow2 256 * modp_inv2 (pow2 256)) % prime = 1);
  lemma_distr_mult3 (as_nat4 a) (pow2 256) (as_nat4 b);
  let multFromDomain = fromDomain multInDomain in 
  lemma_mod_mul_distr_l (as_nat4 a * as_nat4 b *pow2 256) (modp_inv2 (pow2 256)) prime;
  modulo_distributivity_mult_last_two (as_nat4 a) (as_nat4 b) 1 (pow2 256) (modp_inv2 (pow2 256)) prime


(* the lemma shows the equivalence between toDomain(a:nat) and toDomain(a % prime) *)
val inDomain_mod_is_not_mod: a: int -> Lemma (toDomain_ a == toDomain_ (a % prime))

let inDomain_mod_is_not_mod a = 
  lemma_mod_mul_distr_l a (pow2 256) prime


(* the lemma shows that the result of multiplication moved out of domain is the multiplication of the numbers moved out of domain *)
val multiplicationInDomain: #k: nat -> #l: nat -> 
  a: felem4 {as_nat4 a == toDomain_ (k) /\ as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b == toDomain_ (l) /\ as_nat4 b < prime} -> Lemma 
    (ensures (let multResult = Core.montgomery_multiplication a b in as_nat4 multResult == toDomain_ (k * l)))
    
let multiplicationInDomain #k #l a b = 
  let multResult = Core.montgomery_multiplication a b in 
  lemma_mul_nat2 k l;
  let secondBracket = toDomain_ (k * l) in 
    assert(as_nat4 multResult = toDomain_ (k) * toDomain_ (l) * modp_inv2 (pow2 256) % prime);
  modulo_distributivity_mult2 (k * pow2 256) (l* pow2 256) (modp_inv2 (pow2 256)) prime;
  lemma_twice_brackets k (pow2 256) 1 l (pow2 256) 1 (modp_inv2 (pow2 256));
  assert_norm (pow2 256 * modp_inv2 (pow2 256) % prime == 1);
  modulo_distributivity_mult_last_two k (pow2 256) l (pow2 256) (modp_inv2 (pow2 256)) prime;
  lemma_distr_mult3 k (pow2 256) l


val additionInDomain: #k: nat -> #l: nat -> 
  a: felem4 {as_nat4 a == toDomain_ (k) /\ as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b == toDomain_ (l) /\ as_nat4 b < prime} -> Lemma 
  (ensures (let result = felem_add a b in as_nat4 result == toDomain_(k + l)))

let additionInDomain #k #l a b = 
  let result = felem_add a b in 
  assert(as_nat4 result = (as_nat4 a + as_nat4 b) % prime);
  assert(as_nat4 result = (toDomain_(k) + toDomain_(l)) % prime);
  assert(as_nat4 result = ((k * pow2 256 % prime) + (l * pow2 256 % prime)) % prime);
  modulo_distributivity (k * pow2 256) (l *pow2 256) prime;
  assert(as_nat4 result = toDomain_ (k + l))

#reset-options "--z3refresh --z3rlimit  100"


val additionInDomain_spec: #k: nat -> #l: nat -> a: nat_mod_prime{a == toDomain_ k} -> b: nat_mod_prime {b == toDomain_ l} -> 
  Lemma 
    (let result = felem_add_spec a b in result == toDomain_ (k + l))

let additionInDomain_spec #k #l a b = 
    modulo_distributivity (k * pow2 256) (l * pow2 256) prime

val additionInDomain2_spec: a: nat_mod_prime -> b: nat_mod_prime -> Lemma 
  (let result = felem_add_spec a b in result = toDomain_ (fromDomain_ a + fromDomain_ b))

let additionInDomain2_spec a b = 
  let k = fromDomain_ a in 
  let l = fromDomain_ b in 
  lemmaFromDomainToDomain a;
  lemmaFromDomainToDomain b;
  additionInDomain_spec #k #l a b


val additionInDomain2: a: felem4{as_nat4 a < prime} -> b: felem4 {as_nat4 b < prime} -> Lemma (let result = felem_add a b in 
  as_nat4 result = toDomain_ (fromDomain_ (as_nat4 a) + fromDomain_ (as_nat4 b)))

let additionInDomain2 a b = 
  let k = fromDomain_ (as_nat4 a) in 
  let l = fromDomain_ (as_nat4 b) in 
  lemmaFromDomainToDomain (as_nat4 a);
  lemmaFromDomainToDomain (as_nat4 b);
  additionInDomain #k #l a b


(* the lemma shows the equivalence between fromDomain(a:nat) and fromDomain(a % prime) *)
val fromDomain_mod_is_not_mod: a: nat -> Lemma (fromDomain_ a == fromDomain_ (a % prime))

let fromDomain_mod_is_not_mod a = 
  lemma_mod_mul_distr_l a (modp_inv2(pow2 256)) prime


val additionInDomainLemma2: a: felem4{as_nat4 a < prime} -> b: felem4{as_nat4 b < prime} -> 
  Lemma (ensures (as_nat4 (fromDomain (felem_add a b)) = (as_nat4(fromDomain (a)) + as_nat4(fromDomain (b))) % prime))

let  additionInDomainLemma2 a b =  
  let k = (as_nat4 (fromDomain a) + as_nat4 (fromDomain b)) % prime in 
  modulo_distributivity (as_nat4 a * modp_inv2 (pow2 256)) (as_nat4 b * modp_inv2 (pow2 256)) prime;
  distributivity_add_left (as_nat4 a) (as_nat4 b) (modp_inv2 (pow2 256));
  fromDomain_mod_is_not_mod (as_nat4 a + as_nat4 b)

val subtractionInDomain: #k: nat -> #l: nat -> 
  a: felem4 {as_nat4 a == toDomain_ (k) /\ as_nat4 a < prime} -> 
  b: felem4 {as_nat4 b == toDomain_ (l) /\ as_nat4 b < prime} -> Lemma 
  (ensures (let result = felem_sub a b in as_nat4 result == toDomain_(k - l)))

let subtractionInDomain #k #l a b = 
  let result = felem_sub a b in 
  lemma_mod_sub_distr (as_nat4 a) (l * pow2 256) prime;
  lemma_mod_add_distr (-l * pow2 256) (k * pow2 256) prime


val substractionInDomain2: a: felem4{as_nat4 a < prime} -> b: felem4{as_nat4 b < prime} -> Lemma (let result = felem_sub a b in 
  as_nat4 result = toDomain_ (fromDomain_ (as_nat4 a) - fromDomain_ (as_nat4 b)))

let substractionInDomain2 a b = 
  let k = fromDomain_ (as_nat4 a) in 
  let l = fromDomain_ (as_nat4 b) in 
  lemmaFromDomainToDomain (as_nat4 a);
  lemmaFromDomainToDomain (as_nat4 b);
  subtractionInDomain #k #l a b


let rec pow a b =
  if b = 0 then 1
  else a * (pow a (b - 1))


val pow_plus: a: nat -> b: nat -> c: nat -> Lemma (ensures (pow a b * pow a c = pow a (b +c)))
(decreases b)

let rec pow_plus a b c = 
  match b with 
  | 0 -> assert_norm (pow a 0 = 1)
  | _ -> pow_plus a (b -1) c; 
    assert_norm(pow a (b - 1) * a = pow a b)


let rec power_distributivity a b c =
   match b with 
   | 0 -> ()
   | _ -> 
     power_distributivity a (b - 1) c; 
     modulo_distributivity_mult (pow a (b -1)) a c;
     lemma_mod_twice a c;
     modulo_distributivity_mult (pow (a % c) (b -1)) (a % c) c


val power_mult: a: nat -> b: nat -> c: nat -> Lemma (pow (pow a b) c == pow a (b * c))

let rec power_mult a b c = 
  match c with 
  |0 -> assert_norm(pow a 0 = 1); assert(pow (pow a b) 0  = 1)
  |_ ->  power_mult a b (c -1); pow_plus a (b * (c -1)) b


let felem_add_seq a b = 
  let a0 = index a 0 in 
  let a1 = index a 1 in 
  let a2 = index a 2 in 
  let a3 = index a 3 in 

  let b0 = index b 0 in 
  let b1 = index b 1 in 
  let b2 = index b 2 in 
  let b3 = index b 3 in 

  let (r0, r1, r2, r3) = felem_add (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  
  let r = create 4 (u64 0)  in 
  let r = upd r 0 r0 in
  let r = upd r 1 r1 in 
  let r = upd r 2 r2 in 
  let r = upd r 3 r3 in 

  additionInDomain2 (a0, a1, a2, a3) (b0, b1, b2, b3);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat4 (a0, a1, a2, a3)) + fromDomain_ (as_nat4 (b0, b1, b2, b3)));
  r


let felem_sub_seq a b = 
  let a0 = index a 0 in 
  let a1 = index a 1 in 
  let a2 = index a 2 in 
  let a3 = index a 3 in 

  let b0 = index b 0 in 
  let b1 = index b 1 in 
  let b2 = index b 2 in 
  let b3 = index b 3 in 

  let a_tuple = a0, a1, a2, a3 in 
  let b_tuple = b0, b1, b2, b3 in 
  let (r0, r1, r2, r3) = felem_sub a_tuple b_tuple in 

  
  let r = create 4 (u64 0)  in 
  let r = upd r 0 r0 in
  let r = upd r 1 r1 in 
  let r = upd r 2 r2 in 
  let r = upd r 3 r3 in 

  substractionInDomain2 (a0, a1, a2, a3) (b0, b1, b2, b3);
  inDomain_mod_is_not_mod (fromDomain_ (as_nat4 (a0, a1, a2, a3)) - fromDomain_ (as_nat4 (b0, b1, b2, b3)));
  r

val lemma_size_uint64: a0: uint64 -> a1: uint64 -> Lemma
    (uint_v a0 * uint_v a1 < pow2 128 - 2 * pow2 64 + 2)

let lemma_size_uint64 a b = 
  assert(uint_v a <= pow2 64 - 1);
  assert(uint_v b <= pow2 64 - 1);
  assert(uint_v a * uint_v b <= (pow2 64 - 1) * (pow2 64 - 1));
  assert_norm ((pow2 64 -1) * (pow2 64 - 1) = pow2 128 - 2 * pow2 64  + 1);
  assert(uint_v a * uint_v b < pow2 128 - 2 * pow2 64 + 2)

val lemma_mult_plus_two: a0: uint64 -> a1: uint64 -> a2: uint64 -> a3: uint64 -> 
  Lemma 
    (uint_v a0 * uint_v a1 + uint_v a2 + uint_v a3 < pow2 128)

let lemma_mult_plus_two a0 a1 a2 a3 = 
  lemma_size_uint64 a0 a1

inline_for_extraction noextract
val multMM1: x: uint64 -> b0: uint64 ->t0: uint64 ->  t0b: lbuffer uint64  (size 1) -> tempBuffer: lbuffer uint64 (size 1) ->
  Stack uint64
    (requires fun h -> live h t0b /\ live h tempBuffer /\ disjoint t0b tempBuffer)
    (ensures fun h0 f h1 -> modifies2 t0b tempBuffer h0 h1  /\
      (
	let t0Updated = Seq.index (as_seq h1 t0b) 0 in 
	uint_v f + uint_v t0Updated * pow2 64 = uint_v x * uint_v b0 + uint_v t0
      )
    )
    

let multMM1 x b0 t0 t0_b temp_zl = 
  let zl, zh = mul64 x b0 in 
    assert(uint_v zl == (uint_v x * uint_v b0) % pow2 64);
    let h0 = ST.get() in 
  let k = add_carry (u64 0) zl t0 temp_zl in
    let h1 = ST.get() in 
    lemma_mod_add_distr (uint_v t0) (uint_v x * uint_v b0) (pow2 64);
    assert(if uint_v zl + uint_v t0 >= pow2 64 then uint_v k = 1 else uint_v k = 0);
  let c = add_carry k zh (u64 0) t0_b in
  Lib.Buffer.index temp_zl (size 0)


#reset-options "--z3refresh --z3rlimit 200"


inline_for_extraction noextract
val add2: a: uint64 -> b: uint64 -> c: uint64 -> temp_zl: lbuffer uint64 (size 1) -> temp_zh: lbuffer uint64 (size 1) -> 
  Stack unit
    (requires fun h -> live h temp_zl /\ live h temp_zh 
      /\ disjoint temp_zl temp_zh 
      /\ uint_v a +  uint_v b * pow2 64 < pow2 128 - pow2 64 + 1)
    (ensures fun h0 _ h1 -> modifies2 temp_zl temp_zh h0 h1 /\ 
      (
      let temp_zl = Seq.index (as_seq h1 temp_zl) 0 in 
      let temp_zh = Seq.index (as_seq h1 temp_zh) 0 in 
      uint_v temp_zh * pow2 64 + uint_v temp_zl == uint_v a +  uint_v b * pow2 64 + uint_v c
      )
    )  

let add2 a b c temp_zl temp_zh = 
  let k = add_carry (u64 0) a c temp_zl in 
  let _ = add_carry k b (u64 0) temp_zh in  ()


inline_for_extraction noextract
val multMM2: x: uint64 -> b: uint64 ->t: uint64 -> t_curr: lbuffer uint64 (size 1) -> t_next: lbuffer uint64 (size 1) -> temp: lbuffer uint64 (size 2) -> 
  Stack unit 
    (requires fun h -> live h t_curr /\ live h t_next /\ live h temp /\ disjoint t_curr t_next /\ disjoint t_curr temp /\ disjoint t_next temp)
    (ensures fun h0 _ h1 -> modifies3 t_curr t_next temp h0 h1 /\
      (
	let t_curr_before = Seq.index (as_seq h0 t_curr) 0 in 
	let t_curr = Seq.index (as_seq h1 t_curr ) 0 in 
	let t_next = Seq.index (as_seq h1 t_next) 0 in 
	uint_v t_curr + uint_v t_next * pow2 64 == uint_v x * uint_v b + uint_v t + uint_v t_curr_before
    )
)


let multMM2 x b t t_curr t_next temp = 
  let open Lib.Buffer in 
  let temp_zl = sub temp (size 0) (size 1) in 
  let temp_zh = sub temp (size 1) (size 1) in 
  let zl, zh = mul64 x b in 
  lemma_size_uint64 x b;  
  add2 zl zh t_curr.(size 0) temp_zl temp_zh;
  add2 temp_zl.(size 0) temp_zh.(size 0) t t_curr t_next



inline_for_extraction noextract
val montgomery_multiplication_round_1: x: uint64 -> b: felem -> t4_prev: uint64 -> t_buffer: lbuffer uint64 (size 4) -> tempBufferLocal: lbuffer uint64 (size 2) -> 
  Stack uint64 
    (requires fun h -> live h t_buffer /\ live h tempBufferLocal /\ live h b /\ disjoint b t_buffer /\ disjoint b tempBufferLocal /\ disjoint t_buffer tempBufferLocal)
    (ensures fun h0 f h1 -> modifies2 t_buffer tempBufferLocal h0 h1 
      /\
	(
	  let b = as_seq h0 b in 
	  let t_buffer_pr = as_seq h0 t_buffer in 
	  let t_buffer = as_seq h1 t_buffer in 
	  
	  let t4 = Seq.index (as_seq h1 tempBufferLocal) 0 in 
	  let b0 = Seq.index b 0 in 
	  let t0 = Seq.index t_buffer_pr 0 in 

	  uint_v f = (uint_v b0 * uint_v x + uint_v t0) % pow2 64 /\

	  felem_seq_as_nat t_buffer + uint_v t4 * pow2 256 == 
	  (felem_seq_as_nat t_buffer_pr + uint_v t4_prev * pow2 256 + uint_v x * felem_seq_as_nat b - uint_v f) / pow2 64 
    )
)


let montgomery_multiplication_round_1 x b t4 t_buffer tempBufferLocal = 
  let open Lib.Buffer in 
  let temp_zl = sub tempBufferLocal (size 0) (size 1) in 

  let t0 = t_buffer.(size 0) in 
  let t1 = t_buffer.(size 1) in 
  let t2 = t_buffer.(size 2) in 
  let t3 = t_buffer.(size 3) in 

  (*not to delete - stops passing *)
  let t0_b = sub t_buffer (size 0) (size 1) in 
  let t1_b = sub t_buffer (size 1) (size 1) in 
  let t2_b = sub t_buffer (size 2) (size 1) in 
  let t3_b = sub t_buffer (size 3) (size 1) in 

  let f = multMM1 x b.(size 0) t0 t0_b temp_zl in 
  multMM2 x b.(size 1) t1 t0_b t1_b tempBufferLocal;
  multMM2 x b.(size 2) t2 t1_b t2_b tempBufferLocal;
  multMM2 x b.(size 3) t3 t2_b t3_b tempBufferLocal;
  let t4 = add_carry (u64 0) t3_b.(size 0) t4 t3_b in 
  upd tempBufferLocal (size 0) t4;
  f
    
  

val mm_round: x: uint64 -> b: felem -> t4_pr: uint64 -> t_buffer: felem -> 
  Stack uint64
  (requires fun h -> live h b /\ live h t_buffer /\ disjoint b t_buffer)
  (ensures fun h0 t4 h1 -> modifies1 t_buffer h0 h1 /\ 
    (
      let t_buffer_pr = as_seq h0 t_buffer in 
      let t_buffer = as_seq h1 t_buffer in 
      let b = as_seq h0 b in 
      let b0 = Seq.index b 0 in 
      let t0 = Seq.index t_buffer_pr 0 in 
      let f = (uint_v b0 * uint_v x + uint_v t0) % pow2 64 in 

      let t_pr = felem_seq_as_nat t_buffer_pr + uint_v t4_pr * pow2 256 in 
      let t = felem_seq_as_nat t_buffer + uint_v t4 * pow2 256 in 
      t = t_pr + uint_v x * felem_seq_as_nat b + f * prime
    )
  )



let mm_round x b t4 tempBuffer =  
  let open Lib.Buffer in 
  push_frame();

  let tempBufferLocal = create (size 2) (u64 0) in 
  let temp_zl = sub tempBufferLocal (size 0) (size 1) in 
  let temp_zh = sub tempBufferLocal (size 1) (size 1) in 

  let t0_b = sub tempBuffer (size 0) (size 1) in 
  let t1_b = sub tempBuffer (size 1) (size 1) in 
  let t2_b = sub tempBuffer (size 2) (size 1) in 
  let t3_b = sub tempBuffer (size 3) (size 1) in 

  let f = montgomery_multiplication_round_1 x b t4 tempBuffer tempBufferLocal in 
  let t4 = index tempBufferLocal (size 0) in 

  let k = add_carry (u64 0) (t0_b.(size 0)) (f <<. (size 32)) t0_b in 
  let k = add_carry k (t1_b.(size 0)) (f >>. (size 32)) t1_b in 

  let m = sub_borrow (u64 0) f (f <<. (size 32)) temp_zl in 
  let _ = sub_borrow m f (f >>. (size 32)) temp_zh in 


  let k = add_carry k t2_b.(size 0) (index temp_zl (size 0)) t2_b in 
  let k = add_carry k t3_b.(size 0) (index temp_zh (size 0)) t3_b in 
  let _ = add_carry k t4 (u64 0) temp_zl in 

  let t4 = index temp_zl (size 0) in 
  
   pop_frame();
  t4



let montgomery_multiplication_seq a b  = 
  let a0 = index a 0 in 
  let a1 = index a 1 in 
  let a2 = index a 2 in 
  let a3 = index a 3 in 

  let b0 = index b 0 in 
  let b1 = index b 1 in 
  let b2 = index b 2 in 
  let b3 = index b 3 in 

    [@inline_let]
  let a_tuple = a0, a1, a2, a3 in 
    [@inline_let]
  let b_tuple = b0, b1, b2, b3 in 
  let (r0, r1, r2, r3) = montgomery_multiplication (a0, a1, a2, a3) (b0, b1, b2, b3) in 
  lemmaFromDomainToDomain (as_nat4 a_tuple);
  lemmaFromDomainToDomain (as_nat4 b_tuple);
  multiplicationInDomain #(fromDomain_ (as_nat4 a_tuple)) #(fromDomain_ (as_nat4 b_tuple)) a_tuple b_tuple;
  inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat b));

  let r = create 4 (u64 0)  in 
  let r = upd r 0 r0 in
  let r = upd r 1 r1 in 
  let r = upd r 2 r2 in 
  let r = upd r 3 r3 in 
   r




let montgomery_multiplication_buffer a b result = 
  let open Lib.Buffer in 

    push_frame();
    let tempBuffer = create (size 6) (u64 0) in 
      let temp_zl = sub tempBuffer (size 0) (size 1) in 
      let temp_zh = sub tempBuffer (size 1) (size 1) in 
      let t0_buffer = sub tempBuffer (size 2) (size 1) in 
      let t1_buffer = sub tempBuffer (size 3) (size 1) in 
      let t2_buffer = sub tempBuffer (size 4) (size 1) in 
      let t3_buffer = sub tempBuffer (size 5) (size 1) in 
      let t_buffer = sub tempBuffer (size 2) (size 4) in 
    
  let x = index a (size 0) in 
  let a1 = index a (size 1) in 
  let a2 = index a (size 2) in 
  let a3 = index a (size 3) in 
  
  let b0 = index b (size 0) in 
  let b1 = index b (size 1) in 
  let b2 = index b (size 2) in 
  let b3 = index b (size 3) in 
  
  let f, t0 = mul64 b0 x in 
 
  let zl, zh = mul64 b1 x in 
  let k = add_carry (u64 0)  zl t0 temp_zl in (* temp0 = zl + t0 *) 
  let _ = add_carry k zh (u64 0) temp_zh in  
  let k = add_carry (u64 0) (index temp_zl (size 0)) (f <<. (size 32)) temp_zl in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) temp_zh in 
  let t0 = (index temp_zl (size 0)) in 
  let t1 = (index temp_zh (size 0)) in 

  let zl, zh = mul64 b2 x in 
  let k = add_carry  (u64 0)  zl t1 temp_zl  in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry  (u64 0) (index temp_zl (size 0)) (f >>. (size 32)) temp_zl in 
  let _ = add_carry k (index temp_zh (size 0)) (u64 0) temp_zh in 
  let t1 = (index temp_zl (size 0)) in 
  let t2 = (index temp_zh (size 0)) in 


  let zl, zh = mul64 b3 x in 
  let k = add_carry (u64 0) zl t2 temp_zl in 
  let _ = add_carry k zh (u64 0) temp_zh in 
  let k = add_carry (u64 0) (index temp_zl (size 0)) f temp_zl in 
  let _  = add_carry k (index temp_zh (size 0)) (u64 0) temp_zh in 
  let t2 = (index temp_zl (size 0)) in 
  let t3 = (index temp_zh (size 0)) in 

  let t4 = add_carry (u64 0) t3 f temp_zl in (*t3 == temp_zl *) 
  let k = sub_borrow (u64 0) t2 (f <<. (size 32)) temp_zh in 
    let t3 = (index temp_zl (size 0)) in 
    let t2 = (index temp_zh (size 0)) in 
  let k = sub_borrow k t3 (f >>. (size 32)) temp_zl in 
    let t3 = index temp_zl (size 0) in 
  let _ = sub_borrow k t4 (u64 0) temp_zh in  
    let t4 = (index temp_zh (size 0)) in  

  upd t_buffer (size 0) t0;
  upd t_buffer (size 1) t1; 
  upd t_buffer (size 2) t2;
  upd t_buffer (size 3) t3;

  let t4 = mm_round a1 b t4 t_buffer in 
  let t4 = mm_round a2 b t4 t_buffer in 
  let t4 = mm_round a3 b t4 t_buffer in 

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



#reset-options "--z3refresh --z3rlimit 100" 

val lemma_toDomain_reduce_prime3: a: int -> b: int -> c: int -> Lemma (toDomain_ ((a % prime) * (b % prime) * (c % prime)) = toDomain_ (a * b * c))

let lemma_toDomain_reduce_prime3 a b c = 
  inDomain_mod_is_not_mod ((a % prime) * (b % prime) * (c % prime));
  assert(a % prime * ((b % prime) * (c % prime)) % prime == (a % prime) * (b % prime) * (c % prime) % prime);
  lemma_mod_mul_distr_l a ((b % prime) * (c % prime)) prime;
  assert( (a % prime) * (b % prime) * (c % prime) % prime == (b % prime) * ((c % prime) * a) % prime);
  lemma_mod_mul_distr_l b ((c % prime) * a) prime;
  assert((a % prime) * (b % prime) * (c % prime) % prime == (a * b * (c % prime)) % prime);
  lemma_mod_mul_distr_r (a * b) c prime;
  assert((a % prime) * (b % prime) * (c % prime) % prime == (a * b * c) % prime);
  inDomain_mod_is_not_mod (a * b * c);
  assert(toDomain_ ((a % prime) * (b % prime) * (c % prime) % prime) = toDomain_ (a * b * c))


#reset-options "--z3refresh --z3rlimit 300" 
val lemma_toDomain_reduce_prime4: a: int -> b: int -> c: int -> d: nat -> Lemma (toDomain_ ((a % prime) * (b % prime) * (c % prime) * (d % prime)) = toDomain_ (a * b * c * d))

let lemma_toDomain_reduce_prime4 a b c d = 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let ap = a % prime in 
  let bp = b % prime in 
  let cp = c % prime in 
  let dp = d % prime in 
  inDomain_mod_is_not_mod (ap * bp * cp * dp);
    assert(toDomain_ (ap * bp * cp * dp) == toDomain_ ((ap * bp * cp * dp) % prime));
    assert_by_tactic (((ap * bp * cp * dp) % prime) == (ap * (bp * cp * dp)) % prime) canon;
    assert(((ap * bp * cp) * dp) % prime == (ap * (bp * cp * dp)) % prime);
    lemma_mod_mul_distr_l a (bp * cp * dp) prime;
    assert(((ap * bp * cp) * dp) % prime == (a * bp * cp * dp) % prime);
    assert_by_tactic (a * bp * cp * dp == (bp * (a * cp * dp))) canon;
    lemma_mod_mul_distr_l b (a * cp * dp) prime;
    assert(bp * (a * cp * dp) % prime == b * (a * cp * dp) % prime);
    assert_by_tactic (b * (a * cp * dp) == cp * (a * b * dp)) canon;
    assert((ap * bp * cp * dp) % prime == (cp * (a * b * dp)) % prime);
    lemma_mod_mul_distr_l c (a * b * dp) prime;
    assert((ap * bp * cp * dp) % prime == (c * (a * b * dp)) % prime);
    assert_by_tactic (c * (a * b * dp) == dp * (a * b * c)) canon;
    lemma_mod_mul_distr_l d (a * b * c) prime;
    assert((ap * bp * cp * dp) % prime == (d * (a * b * c)) % prime);
    assert_by_tactic (d * (a * b * c) == (a * b * c * d)) canon;
    inDomain_mod_is_not_mod (a * b * c * d)


let mm_cube_seq a= 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in  
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = cube_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    
    lemma_brackets5_twice (as_nat4 a_tuple) (as_nat4 a_tuple) (as_nat4 a_tuple) (modp_inv2 (pow2 256)) (modp_inv2 (pow2 256));
    lemma_mod_mul_distr_l ((as_nat4 a_tuple * modp_inv2 (pow2 256))  * (as_nat4 a_tuple * modp_inv2 (pow2 256))  * as_nat4 a_tuple) (modp_inv2 (pow2 256)) prime;
    lemma_brackets5 (as_nat4 a_tuple * modp_inv2 (pow2 256)) (as_nat4 a_tuple * modp_inv2 (pow2 256))  1 (as_nat4 a_tuple) (modp_inv2 (pow2 256));
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod ((as_nat4 a_tuple * modp_inv2 (pow2 256))  * (as_nat4 a_tuple * modp_inv2 (pow2 256))  * (as_nat4 a_tuple * modp_inv2 (pow2 256)) ) ;
    lemma_toDomain_reduce_prime3 (as_nat4 a_tuple * modp_inv2 (pow2 256)) (as_nat4 a_tuple * modp_inv2 (pow2 256)) (as_nat4 a_tuple * modp_inv2 (pow2 256));
    inDomain_mod_is_not_mod (fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a) * fromDomain_ (felem_seq_as_nat a));
    r


let mm_quatre_seq a= 
  let open FStar.Tactics in 
  let open FStar.Tactics.Canon in 
  let result = montgomery_multiplication_seq a a in 
  let resultFinal = montgomery_multiplication_seq result result in 
      modulo_distributivity_mult ((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) ((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) prime;
      assert_by_tactic (((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) * ((fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) == (fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a)) * (fromDomain_ (felem_seq_as_nat a))) canon;
  resultFinal


val lemma_multiplicationInDomainByNumber: a: felem4 -> b: int -> Lemma (fromDomain_ (as_nat4 a * b % prime) = b * fromDomain_ (as_nat4 a) % prime)

let lemma_multiplicationInDomainByNumber a b = 
  lemma_mod_mul_distr_l (as_nat4 a * b) (modp_inv2 (pow2 256)) prime;
  lemma_brackets_l (as_nat4 a) b (modp_inv2 (pow2 256));
  lemma_brackets (as_nat4 a) b (modp_inv2 (pow2 256));
  lemma_brackets1 (as_nat4 a) b (modp_inv2 (pow2 256));
  lemma_mod_mul_distr_r b (as_nat4 a * modp_inv2 (pow2 256)) prime
  

let mm_byTwo_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = shift_left_felem (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 2;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (2 * fromDomain_ (as_nat4 a_tuple));
    r


let mm_byThree_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByThree_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 3;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (3 * fromDomain_ (as_nat4 a_tuple));
    r


let mm_byFour_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByFour_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 4;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (4 * fromDomain_ (as_nat4 a_tuple)); 
    r


let mm_byEight_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByEight_tuple (a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple 8;
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (8 * fromDomain_ (as_nat4 a_tuple));
    r


let mm_byMinusThree_seq a = 
    let a0 = index a 0 in 
    let a1 = index a 1 in 
    let a2 = index a 2 in 
    let a3 = index a 3 in 
    let a_tuple = (a0, a1, a2, a3) in  
    
    let (r0, r1, r2, r3) = multByMinusThree_tuple(a0, a1, a2, a3) in 

    let r = create 4 (u64 0)  in 
    let r = upd r 0 r0 in
    let r = upd r 1 r1 in 
    let r = upd r 2 r2 in 
    let r = upd r 3 r3 in 
    let r_tuple = (r0, r1, r2, r3) in 
    lemma_multiplicationInDomainByNumber a_tuple (-3);
    lemmaFromDomainToDomain (as_nat4 r_tuple);
    inDomain_mod_is_not_mod (-3 * fromDomain_ (as_nat4 a_tuple));
    r

val lemmaDistributivityInDomain: a: int -> b: int -> Lemma (toDomain_ (a * (b % prime) % prime) = toDomain_ (a * b % prime))
  [SMTPat (toDomain_ (a * (b % prime) % prime))]

let lemmaDistributivityInDomain a b = 
  lemma_mod_mul_distr_r a b prime


val fsquarePowN: n: size_t -> a: felem -> Stack unit 
  (requires (fun h -> live h a /\ as_nat h a < prime)) 
  (ensures (fun h0 _ h1 -> modifies1 a h0 h1 /\  as_nat h1 a < prime /\ (let k = fromDomain_(as_nat h0 a) in as_nat h1 a = toDomain_ (pow k (pow2 (v n))))))
  
let fsquarePowN n a = 
  let h0 = ST.get() in  
  lemmaFromDomainToDomain (as_nat h0 a);
  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 =
    let k_before_d = as_nat h0 a in let k = fromDomain_ k_before_d in 
    as_nat h1 a = toDomain_ (pow k (pow2 i)) /\ 
    as_nat h1 a < prime /\ live h1 a /\ modifies1 a h0 h1 in 
  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
     montgomery_multiplication_buffer a a a; 
     let k = fromDomain_ (as_nat h0 a) in  
     inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ a) * fromDomain_ (as_nat h0_ a));
     lemmaFromDomainToDomainModuloPrime (let k = fromDomain_ (as_nat h0 a) in pow k (pow2 (v x)));
     modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime;
     pow_plus k  (pow2 (v x)) (pow2 (v x )); 
     pow2_double_sum (v x);
     inDomain_mod_is_not_mod (pow k (pow2 (v x + 1)))
  )


val fsquarePowNminusOne: n: size_t -> a: felem -> tempBuffer: felem -> Stack unit 
  (requires (fun h -> live h a /\ live h tempBuffer /\ as_nat h a < prime /\ disjoint a tempBuffer)) 
  (ensures (fun h0 _ h1 -> as_nat h1 a < prime /\ as_nat h1 tempBuffer < prime /\ modifies2 a tempBuffer h0 h1 
/\ (let k = fromDomain_ (as_nat h0 a) in  as_nat h1 a = toDomain_ (pow k (pow2 (v n))) /\ as_nat h1 tempBuffer = toDomain_ (pow
        k (pow2 (v n) -1 )))))

let fsquarePowNminusOne n a b = 
  let h0 = ST.get() in
  Lib.Buffer.upd b (size 0) (u64 1);
  Lib.Buffer.upd b (size 1) (u64 18446744069414584320);
  Lib.Buffer.upd b (size 2) (u64 18446744073709551615);
  Lib.Buffer.upd b (size 3) (u64 4294967294);

  let one = (u64 1, u64 18446744069414584320, u64 18446744073709551615, u64 4294967294) in 
  assert_norm (as_nat4 one = toDomain_(1));
  lemmaFromDomainToDomain (as_nat h0 a);

  let inv (h0: HyperStack.mem) (h1: HyperStack.mem) (i: nat) : Type0 = 
    let k = fromDomain_(as_nat h0 a) in 
    as_nat h1 b = toDomain_ (pow k (pow2 i - 1)) /\ as_nat h1 a < prime /\ live h1 a /\
    as_nat h1 a = toDomain_ (pow k (pow2 i)) /\ as_nat h1 b < prime /\ live h1 b /\ modifies2 a b h0 h1 in 

  for (size 0) n (inv h0) (fun x -> 
    let h0_ = ST.get() in 
    montgomery_multiplication_buffer b a b;
    montgomery_multiplication_buffer a a a;
    let k = fromDomain_ (as_nat h0 a) in 
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ b) * fromDomain_ (as_nat h0_ a));
    inDomain_mod_is_not_mod (fromDomain_ (as_nat h0_ a) * fromDomain_ (as_nat h0_ a));

    lemmaFromDomainToDomainModuloPrime (pow k (pow2 (v x) -1 ));
    lemmaFromDomainToDomainModuloPrime (pow k (pow2 (v x)));
    modulo_distributivity_mult (pow k (pow2 (v x) - 1)) (pow k (pow2 (v x))) prime;
    modulo_distributivity_mult (pow k (pow2 (v x))) (pow k (pow2 (v x))) prime;
    
    pow_plus k (pow2 (v x) -1 ) (pow2 (v x));
    pow_plus k (pow2 (v x)) (pow2 (v x));
    pow2_double_sum (v x);

    inDomain_mod_is_not_mod (pow k (pow2 (v x + 1)));
    inDomain_mod_is_not_mod (pow k (pow2 (v x + 1) - 1))
)

inline_for_extraction noextract   
val norm_part_one: a: felem -> tempBuffer: lbuffer uint64 (size 8) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat h a < prime)
  (ensures fun h0 _ h1 -> modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat h1 buffer_result < prime /\ 
  (let k = fromDomain_ (as_nat h0 a) in as_nat h1 buffer_result = toDomain_(pow k ((pow2 32 - 1) * pow2 224) % prime))))
    
let norm_part_one a tempBuffer = 
    let h0 = ST.get() in 
  Lib.Buffer.update_sub tempBuffer (size 0) (size 4) a;

  let buffer_a = Lib.Buffer.sub tempBuffer (size 0) (size 4) in 
  let buffer_b = Lib.Buffer.sub tempBuffer (size 4) (size 4) in 

  fsquarePowNminusOne (size 32) buffer_a buffer_b;
  fsquarePowN (size 224) buffer_b;

  let k = fromDomain_ (as_nat h0 a) in 
  lemmaFromDomainToDomainModuloPrime (pow k (pow2 32 - 1));
  let k_powers = pow k (pow2 32 - 1) in 
  let k_prime = k_powers % prime in 
  inDomain_mod_is_not_mod (pow k_prime (pow2 224));
  power_distributivity k_powers (pow2 224) prime;
  power_mult k (pow2 32 - 1) (pow2 224)
 
inline_for_extraction noextract   
val norm_part_two: a: felem -> tempBuffer: lbuffer uint64 (size 4) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  as_nat h a < prime)
  (ensures fun h0 _ h1 -> as_nat h1 tempBuffer < prime /\ modifies1 tempBuffer h0 h1 /\
    (let k = fromDomain_ (as_nat h0 a) in as_nat h1 tempBuffer = toDomain_(pow k (pow2 192) % prime)))
    
let norm_part_two a tempBuffer = 
  let h0 = ST.get() in 
  Lib.Buffer.copy tempBuffer a;
  fsquarePowN (size 192) tempBuffer;
  let k = fromDomain_ (as_nat h0 a) in 
  inDomain_mod_is_not_mod (pow k (pow2 192))

inline_for_extraction noextract   
val norm_part_three:a: felem -> tempBuffer: lbuffer uint64 (size 8) -> 
  Stack unit (requires fun h -> live h a /\ live h tempBuffer /\ disjoint a tempBuffer /\  
   as_nat h a < prime)   
  (ensures fun h0 _ h1 ->  modifies1 tempBuffer h0 h1 /\ (let buffer_result = gsub tempBuffer (size 4) (size 4) in as_nat h1 buffer_result < prime
    /\ (let k = fromDomain_ (as_nat h0 a) in as_nat h1 buffer_result = toDomain_(pow k ((pow2 94 - 1) * pow2 2) % prime))))

let norm_part_three a tempBuffer = 
  let h0 = ST.get() in 
  Lib.Buffer.update_sub tempBuffer (size 0) (size 4) a;

  let buffer_a = Lib.Buffer.sub tempBuffer (size 0) (size 4) in 
  let buffer_b = Lib.Buffer.sub tempBuffer (size 4) (size 4) in 

  fsquarePowNminusOne (size 94) buffer_a buffer_b;
  fsquarePowN (size 2) buffer_b;

  let k = fromDomain_ (as_nat h0 a) in 
  lemmaFromDomainToDomainModuloPrime (pow k (pow2 94 - 1));
  let k_powers = pow k (pow2 94 - 1) in 
  let k_prime = k_powers % prime in 
  inDomain_mod_is_not_mod (pow k_prime (pow2 2));
  power_distributivity k_powers (pow2 2) prime;
  power_mult k (pow2 94 - 1) (pow2 2)


val lemma_inDomainModulo: a: nat -> b: nat -> Lemma ((toDomain_ ((a % prime) * (b % prime) % prime) = toDomain_ (a * b % prime)))

let lemma_inDomainModulo a b = 
  lemma_mod_mul_distr_l a (b % prime) prime;
  lemma_mod_mul_distr_r a b prime


let lemmaEraseToDomainFromDomain z = 
  lemma_mod_mul_distr_l (z * z) z prime


val big_power: a: nat -> b: nat -> c: nat -> d: nat -> e: nat -> Lemma (pow a b * pow a c * pow a d * pow a e = pow a (b + c + d + e))

let big_power a b c d e = 
  assert(pow a b * pow a c * pow a d * pow a e = (pow a b * pow a c) * (pow a d * pow a e));
  pow_plus a b c;
  pow_plus a d e;
  pow_plus a (b + c) (d + e)


#reset-options "--z3refresh --z3rlimit 200"
let exponent a result tempBuffer = 
  let h0 = ST.get () in 

  let buffer_norm_1 = Lib.Buffer.sub  tempBuffer (size 0) (size 8) in 
    let buffer_result1 = Lib.Buffer.sub tempBuffer (size 4) (size 4) in 
  let buffer_result2 = Lib.Buffer.sub tempBuffer (size 8) (size 4) in 
  let buffer_norm_3 = Lib.Buffer.sub tempBuffer (size 12) (size 8) in 
    let buffer_result3 = Lib.Buffer.sub tempBuffer (size 16) (size 4) in 
 
  norm_part_one a buffer_norm_1;
  norm_part_two a buffer_result2;
  norm_part_three a buffer_norm_3;
  
    let h1 = ST.get() in 
  montgomery_multiplication_buffer buffer_result1 buffer_result2 buffer_result1;
    let h2 = ST.get() in 
  montgomery_multiplication_buffer buffer_result1 buffer_result3 buffer_result1;
    let h3 = ST.get() in 
  montgomery_multiplication_buffer buffer_result1 a buffer_result1;
    let h4 = ST.get() in 
  copy result buffer_result1; 
    let h5 = ST.get() in 
  
  let k = fromDomain_ (as_nat h0 a) in 
  let power1 = pow k ((pow2 32 - 1) * pow2 224) in 
  let power2 = pow k (pow2 192) in 
  let power3 = pow k ((pow2 94 - 1) * pow2 2) in 
  let power4 = pow k 1 in 

  lemma_inDomainModulo power1 power2;
  lemma_inDomainModulo (power1 * power2) power3;
  inDomain_mod_is_not_mod (((power1 * power2 * power3) % prime * power4));
  lemma_mod_mul_distr_l (power1 * power2 * power3) power4 prime;
  big_power k ((pow2 32 - 1) * pow2 224) (pow2 192) ((pow2 94 -1 ) * pow2 2) 1;
  assert_norm(((pow2 32 - 1) * pow2 224 + pow2 192 + (pow2 94 -1 ) * pow2 2 + 1) = prime - 2)

(*This code is taken from Curve25519, written by Polubelova M *)
val lemma_cswap2_step:
    bit:uint64{v bit <= 1}
  -> p1:uint64
  -> p2:uint64
  -> Lemma (
      let mask = u64 0 -. bit in
      let dummy = mask &. (p1 ^. p2) in
      let p1' = p1 ^. dummy in
      let p2' = p2 ^. dummy in
      if v bit = 1 then p1' == p2 /\ p2' == p1 else p1' == p1 /\ p2' == p2)
let lemma_cswap2_step bit p1 p2 =
  let mask = u64 0 -. bit in
  assert (v bit == 0 ==> v mask == 0);
  assert (v bit == 1 ==> v mask == pow2 64 - 1);
  let dummy = mask &. (p1 ^. p2) in
  logand_lemma mask (p1 ^. p2);
  assert (v bit == 1 ==> v dummy == v (p1 ^. p2));
  assert (v bit == 0 ==> v dummy == 0);
  let p1' = p1 ^. dummy in
  uintv_extensionality dummy (if v bit = 1 then (p1 ^. p2) else u64 0);
  logxor_lemma p1 p2;
  let p2' = p2 ^. dummy in
  logxor_lemma p2 p1
    
let cswap bit p1 p2 =
  let h0 = ST.get () in
  let mask = u64 0 -. bit in

  [@ inline_let]
  let inv h1 (i:nat{i <= 8}) =
    (forall (k:nat{k < i}).
      if v bit = 1
      then (as_seq h1 p1).[k] == (as_seq h0 p2).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p1).[k]
      else (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    (forall (k:nat{i <= k /\ k < 8}).
      (as_seq h1 p1).[k] == (as_seq h0 p1).[k] /\ (as_seq h1 p2).[k] == (as_seq h0 p2).[k]) /\
    modifies (loc p1 |+| loc p2) h0 h1 in

  Lib.Loops.for 0ul 12ul inv
    (fun i ->
      let dummy = mask &. (p1.(i) ^. p2.(i)) in
      p1.(i) <- p1.(i) ^. dummy;
      p2.(i) <- p2.(i) ^. dummy;
      lemma_cswap2_step bit ((as_seq h0 p1).[v i]) ((as_seq h0 p2).[v i])
    );
  let h1 = ST.get () in
  Lib.Sequence.eq_intro (as_seq h1 p1) (if v bit = 1 then as_seq h0 p2 else as_seq h0 p1);
  Lib.Sequence.eq_intro (as_seq h1 p2) (if v bit = 1 then as_seq h0 p1 else as_seq h0 p2)
