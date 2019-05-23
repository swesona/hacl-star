module Hacl.Spec.P256.Ladder

open Lib.IntTypes
open Lib.Buffer

open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication.PointAdd 
open Hacl.Spec.P256.MontgomeryMultiplication.PointDouble

open FStar.Math.Lemmas
open Lib.Sequence
open Lib.ByteSequence


type scalar = lbytes 32

let ith_bit (k:scalar) (i:nat{i < 256}) : uint64 =
	let q = i / 8 in let r = size (i % 8) in
 	to_u64 ((index k q >>. r) &. u8 1)

let pr = p:lseq uint64 4 {let t = sub p 0 4 in  felem_seq_as_nat t < prime}

assume val fromDomainPoint: tuple3 nat nat nat -> tuple3 nat nat nat
assume val toDomainPoint: tuple3 nat nat nat -> tuple3 nat nat nat

assume val point_add:  p: point_prime -> q: point_prime -> Tot (r: point_prime
  {
    let px, py, pz = felem_seq_as_nat(sub p 0 4), felem_seq_as_nat(sub p 4 4), felem_seq_as_nat(sub p 8 4) in 
    let qx, qy, qz = felem_seq_as_nat(sub q 0 4), felem_seq_as_nat(sub q 4 4), felem_seq_as_nat(sub q 8 4) in 
    let rx, ry, rz = felem_seq_as_nat(sub r 0 4), felem_seq_as_nat(sub r 4 4), felem_seq_as_nat(sub r 8 4) in 
    
    let pxD, pyD, pzD = fromDomainPoint (px, py, pz) in 
    let qxD, qyD, qzD = fromDomainPoint (qx, qy, qz) in 
    let rxD, ryD, rzD = fromDomainPoint (rx, ry, rz) in 
 
    let x3N, y3N, z3N = _point_add (pxD, pyD, pzD) (qxD, qyD, qzD) in 
    x3N == rxD /\ y3N == ryD /\ z3N == rzD
  }
)

assume val point_double:  p: point_prime -> Tot (r: point_prime
  {
    let px, py, pz = felem_seq_as_nat(sub p 0 4), felem_seq_as_nat(sub p 4 4), felem_seq_as_nat(sub p 8 4) in 
    let rx, ry, rz = felem_seq_as_nat(sub r 0 4), felem_seq_as_nat(sub r 4 4), felem_seq_as_nat(sub r 8 4) in 
    
    let pxD, pyD, pzD = fromDomainPoint (px, py, pz) in 
    let rxD, ryD, rzD = fromDomainPoint (rx, ry, rz) in 
 
    let x3N, y3N, z3N = _point_double (pxD, pyD, pzD) in
    x3N == rxD /\ y3N == ryD /\ z3N == rzD
  }
)


val _ml_step0: p: point_nat -> q: point_nat -> tuple2 point_nat point_nat

let _ml_step0 r0 r1 = 
  let r0 = _point_add r0 r1 in
  let r1 = _point_double r1 in 
  (r0, r1)

val _ml_step1: p: point_nat -> q: point_nat -> tuple2 point_nat point_nat

let _ml_step1 r0 r1 = 
  let r3 = _point_double r0 in 
  let r1 = _point_add r0 r1 in 
  (r3, r1)

(*changed to any size *)
val _ml_step: k: scalar-> i: nat{i < 256} -> p: point_nat -> q: point_nat -> Tot (r: tuple2 point_nat point_nat)

let _ml_step k i p q = 
    let bit = ith_bit k i in 
    let isZeroBit = eq #U64 bit (u64 0) in 
    if isZeroBit then 
      _ml_step0 p q 
    else _ml_step1 p q  

val montgomery_ladder_step0: p: point_prime -> q: point_prime -> 
  Tot (r: tuple2 point_prime point_prime 
    {
      let r0, r1 = r in 

      let x3_0 = felem_seq_as_nat (sub r0 0 4) in 
      let y3_0 = felem_seq_as_nat (sub r0 4 4) in
      let z3_0 = felem_seq_as_nat (sub r0 8 4) in 

      let x3_1 = felem_seq_as_nat (sub r1 0 4) in 
      let y3_1 = felem_seq_as_nat (sub r1 4 4) in 
      let z3_1 = felem_seq_as_nat (sub r1 8 4) in 
    
      let x1 = felem_seq_as_nat (sub p 0 4) in 
      let y1 = felem_seq_as_nat (sub p 4 4) in 
      let z1 = felem_seq_as_nat (sub p 8 4) in 
      
      let x2 = felem_seq_as_nat (sub q 0 4) in 
      let y2 = felem_seq_as_nat (sub q 4 4) in 
      let z2 = felem_seq_as_nat (sub q 8 4) in
    
      let pxD, pyD, pzD = fromDomainPoint (x1, y1, z1) in 
      let qxD, qyD, qzD = fromDomainPoint (x2, y2, z2) in 
      let x3D_0, y3D_0, z3D_0 = fromDomainPoint (x3_0, y3_0, z3_0) in
      let x3D_1, y3D_1, z3D_1 = fromDomainPoint (x3_1, y3_1, z3_1) in 

      let (x3N_0, y3N_0, z3N_0), (x3N_1, y3N_1, z3N_1) = _ml_step0 (pxD, pyD, pzD) (qxD, qyD, qzD) in 
      x3N_0 == x3D_0 /\ y3N_0 == y3D_0 /\ z3N_0 == z3D_0 /\ x3N_1 == x3D_1 /\ y3N_1 == y3D_1 /\ z3N_1 == z3D_1 
    }
 )   
    

let montgomery_ladder_step0 r0 r1 = 
  let r0 = point_add r0 r1 in 
  let r1 = point_double r1 in 
  (r0, r1)


val montgomery_ladder_step1: p: point_prime -> q: point_prime -> 
  Tot (r: tuple2 point_prime point_prime 
    {
      let r0, r1 = r in 

      let x3_0 = felem_seq_as_nat (sub r0 0 4) in 
      let y3_0 = felem_seq_as_nat (sub r0 4 4) in
      let z3_0 = felem_seq_as_nat (sub r0 8 4) in 

      let x3_1 = felem_seq_as_nat (sub r1 0 4) in 
      let y3_1 = felem_seq_as_nat (sub r1 4 4) in 
      let z3_1 = felem_seq_as_nat (sub r1 8 4) in 
    
      let x1 = felem_seq_as_nat (sub p 0 4) in 
      let y1 = felem_seq_as_nat (sub p 4 4) in 
      let z1 = felem_seq_as_nat (sub p 8 4) in 
      
      let x2 = felem_seq_as_nat (sub q 0 4) in 
      let y2 = felem_seq_as_nat (sub q 4 4) in 
      let z2 = felem_seq_as_nat (sub q 8 4) in
    
      let pxD, pyD, pzD = fromDomainPoint (x1, y1, z1) in 
      let qxD, qyD, qzD = fromDomainPoint (x2, y2, z2) in 
      let x3D_0, y3D_0, z3D_0 = fromDomainPoint (x3_0, y3_0, z3_0) in
      let x3D_1, y3D_1, z3D_1 = fromDomainPoint (x3_1, y3_1, z3_1) in 

      let r0N, r1N = _ml_step1 (pxD, pyD, pzD) (qxD, qyD, qzD) in 
      let (x3N_0, y3N_0, z3N_0) = r0N in 
      let (x3N_1, y3N_1, z3N_1) = r1N in 
    
      x3N_0 == x3D_0 /\  y3N_0 == y3D_0 /\  z3N_0 == z3D_0 /\ 
      x3N_1 == x3D_1 /\  y3N_1 == y3D_1 /\  z3N_1 == z3D_1 
    }
 )   


(*R0 ← 0
  R1 ← P
  for i from m downto 0 do
     if di = 0 then
        R1 ← point_add(R0, R1)
        R0 ← point_double(R0)
     else
        R0 ← point_add(R0, R1)
        R1 ← point_double(R1)
  return R0 *)


let montgomery_ladder_step1 r0 r1 = 
  let r1 = point_add r0 r1 in 
  let r0 = point_double r0 in  
  (r0, r1)

(*

val montgomery_ladder_step: k: scalar -> i: nat {i < 256} -> To
*)
