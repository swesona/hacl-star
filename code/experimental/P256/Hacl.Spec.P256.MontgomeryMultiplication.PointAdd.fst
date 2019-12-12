module Hacl.Spec.P256.MontgomeryMultiplication.PointAdd

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Math.Lib
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions

open Lib.Sequence

open Hacl.Spec.P256.MontgomeryMultiplication
open Lib.Loops
open FStar.Mul
open Hacl.Spec.P256

open Hacl.Spec.P256.MontgomeryMultiplication.PointDouble

let prime = prime256

#reset-options "--z3rlimit 300"  


val lemma_xToSpecification: 
  x1D: nat -> y1D: nat -> z1D: nat -> x2D: nat -> y2D: nat -> z2D: nat -> 
  
  u1: nat{u1 = toDomain_ (z2D * z2D * x1D % prime)} -> 
  u2: nat{u2 = toDomain_ (z1D * z1D * x2D % prime)} -> 
  
  s1: nat{s1 = toDomain_ (z2D * z2D * z2D * y1D % prime)} -> 
  s2: nat{s2 = toDomain_ (z1D * z1D * z1D * y2D % prime)} ->

  x3: nat{ 
    let u1D, u2D = fromDomain_ u1, fromDomain_ u2 in 
    let s1D, s2D = fromDomain_ s1, fromDomain_ s2 in  
    (u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0) ==> 
      (let (xN, yN, zN) = _point_double (x1D, y1D, z1D) in fromDomain_ x3 == xN)} -> 
   y3: nat{
    let u1D, u2D = fromDomain_ u1, fromDomain_ u2 in 
    let s1D, s2D = fromDomain_ s1, fromDomain_ s2 in  
    (u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0) ==> 
      (let (xN, yN, zN) = _point_double (x1D, y1D, z1D) in fromDomain_ y3 == yN)} ->
   z3: nat{
     let u1D, u2D = fromDomain_ u1, fromDomain_ u2 in 
     let s1D, s2D = fromDomain_ s1, fromDomain_ s2 in  
     (u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0) ==>
       (let (xN, yN, zN) = _point_double (x1D, y1D, z1D) in fromDomain_ z3 == zN)}
  ->  
  Lemma 
  (    
    let (xN, yN, zN) = _point_add (x1D, y1D, z1D) (x2D, y2D, z2D) in
    let x3D, y3D, z3D = fromDomainPoint (x3,  y3,  z3) in 
    let u1D = fromDomain_ u1 in let u2D = fromDomain_ u2 in 
    let s1D = fromDomain_ s1 in let s2D = fromDomain_ s2 in 
    (u1D = u2D && s1D = s2D && z1D <> 0 && z2D <> 0)  ==> (xN == x3D /\ yN == y3D /\ zN == z3D)
  )


let lemma_xToSpecification x1D y1D z1D x2D y2D z2D u1 u2 s1 s2  x3 y3 z3 = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
    let u1D = fromDomain_ u1 in let u2D = fromDomain_ u2 in 
    let s1D = fromDomain_ s1 in let s2D = fromDomain_ s2 in  
    
    let (xN, yN, zN) = _point_add (x1D, y1D, z1D) (x2D, y2D, z2D) in 
    let (xDouble, yDouble, zDouble) = _point_double (x1D, y1D, z1D) in 

    let u1N = x1D * z2D * z2D % prime in 
    let u2N = x2D * z1D * z1D % prime in 
    let s1N = y1D * z2D * z2D * z2D % prime in 
    let s2N = y2D * z1D * z1D * z1D % prime in 

    assert_by_tactic (x1D * z2D * z2D = x1D * (z2D * z2D)) canon;
    assert_by_tactic (x2D * z1D * z1D = x2D * (z1D * z1D)) canon;
    
    assert_by_tactic (y1D * z2D * (z2D * z2D) = y1D * z2D * z2D * z2D) canon;
    assert_by_tactic (y2D * z1D * (z1D * z1D) = y2D * z1D * z1D * z1D) canon;


     lemmaToDomainAndBackIsTheSame (u1N);
     lemmaToDomainAndBackIsTheSame (u2N);
     lemmaToDomainAndBackIsTheSame (s1N);
     lemmaToDomainAndBackIsTheSame (s2N)
     

noextract       
val lemma_xToSpecification_after_double: 
  pxD: nat -> pyD: nat -> pzD: nat -> 
  qxD: nat -> qyD: nat -> qzD: nat -> 
  x3: nat -> y3: nat -> z3: nat -> 
  u1: nat -> u2: nat -> s1: nat -> s2: nat -> 
  h: nat -> r: nat -> 
  Lemma
    (requires (    
      let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in 

      let u1D, u2D = fromDomain_ u1, fromDomain_ u2 in 
      let s1D, s2D = fromDomain_ s1, fromDomain_ s2 in 
      let rD = fromDomain_ r in    
      let hD = fromDomain_ h in 
     
      u1 == toDomain_ (qzD * qzD * pxD % prime256) /\
      u2 == toDomain_ (pzD * pzD * qxD % prime256) /\
      s1 == toDomain_ (qzD * qzD * qzD * pyD % prime256) /\
      s2 == toDomain_ (pzD * pzD * pzD * qyD % prime256) /\
      
      h == toDomain_ ((u2D - u1D) % prime256) /\
      r == toDomain_ ((s2D - s1D) % prime256) /\

      (
	if (not (fromDomain_ u1 = fromDomain_ u2 && fromDomain_ s1 = fromDomain_ s2 && pzD <> 0 && qzD <> 0)) then 
	(
	  if qzD = 0 then 
	    fromDomain_ x3 == pxD /\ fromDomain_ y3 == pyD /\ fromDomain_ z3 == pzD
	  else if pzD = 0 then 
	    fromDomain_ x3 == qxD /\  fromDomain_ y3 == qyD /\  fromDomain_ z3 == qzD 
	  else
	    x3 == toDomain_ ((rD * rD - hD * hD * hD - 2 * hD * hD * u1D) % prime) /\
	    y3 == toDomain_ (((hD * hD * u1D - x3D) * rD - s1D * hD*hD*hD) % prime) /\
	    z3 == toDomain_ ((pzD * qzD * hD) % prime)
	)
	else True)
      )
  )
  (ensures 
  (    
    let x3D, y3D, z3D = fromDomain_ x3, fromDomain_ y3, fromDomain_ z3 in 
    let (xN, yN, zN) = _point_add (pxD, pyD, pzD) (qxD, qyD, qzD) in
    let u1D = fromDomain_ u1 in let u2D = fromDomain_ u2 in 
    let s1D = fromDomain_ s1 in let s2D = fromDomain_ s2 in 
    if (not(u1D = u2D && s1D = s2D && pzD <> 0 && qzD <> 0)) then
      xN == x3D /\  yN == y3D /\ zN == z3D
    else True
  )
)


let lemma_xToSpecification_after_double x1D y1D z1D x2D y2D z2D x3 y3 z3  u1 u2 s1 s2 h r = 
    let open FStar.Tactics in 
    let open FStar.Tactics.Canon in 
    
    let u1D = fromDomain_ u1 in 
    let u2D = fromDomain_ u2 in 
    let s1D = fromDomain_ s1 in 
    let s2D = fromDomain_ s2 in 

    let hD = fromDomain_ h in 
    let rD = fromDomain_ r in 
    
    let (xN, yN, zN) = _point_add (x1D, y1D, z1D) (x2D, y2D, z2D) in 

    let u1N = x1D * z2D * z2D % prime in
    let u2N = x2D * z1D * z1D % prime in 
    let s1N = y1D * z2D * z2D * z2D % prime in 
    let s2N = y2D * z1D * z1D * z1D % prime in 

    let hN = (u2N - u1N) % prime in 
    let rN = (s2N - s1N) % prime in 

    assert_by_tactic (x1D * z2D * z2D = (z2D * z2D) * x1D) canon;
    assert_by_tactic (x1D * (z2D * z2D) == z2D * z2D * x1D) canon;
    
    assert_by_tactic (x2D * z1D * z1D = x2D * (z1D * z1D)) canon;
    assert_by_tactic (z1D * z1D * x2D = x2D * (z1D * z1D)) canon;

    assert_by_tactic (z2D * z2D * z2D * y1D = y1D * z2D * (z2D * z2D)) canon;  
    assert_by_tactic (z1D * z1D * z1D * y2D = y2D * z1D * (z1D * z1D)) canon;

    assert_by_tactic (z1D * z2D * hD = hD * z1D * z2D) canon;
    assert_by_tactic ((rD * (u1D * (hD * hD) - xN) - s1D * (hD * hD * hD)) = ((hD * hD * u1D - xN) * rD - s1D * hD*hD*hD)) canon;
    
    assert_by_tactic (forall (n: nat). n * hN * hN = n * (hN * hN)) canon; 
    assert_by_tactic (2 * hD * hD * u1D = 2 * u1D * hD * hD) canon

assume val lemma_point_add_0: a: int -> b: int -> c: int -> Lemma 
  ((a - b - 2 * (c % prime256)) % prime256 == (a - b - 2 * c) % prime256)

assume val lemma_point_add_1: a: int -> b: int -> c: int -> d: int -> e: int -> Lemma
  ((((a % prime256) - b) * c - d * (e % prime256)) % prime256 ==((a - b) * c - d * e) % prime256)
