module Hacl.Spec.P256.Chain

open FStar.HyperStack.All
open FStar.HyperStack
open FStar.HyperStack.ST

module ST = FStar.HyperStack.ST
module HS = FStar.HyperStack

open Lib.IntTypes
open Lib.Buffer

open Hacl.Impl.Curve25519.Field64.Core
module C =  Hacl.Spec.Curve25519.Field64.Core
module D = Hacl.Spec.Curve25519.Field64.Definition
open  Hacl.Spec.P256.Core
open Hacl.Spec.P256.Lemmas
open Hacl.Spec.P256.Definitions
open Hacl.Spec.P256.SolinasReduction
open Hacl.Spec.P256.MontgomeryMultiplication
open Hacl.Spec.P256.MontgomeryMultiplication.PointDouble
open Hacl.Spec.P256.MontgomeryMultiplication.PointAdd


open Lib.Loops
open FStar.Math.Lemmas

module B = LowStar.Buffer
open FStar.Mul


open Hacl.Impl.P256

val chain: p: point_prime -> tempBuffer: lbuffer uint64 (size 100) ->  Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)

let chain p tempBuffer = 
  let tempBuffer32 = sub tempBuffer (size 0) (size 32) in 
  let tempBuffer88 = sub tempBuffer (size 0) (size 88) in 

  let tempBufferPoint = sub tempBuffer (size 88) (size 12) in 

    let h0 = ST.get() in 
  pointToDomain p p;
    let h1 = ST.get() in
    assert(point_x_as_nat h1 p == toDomain_ (point_x_as_nat h0 p) /\ point_y_as_nat h1 p == toDomain_ (point_x_as_nat h0 p) /\ point_z_as_nat h1 p == toDomain_ (point_z_as_nat h0 p) );
  point_double p p tempBuffer88;
    let h2 = ST.get() in 
    assert(as_seq #MUT #uint64 #12 h2 p == point_double_seq (as_seq #MUT #uint64 #12 h1 p));
    assert(
      let x = toDomain_ (point_x_as_nat h0 p) in 
      let y = toDomain_ (point_y_as_nat h0 p) in 
      let z = toDomain_ (point_z_as_nat h0 p) in 
      let xD = fromDomain_ x in let yD = fromDomain_ y in let zD = fromDomain_ z  in 
      let (xN, yN, zN) = _point_double (point_x_as_nat h0 p, point_y_as_nat h0 p, point_z_as_nat h0 p) in 
      point_x_as_nat h2 p == toDomain_ (xN) (*/\ point_y_as_nat h2 p == toDomain_ (yN) /\ point_z_as_nat h2 p == toDomain_ (zN)*));

   assert(let x = point_x_as_nat h1 p in let y = point_y_as_nat h1 p in let z = point_z_as_nat h1 p in let xD = fromDomain_ x in let yD = fromDomain_ y in let zD = fromDomain_ z  in 
  let (xN, yN, zN) = _point_double (xD, yD, zD) in 
  point_x_as_nat h2 p == toDomain_ (xN) (*/\ point_y_as_nat h2 p == toDomain_ (yN) /\ point_z_as_nat h2 p == toDomain_ (zN)*));
    
()    
  
