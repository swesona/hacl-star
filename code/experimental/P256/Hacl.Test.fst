module Hacl.Test

open Lib.IntTypes
open FStar.Math.Lemmas
open FStar.Mul

open Lib.Sequence
open Lib.ByteSequence

friend Lib.ByteSequence 

#set-options "--z3rlimit 100"

val lemma_core1: k: lseq uint64 4 -> Lemma
    (nat_from_bytes_le (uints_to_bytes_le k) == nat_from_intseq_le k)


let lemma_core1 k = 
  lemma_nat
