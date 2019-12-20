module MerkleTree.New.High.Correct

open FStar.Seq

open MerkleTree.New.High
open MerkleTree.New.High.Correct.Base
open MerkleTree.New.High.Correct.Insertion
open MerkleTree.New.High.Correct.Rhs
open MerkleTree.New.High.Correct.Flushing
open MerkleTree.New.High.Correct.Path

module S = FStar.Seq

module Insertion = MerkleTree.New.High.Correct.Insertion
module Rhs = MerkleTree.New.High.Correct.Rhs
module Flushing = MerkleTree.New.High.Correct.Flushing
module Path = MerkleTree.New.High.Correct.Path

module MTS = MerkleTree.Spec

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

/// Correctness of the high-level Merkle tree design

// We claim below statements as the correctness of the high-level Merkle tree design:
// 1) There is an invariant (`mt_inv`), and `create_mt` satisfies it.
// 2) The invariant is preserved for insertion and flushing.
// 3) Assuming the invariant, we can construct the specification (`mt_spec`) for a given tree.
// 4) Merkle paths generated by the design and the corresponding spec are equal.
// 5) Merkle path verification by the design and the spec give the same result.

type old_hashes (#hsz:pos) (mt:merkle_tree #hsz) =
  olds:hashess #hsz {S.length olds = 32 /\ mt_olds_inv #hsz #(MT?.hash_fun mt) 0 (MT?.i mt) olds}

noeq type mt_olds (#hsz:pos) =
| MTO: mt:merkle_tree #hsz {mt_wf_elts mt} ->
       olds:old_hashes #hsz mt ->
       mt_olds #hsz

val mto_inv: #hsz:pos -> mt_olds #hsz -> GTot Type0
let mto_inv #hsz mto =
  mt_inv (MTO?.mt mto) (MTO?.olds mto)

val mto_base: #hsz:pos -> mto:mt_olds #hsz -> GTot (hs:hashes #hsz{S.length hs = MT?.j (MTO?.mt mto)})
let mto_base #hsz mto =
  mt_base (MTO?.mt mto) (MTO?.olds mto)

val mto_spec:
  #hsz:pos ->
  mto:mt_olds #hsz {MT?.j (MTO?.mt mto) > 0} ->
  GTot (MTS.merkle_tree #hsz (log2c (MT?.j (MTO?.mt mto))))
let mto_spec #hsz mto =
  mt_spec (MTO?.mt mto) (MTO?.olds mto)

// `create_mt` is correct.

val create_mt_ok:
  hsz:pos -> f:MTS.hash_fun_t ->
  init:hash #hsz ->
  Lemma (empty_olds_inv #_ #f 0;
         mto_inv (MTO (mt_create hsz f init) (empty_hashes 32)))
let create_mt_ok hsz f init =
  Insertion.create_mt_inv_ok #_ #f init

// `mt_insert` is correct.

val mt_insert_ok:
  #hsz:pos -> 
  mto:mt_olds #hsz -> v:hash #hsz ->
  Lemma (requires mto_inv mto /\ mt_not_full (MTO?.mt mto))
        (ensures  mto_inv (MTO (mt_insert (MTO?.mt mto) v) (MTO?.olds mto)))
let mt_insert_ok #hsz mto v =
  Insertion.mt_insert_inv_preserved (MTO?.mt mto) v (MTO?.olds mto)

// `mt_flush_to` and `mt_flush` are correct.

val mt_flush_to_ok:
  #hsz:pos -> 
  mto:mt_olds #hsz ->
  idx:nat{idx >= MT?.i (MTO?.mt mto) /\ idx < MT?.j (MTO?.mt mto)} ->
  Lemma (requires mto_inv mto)
        (ensures  mto_inv (MTO (mt_flush_to (MTO?.mt mto) idx)
                               (mt_flush_to_olds #hsz #(MT?.hash_fun (MTO?.mt mto)) 0 (MT?.i (MTO?.mt mto)) idx (MT?.j (MTO?.mt mto))
                                 (MTO?.olds mto) (MT?.hs (MTO?.mt mto)))))
let mt_flush_to_ok #_ mto idx =
  Flushing.mt_flush_to_inv_preserved (MTO?.mt mto) (MTO?.olds mto) idx

val mt_flush_ok:
  #hsz:pos -> 
  mto:mt_olds #hsz ->
  Lemma (requires mto_inv mto /\ MT?.j (MTO?.mt mto) > MT?.i (MTO?.mt mto))
        (ensures  mto_inv (MTO (mt_flush_to (MTO?.mt mto) (MT?.j (MTO?.mt mto) - 1))
                               (mt_flush_to_olds #hsz #(MT?.hash_fun (MTO?.mt mto)) 0 (MT?.i (MTO?.mt mto))
                                 (MT?.j (MTO?.mt mto) - 1) (MT?.j (MTO?.mt mto))
                                 (MTO?.olds mto) (MT?.hs (MTO?.mt mto)))))
let mt_flush_ok #_ mto =
  Flushing.mt_flush_inv_preserved (MTO?.mt mto) (MTO?.olds mto)

// `mt_get_root` is correct.

val mt_get_root_ok:
  #hsz:pos -> 
  mto:mt_olds #hsz -> drt:hash #hsz ->
  Lemma (requires mto_inv mto)
        (ensures (let nmt, rt = mt_get_root (MTO?.mt mto) drt in
                 // Only `MT?.rhs` and `MT?.mroot` are changed.
                 MT?.i (MTO?.mt mto) == MT?.i nmt /\
                 MT?.j (MTO?.mt mto) == MT?.j nmt /\
                 MT?.hs (MTO?.mt mto) == MT?.hs nmt /\
                 // A Merkle tree with new `MT?.rhs` and `MT?.mroot` is valid.
                 mt_inv nmt (MTO?.olds mto) /\
                 // A returned root is indeed the Merkle root.
                 rt == MT?.mroot nmt))
let mt_get_root_ok #_ mto drt =
  Rhs.mt_get_root_inv_ok (MTO?.mt mto) drt (MTO?.olds mto)

// `mt_get_path` is correct.

val mt_get_path_ok:
  #hsz:pos -> 
  mto:mt_olds #hsz ->
  idx:nat{MT?.i (MTO?.mt mto) <= idx && idx < MT?.j (MTO?.mt mto)} ->
  drt:hash ->
  Lemma (requires mto_inv mto /\ MT?.j (MTO?.mt mto) > 0)
        (ensures (let f = (MT?.hash_fun (MTO?.mt mto)) in
                 let j, p, rt = mt_get_path (MTO?.mt mto) idx drt in
                 j == MT?.j (MTO?.mt mto) /\
                 mt_root_inv #_ #f (mto_base mto) hash_init false rt /\
                 S.head p == S.index (mto_base mto) idx /\
                 (assert (S.length (S.tail p) == mt_path_length idx (MT?.j (MTO?.mt mto)) false);
                 S.equal (path_spec idx (MT?.j (MTO?.mt mto)) false (S.tail p))
                         (MTS.mt_get_path #_ #f #(log2c j) (mto_spec mto) idx))))
let mt_get_path_ok #_ mto idx drt =
  Path.mt_get_path_inv_ok (MTO?.mt mto) (MTO?.olds mto) idx drt

// `mt_verify` is correct.

val mt_verify_ok:
  #hsz:pos -> #f:MTS.hash_fun_t ->
  k:nat ->
  j:nat{k < j} ->
  p:path #hsz {S.length p = 1 + mt_path_length k j false} ->
  rt:hash #hsz ->
  Lemma (mt_verify #_ #f k j p rt <==>
         MTS.mt_verify #_ #f #(log2c j)
           (path_spec k j false (S.tail p)) k (MTS.HRaw (S.head p)) (MTS.HRaw rt))
let mt_verify_ok #_ #f k j p rt =
  Path.mt_verify_ok #_ #f k j p rt
