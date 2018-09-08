module Hacl.Impl.Aes.NI

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
open Lib.Utils
open Lib.Vec128


(* Parameters for AES-128 *)
noextract inline_for_extraction let nb =  4
noextract inline_for_extraction let nk =  4 // 4, 6, or 8 for 128/192/256
noextract inline_for_extraction let nr =  10 // 10, 12, or 14 for 128/192/256

type block = lbytes 16
type skey  = lbytes 16
type skey256  = lbytes 32

type state = lbuffer vec128 4
type key1 =  lbuffer vec128 1
type keyr =  lbuffer vec128 9
type keyex = lbuffer vec128 15 // Saving space for AES-256

inline_for_extraction
val aes_enc: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_enc st key = 
    st.(size 0) <- ni_aes_enc st.(size 0) key.(size 0);
    st.(size 1) <- ni_aes_enc st.(size 1) key.(size 0);
    st.(size 2) <- ni_aes_enc st.(size 2) key.(size 0);
    st.(size 3) <- ni_aes_enc st.(size 3) key.(size 0)

inline_for_extraction
val aes_enc_last: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let aes_enc_last st key = 
    st.(size 0) <- ni_aes_enc_last st.(size 0) key.(size 0);
    st.(size 1) <- ni_aes_enc_last st.(size 1) key.(size 0);
    st.(size 2) <- ni_aes_enc_last st.(size 2) key.(size 0);
    st.(size 3) <- ni_aes_enc_last st.(size 3) key.(size 0)

let rcon =  gcreateL [u8(0x8d); u8(0x01); u8(0x02); u8(0x04); u8(0x08); u8(0x10); u8(0x20); u8(0x40); u8(0x80); u8(0x1b); u8(0x36)]

inline_for_extraction
val aes_keygen_assist: ok:key1 -> ik:key1 -> rcon:uint8 -> ST unit
			     (requires (fun h -> live h ok /\ live h ik))
			     (ensures (fun h0 _ h1 -> live h1 ok /\ live h1 ik /\ modifies (loc_buffer ok) h0 h1))
let aes_keygen_assist ok ik rcon = 
    ok.(size 0) <- ni_aes_keygen_assist ik.(size 0) rcon		      


inline_for_extraction
val add_round_key: st:state -> key:key1 -> ST unit
			     (requires (fun h -> live h st /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let add_round_key st key = 
    st.(size 0) <- vec128_xor st.(size 0) key.(size 0);
    st.(size 1) <- vec128_xor st.(size 1) key.(size 0);
    st.(size 2) <- vec128_xor st.(size 2) key.(size 0);
    st.(size 3) <- vec128_xor st.(size 3) key.(size 0)

val enc_rounds: st:state -> key:keyr -> n:size_t -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let enc_rounds st key n = 
    let h0 = ST.get() in
    loop_nospec #h0 n st 
      (fun i -> aes_enc st (sub key i (size 1)))


inline_for_extraction
val block_cipher: st:state -> key:keyex -> n:size_t -> ST unit
	     (requires (fun h -> live h st /\ live h key))
	     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 key /\ modifies (loc_buffer st) h0 h1))
let block_cipher st key n = 
    let k0 = sub key (size 0) (size 1) in
    let kr = sub key (size 1) (size 9) in
    let kn = sub key (size 10) (size 1) in
    add_round_key st k0;
    enc_rounds st kr (n -. size 1);
    aes_enc_last st kn
   
inline_for_extraction 
val key_expansion_step: next:key1 -> prev:key1 -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc_buffer next) h0 h1))
let key_expansion_step next prev = 
    next.(size 0) <- vec128_shuffle32 next.(size 0) (vec128_shuffle32_spec (u8 3) (u8 3) (u8 3) (u8 3));
    let key = prev.(size 0) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    next.(size 0) <- vec128_xor next.(size 0) key


inline_for_extraction 
val key_expansion_step2: next:key1 -> prev:key1 -> ST unit
			     (requires (fun h -> live h prev /\ live h next))
			     (ensures (fun h0 _ h1 -> live h1 prev /\ live h1 next /\ modifies (loc_buffer next) h0 h1))
let key_expansion_step2 next prev = 
    next.(size 0) <- vec128_shuffle32 next.(size 0) (vec128_shuffle32_spec (u8 2) (u8 2) (u8 2) (u8 2));
    let key = prev.(size 0) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    let key = vec128_xor key (vec128_shift_left key (size 32)) in
    next.(size 0) <- vec128_xor next.(size 0) key


val key_expansion128: keyx:keyex -> key:skey -> ST unit
			     (requires (fun h -> live h keyx /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc_buffer keyx) h0 h1))
let key_expansion128 keyx key = 
    keyx.(size 0) <- vec128_load_le key;
    let h0 = ST.get() in
    (* I WOULD LIKE TO HAVE A LOOP HERE BUT AES_KEYGEN_ASSIST INSISTS ON AN IMMEDIATE RCON *)
    (* MAYBE WE SHOULD UNROLL ONLY THIS LOOP *)
    (* loop_nospec #h0 (size 10) keyx 
    (fun i -> 
       let prev = sub keyx i (size 1) in
       let next = sub keyx (i +. size 1) (size 1) in
       aes_keygen_assist next rcon.(i +. size 1);
       key_expansion_step next prev)
		     *)
       let prev = sub keyx (size 0) (size 1) in
       let next = sub keyx (size 1) (size 1) in
       aes_keygen_assist next prev (u8 0x01);
       key_expansion_step next prev;
       let prev = sub keyx (size 1) (size 1) in
       let next = sub keyx (size 2) (size 1) in
       aes_keygen_assist next prev (u8 0x02);
       key_expansion_step next prev;
       let prev = sub keyx (size 2) (size 1) in
       let next = sub keyx (size 3) (size 1) in
       aes_keygen_assist next prev (u8 0x04);
       key_expansion_step next prev;
       let prev = sub keyx (size 3) (size 1) in
       let next = sub keyx (size 4) (size 1) in
       aes_keygen_assist next prev (u8 0x08);
       key_expansion_step next prev;
       let prev = sub keyx (size 4) (size 1) in
       let next = sub keyx (size 5) (size 1) in
       aes_keygen_assist next prev (u8 0x10);
       key_expansion_step next prev;
       let prev = sub keyx (size 5) (size 1) in
       let next = sub keyx (size 6) (size 1) in
       aes_keygen_assist next prev (u8 0x20);
       key_expansion_step next prev;
       let prev = sub keyx (size 6) (size 1) in
       let next = sub keyx (size 7) (size 1) in
       aes_keygen_assist next prev (u8 0x40);
       key_expansion_step next prev;
       let prev = sub keyx (size 7) (size 1) in
       let next = sub keyx (size 8) (size 1) in
       aes_keygen_assist next prev (u8 0x80);
       key_expansion_step next prev;
       let prev = sub keyx (size 8) (size 1) in
       let next = sub keyx (size 9) (size 1) in
       aes_keygen_assist next prev (u8 0x1b);
       key_expansion_step next prev;
       let prev = sub keyx (size 9) (size 1) in
       let next = sub keyx (size 10) (size 1) in
       aes_keygen_assist next prev (u8 0x36);
       key_expansion_step next prev
       

val key_expansion256: keyx:keyex -> key:skey256 -> ST unit
			     (requires (fun h -> live h keyx /\ live h key))
			     (ensures (fun h0 _ h1 -> live h1 keyx /\ live h1 key /\ modifies (loc_buffer keyx) h0 h1))
let key_expansion256 keyx key = 
    keyx.(size 0) <- vec128_load_le (sub key (size 0) (size 16));
    keyx.(size 1) <- vec128_load_le (sub key (size 16) (size 16));
    let h0 = ST.get() in
    (* I WOULD LIKE TO HAVE A LOOP HERE BUT AES_KEYGEN_ASSIST INSISTS ON AN IMMEDIATE RCON *)
    (* MAYBE WE SHOULD UNROLL ONLY THIS LOOP *)
       let prev0 = sub keyx (size 0) (size 1) in
       let prev1 = sub keyx (size 1) (size 1) in
       let next0 = sub keyx (size 2) (size 1) in
       let next1 = sub keyx (size 3) (size 1) in
       aes_keygen_assist next0 prev1 (u8 0x01);
       key_expansion_step next0 prev0;
       aes_keygen_assist next1 next0 (u8 0x00);
       key_expansion_step2 next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (size 4) (size 1) in
       let next1 = sub keyx (size 5) (size 1) in
       aes_keygen_assist next0 prev1 (u8 0x02);
       key_expansion_step next0 prev0;
       aes_keygen_assist next1 next0 (u8 0x00);
       key_expansion_step2 next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (size 6) (size 1) in
       let next1 = sub keyx (size 7) (size 1) in
       aes_keygen_assist next0 prev1 (u8 0x04);
       key_expansion_step next0 prev0;
       aes_keygen_assist next1 next0 (u8 0x00);
       key_expansion_step2 next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (size 8) (size 1) in
       let next1 = sub keyx (size 9) (size 1) in
       aes_keygen_assist next0 prev1 (u8 0x08);
       key_expansion_step next0 prev0;
       aes_keygen_assist next1 next0 (u8 0x00);
       key_expansion_step2 next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (size 10) (size 1) in
       let next1 = sub keyx (size 11) (size 1) in
       aes_keygen_assist next0 prev1 (u8 0x10);
       key_expansion_step next0 prev0;
       aes_keygen_assist next1 next0 (u8 0x00);
       key_expansion_step2 next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (size 12) (size 1) in
       let next1 = sub keyx (size 13) (size 1) in
       aes_keygen_assist next0 prev1 (u8 0x20);
       key_expansion_step next0 prev0;
       aes_keygen_assist next1 next0 (u8 0x00);
       key_expansion_step2 next1 prev1;
       let prev0 = next0 in
       let prev1 = next1 in
       let next0 = sub keyx (size 14) (size 1) in
       aes_keygen_assist next0 prev1 (u8 0x40);
       key_expansion_step next0 prev0
    
       

inline_for_extraction
val aes_block: st:state -> keyx:keyex -> nonce:state -> counter:size_t -> rounds:size_t -> ST unit
			     (requires (fun h -> live h st /\ live h keyx /\ live h nonce))
			     (ensures (fun h0 _ h1 -> live h1 st /\ live h1 nonce /\ live h1 keyx /\ modifies (loc_buffer st) h0 h1))
let aes_block st keyx nonce counter rounds = 
    let counter0 = htobe32 (size_to_uint32 counter) in
    let counter1 = htobe32 (size_to_uint32 (counter +. size 1)) in
    let counter2 = htobe32 (size_to_uint32 (counter +. size 2)) in
    let counter3 = htobe32 (size_to_uint32 (counter +. size 3)) in
    st.(size 0) <- vec128_insert32 nonce.(size 0) counter0 (u8 3);
    st.(size 1) <- vec128_insert32 nonce.(size 0) counter1 (u8 3);
    st.(size 2) <- vec128_insert32 nonce.(size 0) counter2 (u8 3);
    st.(size 3) <- vec128_insert32 nonce.(size 0) counter3 (u8 3);
    block_cipher st keyx rounds

inline_for_extraction noextract
val aes_alloc: rounds:size_t -> StackInline (keyex * key1)
			     (requires (fun h -> True))
			     (ensures (fun h0 (x,y) h1 -> live h1 x /\ live h1 y))
let aes_alloc rounds = 
  let keyex = alloca vec128_zero 15ul in
  let nonce = alloca vec128_zero 1ul in
  (keyex,nonce)


inline_for_extraction
val aes_init_nonce: nvec:key1 -> nonce:lbytes 12 -> ST unit
			     (requires (fun h -> live h nonce /\ live h nvec))
			     (ensures (fun h0 b h1 -> modifies (loc_buffer nvec) h0 h1))
let aes_init_nonce nvec nonce = 
  push_frame();
  let nb = alloca 0uy 16ul in
  blit nonce (size 0) nb (size 0) (size 12);
  nvec.(size 0) <- vec128_load_le nb;
  pop_frame()


inline_for_extraction
val aes128_init: keyx:keyex -> nvec:key1 -> key:skey -> nonce:lbytes 12 -> ST unit
			     (requires (fun h -> live h keyx /\ live h nonce /\ live h nvec /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc_union (loc_buffer keyx) (loc_buffer nvec)) h0 h1))
let aes128_init keyx (nvec:key1) key nonce = 
  push_frame();
  key_expansion128 keyx key ; 
  aes_init_nonce nvec nonce;
  pop_frame()


inline_for_extraction
val aes128_key_block: kb:lbytes 16 -> keyx:keyex -> nvec:key1 -> counter:size_t -> ST unit
			     (requires (fun h -> live h kb /\ live h keyx /\ live h nvec))
			     (ensures (fun h0 _ h1 -> live h1 kb /\ live h1 nvec /\ live h1 keyx /\ modifies (loc_buffer kb) h0 h1))
let aes128_key_block kb keyx nvec counter = 
    push_frame();
    let st = alloca vec128_zero 4ul in
    aes_block st keyx nvec counter (size 10);
    vec128_store_le kb st.(size 0);
    pop_frame()
    


inline_for_extraction
val aes256_init: keyx:keyex -> nvec:key1 -> key:skey -> nonce:lbytes 12 -> ST unit
			     (requires (fun h -> live h keyx /\ live h nonce /\ live h nvec /\ live h key))
			     (ensures (fun h0 b h1 -> modifies (loc_union (loc_buffer keyx) (loc_buffer nvec)) h0 h1))
let aes256_init keyx (nvec:key1) key nonce = 
  push_frame();
  key_expansion256 keyx key ; 
  aes_init_nonce nvec nonce;
  pop_frame()


inline_for_extraction
val aes_update4: out:lbytes 64 -> inp:lbytes 64 -> keyx:keyex -> nvec:key1 -> counter:size_t -> rounds:size_t -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h keyx /\ live h nvec))
			     (ensures (fun h0 b h1 -> modifies (loc_buffer out) h0 h1))
let aes_update4 out inp keyx nvec ctr rounds =
  push_frame();
  let st = alloca vec128_zero 4ul in
  aes_block st keyx nvec ctr rounds;
  st.(size 0) <- vec128_xor st.(size 0) (vec128_load_le (sub inp (size 0) (size 16)));
  st.(size 1) <- vec128_xor st.(size 1) (vec128_load_le (sub inp (size 16) (size 16)));
  st.(size 2) <- vec128_xor st.(size 2) (vec128_load_le (sub inp (size 32) (size 16)));
  st.(size 3) <- vec128_xor st.(size 3) (vec128_load_le (sub inp (size 48) (size 16)));
  vec128_store_le (sub out (size 0) (size 16)) st.(size 0);
  vec128_store_le (sub out (size 16) (size 16)) st.(size 1);
  vec128_store_le (sub out (size 32) (size 16)) st.(size 2);
  vec128_store_le (sub out (size 48) (size 16)) st.(size 3);
  pop_frame()

val aes_ctr: out:bytes -> inp:bytes -> len:size_t -> keyx:keyex -> nvec:key1 -> counter:size_t -> rounds:size_t -> ST unit
			     (requires (fun h -> live h out /\ live h inp /\ live h keyx /\ live h nvec))
			     (ensures (fun h0 _ h1 -> modifies (loc_buffer out) h0 h1))
let aes_ctr out inp len kex nvec counter rounds = 
  push_frame();
  let blocks64 = len /. size 64 in
  let h0 = ST.get() in
  loop_nospec #h0 blocks64 out 
    (fun i -> 
      let ctr = counter +. (i *. size 4) in
      let ib = sub inp (i *. size 64) (size 64) in
      let ob = sub out (i *. size 64) (size 64) in
      aes_update4 ob ib kex nvec ctr rounds);
  let rem = len %. size 64 in
  if (rem >. size 0) then (
      let ctr = counter +. (blocks64 *. size 4) in
      let ib = sub inp (blocks64 *. size 64) rem in
      let ob = sub out (blocks64 *. size 64) rem in
      let last = alloca 0uy 64ul in
      blit ib (size 0) last (size 0) rem;
      aes_update4 last last kex nvec ctr rounds;
      blit last (size 0) ob (size 0) rem);
  pop_frame()

let aes128_ctr_encrypt out inp in_len k n c = 
  push_frame();
  let (kex,nvec) = aes_alloc (size 10) in
  aes128_init kex nvec k n;
  aes_ctr out inp in_len kex nvec c (size 10);
  pop_frame()

let aes128_ctr_decrypt out inp in_len k n c = 
  aes128_ctr_encrypt out inp in_len k n c

let aes256_ctr_encrypt out inp in_len k n c = 
  push_frame();
  let (kex,nvec) = aes_alloc (size 14) in
  aes256_init kex nvec k n;
  aes_ctr out inp in_len kex nvec c (size 14);
  pop_frame()

let aes256_ctr_decrypt out inp in_len k n c = 
  aes128_ctr_encrypt out inp in_len k n c
