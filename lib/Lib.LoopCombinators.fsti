module Lib.LoopCombinators

(**
* fold_left-like loop combinator:
* [ repeat_left lo hi a f acc == f (hi - 1) .. ... (f (lo + 1) (f lo acc)) ]
*
* e.g. [ repeat_left 0 3 (fun _ -> list int) Cons [] == [2;1;0] ]
*
* It satisfies
* [ repeat_left lo hi (fun _ -> a) f acc == fold_left (flip f) acc [lo..hi-1] ]
*
* A simpler variant with a non-dependent accumuator used to be called [repeat_range]
*)
inline_for_extraction
val repeat_left:
    min:nat
  -> max:nat{min <= max}
  -> lo:nat{min <= lo}
  -> hi:nat{lo <= hi /\ hi <= max}
  -> a:(i:nat{min <= i /\ i <= max} -> Type)
  -> f:(i:nat{min <= i /\ i < max} -> a i -> a (i + 1))
  -> acc:a lo
  -> Tot (a hi) (decreases (hi - lo))

inline_for_extraction
val repeat_left_all_ml:
    min:nat
  -> max:nat{min <= max}
  -> lo:nat{min <= lo}
  -> hi:nat{lo <= hi /\ hi <= max}
  -> a:(i:nat{min <= i /\ i <= max} -> Type)
  -> f:(i:nat{min <= i /\ i < max} -> a i -> FStar.All.ML (a (i + 1)))
  -> acc:a lo
  -> FStar.All.ML (a hi)

(**
* fold_right-like loop combinator:
* [ repeat_right lo hi a f acc == f (hi - 1) .. ... (f (lo + 1) (f lo acc)) ]
*
* e.g. [ repeat_right 0 3 (fun _ -> list int) Cons [] == [2;1;0] ]
*
* It satisfies
* [ repeat_right lo hi (fun _ -> a) f acc == fold_right f acc [hi-1..lo] ]
*)
val repeat_right:
    min:nat
  -> max:nat{min <= max}
  -> lo:nat{min <= lo}
  -> hi:nat{lo <= hi /\ hi <= max}
  -> a:(i:nat{min <= i /\ i <= max} -> Type)
  -> f:(i:nat{min <= i /\ i < max} -> a i -> a (i + 1))
  -> acc:a lo
  -> Tot (a hi) (decreases (hi - lo))

(** Splitting a repetition *)
val repeat_right_plus:
    min:nat
  -> max:nat{min <= max}
  -> lo:nat{min <= lo}
  -> mi:nat{lo <= mi}
  -> hi:nat{mi <= hi /\ hi <= max}
  -> a:(i:nat{min <= i /\ i <= max} -> Type)
  -> f:(i:nat{min <= i /\ i < max} -> a i -> a (i + 1))
  -> acc:a lo
  -> Lemma (ensures
      repeat_right min max lo hi a f acc ==
      repeat_right min max mi hi a f (repeat_right min max lo mi a f acc))
    (decreases hi)

(** Unfolding one iteration *)
val unfold_repeat_right:
    min:nat
  -> max:nat{min <= max}
  -> lo:nat{min <= lo}
  -> hi:nat{lo <= hi /\ hi <= max}
  -> a:(i:nat{min <= i /\ i <= max} -> Type)
  -> f:(i:nat{min <= i /\ i < max} -> a i -> a (i + 1))
  -> acc0:a lo
  -> i:nat{lo <= i /\ i < hi}
  -> Lemma (
      repeat_right min max lo (i + 1) a f acc0 ==
      f i (repeat_right min max lo i a f acc0))

val eq_repeat_right:
    min:nat
  -> max:nat{min <= max}
  -> lo:nat{min <= lo}
  -> hi:nat{lo <= hi /\ hi <= max}
  -> a:(i:nat{min <= i /\ i <= max} -> Type)
  -> f:(i:nat{min <= i /\ i < max} -> a i -> a (i + 1))
  -> acc0:a lo
  -> Lemma (repeat_right min max lo lo a f acc0 == acc0)

(**
* [repeat_left] and [repeat_right] are equivalent.
*
* This follows from the third duality theorem
* [ fold_right f acc xs = fold_left (flip f) acc (reverse xs) ]
*)
val repeat_left_right:
    min:nat
  -> max:nat{min <= max}
  -> lo:nat{min <= lo}
  -> hi:nat{lo <= hi /\ hi <= max}
  -> a:(i:nat{min <= i /\ i <= max} -> Type)
  -> f:(i:nat{min <= i /\ i < max} -> a i -> a (i + 1))
  -> acc:a lo
  -> Lemma (ensures repeat_right min max lo hi a f acc == repeat_left min max lo hi a f acc)
    (decreases (hi - lo))

(**
* Repetition starting from 0
*
* Defined as [repeat_right] for convenience, but [repeat_left] may be more
* efficient when extracted to OCaml.
*)

val repeat_gen:
    max:nat
  -> n:nat{n <= max}
  -> a:(i:nat{i <= max} -> Type)
  -> f:(i:nat{i < max} -> a i -> a (i + 1))
  -> acc0:a 0
  -> a n

(** Unfolding one iteration *)
val unfold_repeat_gen:
    max:nat
  -> n:nat{n <= max}
  -> a:(i:nat{i <= max} -> Type)
  -> f:(i:nat{i < max} -> a i -> a (i + 1))
  -> acc0:a 0
  -> i:nat{i < n}
  -> Lemma (repeat_gen max (i + 1) a f acc0 == f i (repeat_gen max i a f acc0))

val eq_repeat_gen0:
    max:nat
  -> a:(i:nat{i <= max} -> Type)
  -> f:(i:nat{i < max} -> a i -> a (i + 1))
  -> acc0:a 0
  -> Lemma (repeat_gen max 0 a f acc0 == acc0)

(**
* Repetition with a fixed accumulator type
*)

let fixed_a (a:Type) (i:nat) = a

val repeati:
    #a:Type
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a)
  -> acc0:a
  -> a

(** Unfolding one iteration *)
val unfold_repeati:
    #a:Type
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a)
  -> acc0:a
  -> i:nat{i < n}
  -> Lemma (repeati #a max (i + 1) f acc0 == f i (repeati #a max i f acc0))

val eq_repeati0:
    #a:Type
  -> max:nat
  -> f:(i:nat{i < max} -> a -> a)
  -> acc0:a
  -> Lemma (repeati #a max 0 f acc0 == acc0)

val repeati_def:
    #a:Type
  -> max:nat
  -> n:nat{n <= max}
  -> f:(i:nat{i < max} -> a -> a)
  -> acc:a
  -> Lemma (repeati max n f acc == repeat_right 0 max 0 n (fixed_a a) f acc)

val repeat:
    #a:Type
  -> max:nat
  -> n:nat{n <= max}
  -> f:(a -> a)
  -> acc0:a
  -> a

val eq_repeat0:
    #a:Type
  -> max:nat
  -> f:(a -> a)
  -> acc0:a
  -> Lemma (repeat #a max 0 f acc0 == acc0)

val unfold_repeat:
    #a:Type
  -> max:nat
  -> n:nat{n <= max}
  -> f:(a -> a)
  -> acc0:a
  -> i:nat{i < n}
  -> Lemma (repeat #a max (i + 1) f acc0 == f (repeat #a max i f acc0))

val repeat_range:
    #a:Type
  -> min:nat
  -> max:nat{min <= max}
  -> (s:nat{s >= min /\ s < max} -> a -> Tot a)
  -> a
  -> Tot a (decreases (max - min))

val repeat_range_all_ml:
    #a:Type
  -> min:nat
  -> max:nat{min <= max}
  -> (s:nat{s >= min /\ s < max} -> a -> FStar.All.ML a)
  -> a
  -> FStar.All.ML a

unfold
type repeatable (#a:Type) (#n:nat) (pred:(i:nat{i <= n} -> a -> Tot Type)) =
  i:nat{i < n} -> x:a{pred i x} -> y:a{pred (i+1) y}

val repeat_range_inductive:
    #a:Type
  -> min:nat
  -> max:nat{min <= max}
  -> pred:(i:nat{i <= max} -> a -> Type)
  -> f:repeatable #a #max pred
  -> x0:a{pred min x0}
  -> Tot (res:a{pred max res}) (decreases (max - min))

val repeati_inductive:
   #a:Type
 -> n:nat
 -> pred:(i:nat{i <= n} -> a -> Type)
 -> f:repeatable #a #n pred
 -> x0:a{pred 0 x0}
 -> res:a{pred n res}

val repeati_inductive_repeat_gen:
   #a:Type
 -> n:nat
 -> pred:(i:nat{i <= n} -> a -> Type)
 -> f:repeatable #a #n pred
 -> x0:a{pred 0 x0}
 -> Lemma (repeati_inductive n pred f x0 == repeat_gen n n (fun i -> x:a{pred i x}) f x0)

type preserves_predicate (n:nat)
     (a:(i:nat{i <= n} -> Type))
     (f:(i:nat{i < n} -> a i -> a (i + 1)))
     (pred:(i:nat{i <= n} -> a i -> Tot Type))=
  forall (i:nat{i < n}) (x:a i). pred i x ==> pred (i + 1) (f i x)

val repeat_gen_inductive:
   n:nat
 -> a:(i:nat{i <= n} -> Type)
 -> pred:(i:nat{i <= n} -> a i -> Type0)
 -> f:(i:nat{i < n} -> a i -> a (i + 1))
 -> x0:a 0
 -> Pure (a n)
   (requires preserves_predicate n a f pred /\ pred 0 x0)
   (ensures fun res -> pred n res /\ res == repeat_gen n n a f x0)

type preserves (#a:Type)
  (#n:nat)
  (f:(i:nat{i < n} -> a -> a))
  (pred:(i:nat{i <= n} -> a -> Tot Type)) =
  forall (i:nat{i < n}) (x:a). pred i x ==> pred (i + 1) (f i x)

val repeati_inductive':
  #a:Type
  -> n:nat
  -> pred:(i:nat{i <= n} -> a -> Type0)
  -> f:(i:nat{i < n} -> a -> a)
  -> x0:a
  -> Pure a
    (requires preserves #a #n f pred /\ pred 0 x0)
    (ensures fun res -> pred n res /\ res == repeati n n f x0)
