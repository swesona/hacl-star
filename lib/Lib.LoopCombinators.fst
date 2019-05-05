module Lib.LoopCombinators

let rec repeat_left min max lo hi a f acc =
  if lo = hi then acc
  else repeat_left min max (lo + 1) hi a f (f lo acc)

let rec repeat_left_all_ml min max lo hi a f acc =
  if lo = hi then acc
  else repeat_left_all_ml min max (lo + 1) hi a f (f lo acc)

let rec repeat_right min max lo hi a f acc =
  if lo = hi then acc
  else f (hi - 1) (repeat_right min max lo (hi - 1) a f acc)

let rec repeat_right_plus min max lo mi hi a f acc =
  if hi = mi then ()
  else repeat_right_plus min max lo mi (hi - 1) a f acc

let unfold_repeat_right min max lo hi a f acc0 i = ()

let eq_repeat_right min max lo hi a f acc0 = ()

let rec repeat_left_right min max lo hi a f acc =
  if lo = hi then ()
  else
    begin
    repeat_right_plus min max lo (lo + 1) hi a f acc;
    repeat_left_right min max (lo + 1) hi a f (f lo acc)
    end

let repeat_gen max n a f acc0 =
  repeat_right 0 max 0 n a f acc0

let unfold_repeat_gen max n a f acc0 i = ()
(* // Proof when using [repeat_left]:
  repeat_left_right 0 (i + 1) a f acc0;
  repeat_left_right 0 i a f acc0
*)

let eq_repeat_gen0 max a f acc0 = ()

let fixed_i f (i:nat) = f

let repeati #a max n f acc0 =
  repeat_gen max n (fixed_a a) f acc0

let unfold_repeati #a max n f acc0 i =
  unfold_repeat_gen max n (fixed_a a) f acc0 i

let eq_repeati0 #a max f acc0 = ()

let repeati_def #a max n f acc0 = ()

let repeat #a max n f acc0 =
  repeati max n (fixed_i f) acc0

let eq_repeat0 #a max f acc0 = ()

let unfold_repeat #a max n f acc0 i =
  unfold_repeati #a max n (fixed_i f) acc0 i

let repeat_range #a min max f x =
  repeat_left min max min max (fun _ -> a) f x

let repeat_range_all_ml #a min max f x =
  repeat_left_all_ml min max min max (fun _ -> a) f x

let repeat_range_inductive #a min max pred f x =
  repeat_left min max min max (fun i -> x:a{pred i x}) f x

let repeati_inductive #a n pred f x0 =
  repeat_range_inductive #a 0 n pred f x0

let repeati_inductive_repeat_gen #a n pred f x0 =
  let a' i = x:a{pred i x} in
  let f' (i:nat{i < n}) (x:a' i) : y:a' (i + 1) = f i x in
  repeat_left_right 0 n 0 n (fun i -> x:a{pred i x}) f x0;
  assert_norm (repeati_inductive n pred f x0 == repeat_right 0 n 0 n (fun i -> a' i) f' x0);
  assert (repeat_gen n n (fun i -> x:a{pred i x}) f x0 == repeat_right 0 n 0 n a' f' x0);
  let repeat_right_eta
    (a:(i:nat{0 <= i /\ i <= n} -> Type))
    (f:(i:nat{0 <= i /\ i < n} -> a i -> a (i + 1)))
    (acc:a 0) :
    Lemma (repeat_right 0 n 0 n a f acc == repeat_right 0 n 0 n (fun i -> a i) f acc) = () in
  repeat_right_eta a' f' x0

let repeat_gen_inductive n a pred f x0 =
  let f' (i:nat{i < n})
         (x:a i{pred i x /\ x == repeat_gen n i a f x0})
         : x':a (i + 1){pred (i + 1) x' /\ x' == repeat_gen n (i + 1) a f x0}
         = f i x in
  repeat_gen n n (fun i -> x:a i{pred i x /\ x == repeat_gen n i a f x0}) f' x0

let repeati_inductive' #a n pred f x0 =
  let f'
    (i:nat{i < n})
    (x:a{pred i x /\ x == repeati n i f x0})
    : x':a{pred (i + 1) x' /\ x' == repeati n (i + 1) f x0}
    = f i x in
  repeat_gen n n (fun i -> x:a{pred i x /\ x == repeati n i f x0}) f' x0
