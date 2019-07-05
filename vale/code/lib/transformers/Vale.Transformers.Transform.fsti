(**

   This module exposes user-friendly transformers and lemmas for them.

   Each transformation takes 1 or more [va_code] object(s) and
   produces a [va_code] object, along with additional data. The lemma
   guarantees that the produced [va_code] object is semantically
   identical to the (first, if more than one) provided [va_code]
   object.

   The additional data that is generated is always a [pbool] which is
   [ttrue] if the transformation succeeded, and otherwise is a [ffalse
   reason].  Under both circumstances, the lemma mentioned above is
   held, and in particular, a failed transformation is still safe to
   use (since in that case, the code returned is exactly the same as
   the first [va_code] object). The additional data is provided only
   for debugging, since we expect that after debugging and fixing
   things, all transformations will succeed.

*)
module Vale.Transformers.Transform

open Vale.X64.Machine_s
open Vale.Def.PossiblyMonad
open Vale.X64.Decls

/// Common definitions amongst transformations.

let equiv_states (s1 s2:va_state) =
  let open Vale.X64.State in
  s1.vs_ok == s2.vs_ok /\
  Vale.X64.Regs.equal s1.vs_regs s2.vs_regs /\
  Vale.X64.Flags.sel fCarry s1.vs_flags == Vale.X64.Flags.sel fCarry s2.vs_flags /\
  Vale.X64.Flags.sel fOverflow s1.vs_flags == Vale.X64.Flags.sel fOverflow s2.vs_flags /\
  s1.vs_heap == s2.vs_heap /\
  s1.vs_stack == s2.vs_stack /\
  s1.vs_memTaint == s2.vs_memTaint /\
  s1.vs_stackTaint == s2.vs_stackTaint

noeq
type transformation_result = {
  success : pbool;
  result : va_code;
}

/// The Instruction Reordering Transformation

val reorder :
  orig:va_code ->
  hint:va_code ->
  transformation_result

val lemma_reorder :
  orig:va_code ->
  hint:va_code ->
  transformed:va_code ->
  va_s0:va_state -> va_sM:va_state -> va_fM:va_fuel ->
  Ghost (va_state & va_fuel)
    (requires (
        (va_require_total transformed (reorder orig hint).result va_s0) /\
        (va_get_ok va_s0) /\
        (va_ensure_total orig va_s0 va_sM va_fM) /\
        (va_get_ok va_sM)))
    (ensures (fun (va_sM', va_fM') ->
         (va_fM' == va_fM) /\
         (equiv_states va_sM va_sM') /\
         (va_ensure_total transformed va_s0 va_sM' va_fM') /\
         (va_get_ok va_sM')))
