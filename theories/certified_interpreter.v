(** Proof of progress **)
(* (C) Rao Xiaojia, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith Omega.
From Wasm Require Export operations typing datatypes_properties typing opsem properties type_preservation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
(*Let administrative_instruction := administrative_instruction host_function.

Let to_e_list : seq basic_instruction -> seq administrative_instruction := @to_e_list _.
Let to_b_list : seq administrative_instruction -> seq basic_instruction := @to_b_list _.*)
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.
Let s_typing := @s_typing host_function.
(*Let reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=
  @reduce_simple _.
Let const_list : seq administrative_instruction -> bool := @const_list _.
Let lholed := lholed host_function.
Let lfilled : depth -> lholed -> seq administrative_instruction -> seq administrative_instruction -> bool :=
  @lfilled _.*)
Let inst_typing := @inst_typing host_function.
Let sglob : store_record -> instance -> nat -> option global := @sglob _.
Let smem_ind : store_record -> instance -> option nat := @smem_ind _.

Let host := host host_function.

Variable host_instance : host.

Let host_state := host_state host_instance.

Let host_application := @host_application host_function host_instance.

Let reduce : host_state -> store_record -> frame -> seq administrative_instruction ->
             host_state -> store_record -> frame -> seq administrative_instruction -> Prop
  := @reduce _ _.

Definition terminal_form (es: seq administrative_instruction) :=
  const_list es \/ es = [::AI_trap].

(* XXX copied the above from progress, probably some of it is redundant *)

(* TODO the return type will actually be a disjunction
 * to cover the terminal case *)
Definition interpret_one_step: forall s f es hs,
    (exists ts, config_typing s f es ts) ->
    {es' & {f' & {s' & {hs' &
      reduce hs s f es hs' s' f' es' /\
      (exists ts', config_typing s' f' es' ts')}}}}.
Admitted.

Theorem t_progress: forall s f es ts hs,
    config_typing s f es ts ->
    terminal_form es \/
    exists s' f' es' hs', reduce hs s f es hs' s' f' es'.
Proof.
  intros s f es ts hs Htype.
  assert (H_well_typed : exists ts, config_typing s f es ts).
  { exists ts. by assumption. }

  destruct (interpret_one_step hs H_well_typed)
  as [es' [f' [s' [hs' [Hstep _]]]]].

  right. (* TODO not accounting for the terminal case *)
  exists s', f', es', hs'.
  by apply Hstep.
Qed.

End Host.

