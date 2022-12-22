From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
From Wasm Require Export typing opsem properties interpreter_func.

(* Search (reduce _ _ _ ([::_]) _ _ _ _). *)
Type [::2] ++ [::1].

Section intro.

  Variable host_function : eqType.

  Let store_record := store_record host_function.
  Let function_closure := function_closure host_function.
  Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
        @e_typing _.
  Let s_typing := @s_typing host_function.
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

  Let reduce_trans := @reduce_trans host_function host_instance.

  Let config_tuple := config_tuple host_instance.


  Lemma test: forall {T: Type} (s: T) Q P ,
      ((exists s, Q s) -> P) -> (Q s) -> P.
  Proof.
    move => T s Q P Himpl HQ.
    apply Himpl; eexists; by apply HQ.
    (* equivalently(?):
       apply Himpl. eexists. apply HQ.
     *)
  Qed.

  (* TODO is there a nicer way to search for [(x = y)|(y = x)]? *)
  Search [
    (?xs ++ rcons ?ys ?y = rcons (?xs ++ ?ys) ?y)
    | (rcons (?xs ++ ?ys) ?y = ?xs ++ rcons ?ys ?y)
  ].

  (* Reduction of a sequence of commands.
     There's no `explicit` rule that allows this to be possible, yet this is certainly an expected behaviour.
 *)
  Lemma opsem_reduce_seq1: forall hs1 s1 f1 es1 hs2 s2 f2 es2 es0,
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (es1 ++ es0) hs2 s2 f2 (es2 ++ es0).
  Proof.
    move => hs1 s1 f1 es1 hs2 s2 f2 es2 es0.
    (* TODO read up on `induction using` *)
    induction es0 as [|es0 e IHes0] using last_ind.
    - (* Base case: just need to use es ++ [::] = es *)
      intros H. repeat rewrite cats0. apply H.
    - (* Inductive case *)
      intros H. apply IHes0 in H as IHes0'.
      (* Now need to frame off the e at the end *)
      repeat rewrite <- rcons_cat.
      (* No longer matters that the list is a concatenation *)
      remember (es1 ++ es0) as es10. remember (es2 ++ es0) as es20.
      (* Go from `rcons es10 e` to `es10 ++ [::e]` *)
      repeat rewrite <- cats1.
      (* Not sure how this works precisely but it gives me the subgoals I wanted.
         Found this used for applying r_label elsewhere in the code.
         Need to read up on automation.
         How is eapply different to apply? They seem to produce the same results here. *)
      eapply r_label; eauto; try apply/lfilledP.
      (* Should I even be proving this? is there a lemma to get this directly? *)
        * assert (LF: lfilledInd 0 (LH_base [::] [::e]) es10 (es10 ++ [::e])).
          (* How is this different from just `apply LfilledBase.`? Just extra automation? *)
          { by apply LfilledBase. }
          apply LF.
        * (* Repetition from above. Any point in factoring this out? *)
          assert (LF: lfilledInd 0 (LH_base [::] [::e]) es20 (es20 ++ [::e])).
          { by apply LfilledBase. }
          apply LF.
  Qed.

  (* XXX LFilledBase might come in useful *)
  (* Now note that given Wasm's representation of value stack squashed into the
      * instruction list, adding more constants to the bottom of the value
      * stack should not matter as well. *)
  Lemma opsem_reduce_seq2: forall hs1 s1 f1 es1 hs2 s2 f2 es2 vs,
      const_list vs ->
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (vs ++ es1) hs2 s2 f2 (vs ++ es2).
  Proof.
    move => hs1 s1 f1 es1 hs2 s2 f2 es2 vs Hvs Hes1es2.
    induction vs.
    - apply Hes1es2.
      (*
         why is IHvs now (a->c) and not (a->b->c)?
         did Coq automatically notice b holds?
      *)
    - inversion Hvs as [Hvs'].
      (* this could be used for IHvs? *)
      (* could reflection be used instead of andb_true_iff? *)
      apply Bool.andb_true_iff in Hvs' as [const_a const_vs].
      apply IHvs in const_vs as H_vs_es1_es2.
      simpl.
      remember (vs ++ es1) as vs_es1.
      remember (vs ++ es2) as vs_es2.

  Admitted.

  (* This lemma can of course be derived from the two above. However, its proof itself is
     even simpler. *)
  Lemma opsem_reduce_seq3: forall hs1 s1 f1 es1 hs2 s2 f2 es2 vs es0,
      const_list vs ->
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (vs ++ es1 ++ es0) hs2 s2 f2 (vs ++ es2 ++ es0).
  Proof.
  Admitted.




  (* Typing lemmas *)

  (* An easier one to get started *)


  (* In properties.v, there's a proof of another verison of this lemma with the goal being the non-constructive exists. However, that proof relies on inverting the typing rule, which cannot be used here due to the goal being a sigma type (try coping the proof and see where it goes wrong; the tactic auto_prove_bet has to be copied here as well for that to be observed).
     Find a way to prove this lemma with goal being the sigma-typed exists; likely it should be done by an induction on es1 or a destruct of e (or both). This might be quite difficult.
 *)
  Lemma composition_typing_single_sig: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    { ts & { t1s' & { t2s' & { t3s | t1s = ts ++ t1s' /\
                                       t2s = ts ++ t2s' /\
                                       be_typing C es1 (Tf t1s' t3s) /\
                                       be_typing C [::e] (Tf t3s t2s') }}}}.
  Proof.
  Admitted.

  (* Another composition typing lemma, with the second component being a general list instead of just a singleton. *)
  Lemma composition_typing_sig: forall C es1 es2 t1s t2s,
      be_typing C (es1 ++ es2) (Tf t1s t2s) ->
      { ts & { t1s' & { t2s' & { t3s | t1s = ts ++ t1s' /\
                                         t2s = ts ++ t2s' /\
                                         be_typing C es1 (Tf t1s' t3s) /\
                                         be_typing C es2 (Tf t3s t2s') }}}}.
  Proof.
  Admitted.




  (* Additional opsem practice *)
  (* Here is a simple program that involves loops. Observe the code below. *)
  Definition i32_of_Z (z: Z) := VAL_int32 (Wasm_int.int_of_Z i32m z).

  Definition loop_body : seq basic_instruction :=
    [ :: BI_get_local 0; BI_testop T_i32 TO_eqz; BI_br_if 1;
      BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add); BI_set_local 1;
      BI_get_local 0; BI_const (i32_of_Z 1); BI_binop T_i32 (Binop_i BOI_sub); BI_set_local 0
    ].

  Definition code : seq administrative_instruction :=
    [:: AI_basic (BI_block (Tf [:: T_i32] [:: T_i32]) [:: BI_loop (Tf [:: T_i32] [:: T_i32]) loop_body ]);
     AI_basic (BI_get_local 1)].

  Definition result_place_holder : seq administrative_instruction.
  Admitted.

  (* Try to work out what it does under the given premises, and fill in the above definition that specifies the execution result. Proving the reduction might be actually very tedious. *)
    Lemma opsem_reduce_loop: forall hs s f (z:Z),
      (z >= 0)%Z ->
      f.(f_locs) = [:: i32_of_Z z; i32_of_Z 0] ->
      exists f', reduce_trans (hs, s, f, code) (hs, s, f', result_place_holder).
  Proof.
  Admitted.


End intro.


