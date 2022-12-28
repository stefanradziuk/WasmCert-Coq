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
    move => hs1 s1 f1 es1 hs2 s2 f2 es2 es0 H.
    assert (LF: forall es, lfilledInd 0 (LH_base [::] es0) es (es ++ es0)).
    (* How does `by` make this different from `apply LfilledBase.`? Just extra automation?
       Also, should be using intros or move?
    *)
    { intros. by apply LfilledBase. }
    (* Not sure how this works precisely but it gives me the subgoals I wanted.
       Found this used for applying r_label elsewhere in the code.
       Need to read up on automation.
       How is eapply different to apply? They seem to produce the same results here. *)
    eapply r_label; eauto; try apply/lfilledP.
    - apply LF.
    - apply LF.
  Qed.

  (* Now note that given Wasm's representation of value stack squashed into the
      * instruction list, adding more constants to the bottom of the value
      * stack should not matter as well. *)
  Lemma opsem_reduce_seq2: forall hs1 s1 f1 es1 hs2 s2 f2 es2 vs,
      const_list vs ->
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (vs ++ es1) hs2 s2 f2 (vs ++ es2).
  Proof.
    move => hs1 s1 f1 es1 hs2 s2 f2 es2 vs Hvs Hes1es2.
    assert (LF: forall es, lfilledInd 0 (LH_base vs [::]) es (vs ++ es ++ [::])).
    { intros. by apply LfilledBase. }
    eapply r_label; eauto; try apply/lfilledP.
    - rewrite <- cats0; rewrite <- catA. apply LF.
    - rewrite <- cats0; rewrite <- catA. apply LF.
  Qed.

  (* This lemma can of course be derived from the two above. However, its proof itself is
     even simpler. *)
  Lemma opsem_reduce_seq3: forall hs1 s1 f1 es1 hs2 s2 f2 es2 vs es0,
      const_list vs ->
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (vs ++ es1 ++ es0) hs2 s2 f2 (vs ++ es2 ++ es0).
  Proof.
    move => hs1 s1 f1 es1 hs2 s2 f2 es2 vs es0 Hconst H.
    assert (LF: forall es, lfilledInd 0 (LH_base vs es0) es (vs ++ es ++ es0)).
    { intros. by apply LfilledBase. }
    eapply r_label; eauto; try apply/lfilledP.
    - apply LF.
    - apply LF.
  Qed.


  (* Typing lemmas *)

  (* An easier one to get started *)


  Lemma sig_test: {x | x mod 2 = 0}.
  Proof. exists 4. reflexivity. Qed.

  Lemma sigT_test: {x & x mod 2 = 0}.
  Proof. exists 4. reflexivity. Qed.

  Lemma sig_sigT_test1: {x & {y | x mod y = 0}}.
  Proof. exists 4. exists 2. reflexivity. Qed.

  Lemma sig_sigT_test2: {x & {y & x mod y = 0}}.
  Proof. exists 4. exists 2. reflexivity. Qed.

  Lemma sig_sigT_test_H: 0 = 0 -> {x & {y | x mod y = 0}}.
  Proof. intro H. exists 4. exists 2. reflexivity. Qed.

  (* In properties.v, there's a proof of another verison of this lemma with the goal being the non-constructive exists. However, that proof relies on inverting the typing rule, which cannot be used here due to the goal being a sigma type (try coping the proof and see where it goes wrong; the tactic auto_prove_bet has to be copied here as well for that to be observed).
     Find a way to prove this lemma with goal being the sigma-typed exists; likely it should be done by an induction on es1 or a destruct of e (or both). This might be quite difficult.
 *)

  (* (be_typing C es t) ≡ (C ⊢ es : t) *)
  (*
  | bet_empty : forall C,
    be_typing C [::] (Tf [::] [::])
  | bet_composition : forall C es e t1s t2s t3s,
    be_typing C es (Tf t1s t2s) ->
    be_typing C [::e] (Tf t2s t3s) ->
    be_typing C (app es [::e]) (Tf t1s t3s)

     looking at bet_empty and bet_composition, wouldn't ts always be [::]?
   *)

  Type last_ind.

  Lemma composition_typing_single_sig: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    { ts & { t1s' & { t2s' & { t3s | t1s = ts ++ t1s' /\
                                       t2s = ts ++ t2s' /\
                                       be_typing C es1 (Tf t1s' t3s) /\
                                       be_typing C [::e] (Tf t3s t2s') }}}}.
  Proof.
    (* maybe induction on es1 and then destruct on the elem added to es1? *)
    (* induction from the right? *)
    (*
    move => C es1 e t1s t2s HType.
    generalize es1.
    apply last_ind.
    - (* base case *)
      (* This worked but I still have
         HType : be_typing C (es1 ++ [:: e]) (Tf t1s t2s)
         and I'd like it to be
         HType : be_typing C ([::] ++ [:: e]) (Tf t1s t2s)
      *)
    generalize HType. (* this makes last_ind fail later? *)
    -

    destruct e. (* ? *)
     *)

    move => C es1 e.
    induction es1 as [|e' es1' IHes].
      (* i'd like to apply bet_empty and weakening to type es1=[::] and HType
         to type [::e] hence:
           t1s' = t3s
         to match HType:
           t3s  = t1s
           t2s' = t2s (and hence ts = [::])
      *)
    - move => t1s t2s HType. exists [::], t1s, t2s, t1s.
      simpl in HType.
      split. { reflexivity. } split. { reflexivity. } split.
      * apply bet_weakening_empty_both. apply bet_empty.
      * apply HType.
    - move => t1s t2s HType.
      (* XXX don't think I'll be able to get the antecedent from HType
         I can't really type (es1' ++ [:: e]) without inverting HType?
         unless I do this fully case by case?

         HType : be_typing C ((e' :: es1') ++ [:: e]) (Tf t1s t2s)
         IHes : forall t1s t2s : result_type,
           be_typing C (es1' ++ [:: e]) (Tf t1s t2s) -> ...

       *)
  Admitted.

  (* Another composition typing lemma, with the second component being a general list instead of just a singleton. *)
  (* XXX induction on es2 and use composition_typing_single_sig? *)
  Lemma composition_typing_sig: forall C es1 es2 t1s t2s,
      be_typing C (es1 ++ es2) (Tf t1s t2s) ->
      { ts & { t1s' & { t2s' & { t3s | t1s = ts ++ t1s' /\
                                         t2s = ts ++ t2s' /\
                                         be_typing C es1 (Tf t1s' t3s) /\
                                         be_typing C es2 (Tf t3s t2s') }}}}.
  Proof.
    intros C es1 es2 t1s t2s H.
    induction es2 using last_ind.
    (* looks like last_ind is not right here?
       it enforces the same types for es2 and x:
       H : be_typing C (es1 ++ rcons es2 x) (Tf t1s t2s)
       IHes2 : be_typing C (es1 ++ es2) (Tf t1s t2s) ->
     *)

    - rewrite cats0 in H.
      exists [::], t1s, t2s, t2s.
      split. reflexivity. split. reflexivity. split.
      * apply H.
      * apply bet_weakening_empty_both. apply bet_empty.
    - assert (IHes2_ante : be_typing C (es1 ++ es2) (Tf t1s t2s)).
      { (* TODO destruct IHes2 instead of asserT? *)
        rewrite <- cats1 in H. rewrite catA in H.
        remember (es1 ++ es2) as es12.
        apply composition_typing_single_sig in H.
        (* this is a bit ugly *)
        destruct H as [ts_H [t1s'_H [t2s'_H [t3s_H [
          Heq_t1s [Heq_t2s [HType_es12 HType_x]]
        ]]]]].
        (* can get anything useful from HType_x here? mayhbe by inversion? *)
        apply (bet_weakening ts_H) in HType_es12.

        (* XXX the types in HType_es12 don't quite match the goal (yet?) *)
        (* intros later? *)
        give_up.
      }
      apply IHes2 in IHes2_ante as [ts_IH [t1s'_IH [t2s'_IH [t3s_IH [
        IHeq_t1s [IHeq_t2s [IHType_es1 IHType_es2]]]]]]
      ].

      (* is this even necessary?
         can we apply composition_typing_single_sig instead? *)
      exists ts_IH, t1s'_IH, t2s'_IH, t3s_IH.
      split. auto. split. auto. split.
      * apply IHType_es1.
      * rewrite <- cats1. apply (bet_composition IHType_es2).
        (* TODO need to type x somehow. destruct x? (28 cases) *)
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


