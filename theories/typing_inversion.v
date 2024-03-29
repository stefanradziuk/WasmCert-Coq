(** Proof of preservation **)
(* (C) Rao Xiaojia, M. Bodin - see LICENSE.txt *)

From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
From Wasm Require Export operations datatypes_properties typing opsem properties.

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
Let inst_typing : store_record -> instance -> t_context -> bool := @inst_typing _.
(*Let reduce_simple : seq administrative_instruction -> seq administrative_instruction -> Prop :=
  @reduce_simple _.
Let const_list : seq administrative_instruction -> bool := @const_list _.
Let lholed := lholed host_function.
Let lfilled : depth -> lholed -> seq administrative_instruction -> seq administrative_instruction -> bool :=
  @lfilled _.
Let es_is_basic : seq administrative_instruction -> Prop := @es_is_basic _.*)

Let host := host host_function.

Variable host_instance : host.

Let host_state := host_state host_instance.

Let reduce : host_state -> store_record -> frame -> seq administrative_instruction ->
             host_state -> store_record -> frame -> seq administrative_instruction -> Prop
  := @reduce _ _.

Let s_globals : store_record -> seq global := @s_globals _.
Let s_mems : store_record -> seq memory := @s_mems _.
Let functions_agree : seq function_closure -> nat -> function_type -> bool := @functions_agree _.
Let cl_type : function_closure -> function_type := @cl_type _.
Let store_extension: store_record -> store_record -> Prop := @store_extension _.

Lemma upd_label_overwrite: forall C l1 l2,
    upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

(*
  These proofs are largely similar.
  A sensible thing to do is to make tactics for all of them.
  However, some of the proofs depend on the previous ones...
*)

Lemma BI_const_typing: forall C econst t1s t2s,
    be_typing C [::BI_const econst] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst].
Proof.
  move => C econst t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma BI_const2_typing: forall C econst1 econst2 t1s t2s,
    be_typing C [::BI_const econst1; BI_const econst2] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst1; typeof econst2].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list2 in H1; inversion H1; subst.
    apply BI_const_typing in HType1; subst.
    apply BI_const_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma BI_const3_typing: forall C econst1 econst2 econst3 t1s t2s,
    be_typing C [::BI_const econst1; BI_const econst2; BI_const econst3] (Tf t1s t2s) ->
    t2s = t1s ++ [::typeof econst1; typeof econst2; typeof econst3].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list3 in H1; inversion H1; subst.
    apply BI_const2_typing in HType1; subst.
    apply BI_const_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma Const_list_typing_empty: forall C vs,
    be_typing C (to_b_list (v_to_e_list vs)) (Tf [::] (vs_to_vts vs)).
Proof.
  move => C vs.
  generalize dependent vs.
  induction vs => //=.
  - by apply bet_empty.
  - rewrite - cat1s.
    replace (typeof a :: vs_to_vts vs) with ([::typeof a] ++ vs_to_vts vs) => //.
    eapply bet_composition'; eauto; first by apply bet_const.
    by apply bet_weakening_empty_1.
Qed.

Lemma Unop_typing: forall C t op t1s t2s,
    be_typing C [::BI_unop t op] (Tf t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - split => //=. by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    split => //=.
    destruct H0 as [ts' H0].
    exists (ts ++ ts').
    rewrite - catA.
    by rewrite H0.
Qed.

Lemma Binop_typing: forall C t op t1s t2s,
    be_typing C [::BI_binop t op] (Tf t1s t2s) ->
    t1s = t2s ++ [::t] /\ exists ts, t2s = ts ++ [::t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - split => //=. by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    split => //=.
    + destruct H0 as [ts' H0].
      by rewrite - catA.
    + destruct H0 as [ts' H0].
      exists (ts ++ ts').
      subst.
      by rewrite - catA.
Qed.

Lemma Testop_typing: forall C t op t1s t2s,
    be_typing C [::BI_testop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

(* XXX right place for this? *)
Lemma Testop_typing_is_int_t: forall C t op t1s t2s,
    be_typing C [::BI_testop t op] (Tf t1s t2s) ->
    is_int_t t.
Proof.
  move => C t op t1s t2s HType.
  destruct t => //.
  - gen_ind_subst HType => //.
    * eapply IHHType2 => //.
      by apply extract_list1 in Econs as [??]; subst e.
    * eapply IHHType => //.
  - gen_ind_subst HType => //.
    * eapply IHHType2 => //.
      by apply extract_list1 in Econs as [??]; subst e.
    * eapply IHHType => //.
Qed.

Lemma Relop_typing: forall C t op t1s t2s,
    be_typing C [::BI_relop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t; t] /\ t2s = ts ++ [::T_i32].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Cvtop_typing: forall C t1 t2 op sx t1s t2s,
    be_typing C [::BI_cvtop t2 op t1 sx] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t1] /\ t2s = ts ++ [::t2].
Proof.
  move => C t1 t2 op sx t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

(* TODO move this to a different file?
 * interpreter_func.v?
 * or move all typing inversion lemmas out to a common file? *)
Lemma Cvtop_reinterpret_typing: forall C t1 t2 sx t1s t2s,
    be_typing C [::BI_cvtop t2 CVO_reinterpret t1 sx] (Tf t1s t2s) ->
    sx = None.
Proof.
  move => C t1 t2 sx t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in H1; destruct H1; subst.
    by eapply IHHType2.
  - by edestruct IHHType.
Qed.

Lemma Nop_typing: forall C t1s t2s,
    be_typing C [::BI_nop] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - f_equal. by eapply IHHType.
Qed.

Lemma Drop_typing: forall C t1s t2s,
    be_typing C [::BI_drop] (Tf t1s t2s) ->
    exists t, t1s = t2s ++ [::t].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //=.
  - by eauto.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    exists x. repeat rewrite -catA. by f_equal.
Qed.

Lemma Select_typing: forall C t1s t2s,
    be_typing C [::BI_select] (Tf t1s t2s) ->
    exists ts t, t1s = ts ++ [::t; t; T_i32] /\ t2s = ts ++ [::t].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - by exists [::], t.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    edestruct H as [x2 [H3 H4]]; subst.
    exists (ts ++ x), x2. by split; repeat rewrite -catA.
Qed.

Lemma If_typing: forall C t1s t2s e1s e2s ts ts',
    be_typing C [::BI_if (Tf t1s t2s) e1s e2s] (Tf ts ts') ->
    exists ts0, ts = ts0 ++ t1s ++ [::T_i32] /\ ts' = ts0 ++ t2s /\
                be_typing (upd_label C ([:: t2s] ++ tc_label C)) e1s (Tf t1s t2s) /\
                be_typing (upd_label C ([:: t2s] ++ tc_label C)) e2s (Tf t1s t2s).
Proof.
  move => C t1s t2s e1s e2s ts ts' HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [H1 [H2 [H3 H4]]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    repeat split => //=.
Qed.

Lemma Br_if_typing: forall C ts1 ts2 i,
    be_typing C [::BI_br_if i] (Tf ts1 ts2) ->
    exists ts ts', ts2 = ts ++ ts' /\ ts1 = ts2 ++ [::T_i32] /\ i < length (tc_label C) /\ plop2 C i ts'.
Proof.
  move => C ts1 ts2 i HType.
  gen_ind_subst HType.
  - unfold plop2 in H0.
    by exists [::], ts2.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite -catA. f_equal => //=.
    edestruct IHHType => //=.
    destruct H as [ts' [H1 [H2 [H3 H4]]]].
    exists (ts ++ x), ts'. subst.
    split.
    + repeat rewrite -catA. by f_equal.
    + split => //=.
Qed.

Lemma Br_table_typing: forall C ts1 ts2 ids i0,
    be_typing C [::BI_br_table ids i0] (Tf ts1 ts2) ->
    exists ts1' ts, ts1 = ts1' ++ ts ++ [::T_i32] /\
                         all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (ids ++ [::i0]).
Proof.
  move => C ts1 ts2 ids i0 HType.
  gen_ind_subst HType.
  - by exists t1s, ts.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]].
    exists (ts ++ x), ts'. subst.
    split => //=.
    + repeat rewrite -catA. by f_equal => //=.
Qed.

Lemma Tee_local_typing: forall C i ts1 ts2,
    be_typing C [::BI_tee_local i] (Tf ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [::t] /\ i < length (tc_local C) /\
                 List.nth_error (tc_local C) i = Some t.
Proof.
  move => C i ts1 ts2 HType.
  gen_ind_subst HType.
  - by exists [::], t.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 [H3 H4]]]]. subst.
    exists (ts ++ x), t. subst.
    repeat (try split => //=).
    by rewrite -catA.
Qed.

Lemma Const_list_typing: forall C vs t1s t2s,
    be_typing C (to_b_list (v_to_e_list vs)) (Tf t1s t2s) ->
    t2s = t1s ++ (map typeof vs).
Proof.
  move => C vs.
  induction vs => //=; move => t1s t2s HType.
  - apply empty_typing in HType. subst. by rewrite cats0.
  - rewrite -cat1s in HType.
    rewrite -cat1s.
    apply composition_typing in HType.
    destruct HType as [ts [ts1' [ts2' [ts3 [H1 [H2 [H3 H4]]]]]]].
    subst.
    apply BI_const_typing in H3.
    apply IHvs in H4.
    subst.
    by repeat rewrite catA.
Qed.
(*
  Unlike the above proofs which have a linear dependent structure therefore hard
    to factorize into a tactic, the following proofs are independent of each other
    and should therefore be easily refactorable.
*)

Ltac et_dependent_ind H :=
  let Ht := type of H in
  lazymatch Ht with
  | e_typing ?s ?C ?es (Tf ?t1s ?t2s) =>
    let s2 := fresh "s2" in
    let C2 := fresh "C2" in
    let es2 := fresh "es2" in
    let tf2 := fresh "tf2" in
    remember s as s2 eqn:Hrems;
    remember C as C2 eqn:HremC;
    remember es as es2 eqn:Hremes;
    remember (Tf t1s t2s) as tf2 eqn:Hremtf;
    generalize dependent Hrems;
    generalize dependent HremC;
    generalize dependent Hremtf;
    generalize dependent s; generalize dependent C;
    generalize dependent t1s; generalize dependent t2s;
    induction H
  | e_typing ?s ?C ?es ?tf =>
    let s2 := fresh "s2" in
    let C2 := fresh "C2" in
    let es2 := fresh "es2" in
    remember s as s2 eqn:Hrems;
    remember C as C2 eqn:HremC;
    remember es as es2 eqn:Hremes;
    generalize dependent Hrems;
    generalize dependent HremC;
    generalize dependent s; generalize dependent C;
    induction H
  | _ => fail "hypothesis not an e_typing relation"
  end; intros; subst.

(* We need this version for dealing with the version of predicate with host. *)
Ltac basic_inversion' :=
   repeat lazymatch goal with
         | H: True |- _ =>
           clear H
         | H: es_is_basic (_ ++ _) |- _ =>
           let Ha := fresh H in
           let Hb := fresh H in
           apply basic_concat in H; destruct H as [Ha Hb]
         | H: es_is_basic [::] |- _ =>
           clear H
         | H: es_is_basic [::_] |- _ =>
           let H1 := fresh H in
           let H2 := fresh H in
           try by (unfold es_is_basic in H; destruct H as [H1 H2]; inversion H1)
         | H: e_is_basic _ |- _ =>
           inversion H; try by []
         end.

(* TODO use this in itp completeness lemmas? *)
Ltac invert_be_typing:=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    extract_listn
  | H: be_typing _ [::] _ |- _ =>
    apply empty_typing in H; subst
  | H: be_typing _ [:: BI_const _] _ |- _ =>
    apply BI_const_typing in H; subst
  | H: be_typing _ [:: BI_const _; BI_const _] _ |- _ =>
    apply BI_const2_typing in H; subst
  | H: be_typing _ [:: BI_const _; BI_const _; BI_const _] _ |- _ =>
    apply BI_const3_typing in H; subst
  | H: be_typing _ [::BI_unop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Unop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::BI_binop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Binop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::BI_testop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Testop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_relop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Relop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_cvtop _ _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Cvtop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_drop] _ |- _ =>
    apply Drop_typing in H; destruct H; subst
  | H: be_typing _ [::BI_select] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Select_typing in H; destruct H as [ts [t [H1 H2]]]; subst
  | H: be_typing _ [::BI_if _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply If_typing in H; destruct H as [ts [H1 [H2 [H3 H4]]]]; subst
  | H: be_typing _ [::BI_br_if _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Br_if_typing in H; destruct H as [ts [ts' [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ [::BI_br_table _ _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Br_table_typing in H; destruct H as [ts [ts' [H1 H2]]]; subst
  | H: be_typing _ [::BI_tee_local _] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Tee_local_typing in H; destruct H as [ts [t [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ (_ ++ _) _ |- _ =>
    let ts1 := fresh "ts1" in
    let ts2 := fresh "ts2" in
    let ts3 := fresh "ts3" in
    let ts4 := fresh "ts4" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply composition_typing in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]]
  | H: be_typing _ [::_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  end.

Lemma Invoke_func_typing: forall s C a t1s t2s,
    e_typing s C [::AI_invoke a] (Tf t1s t2s) ->
    exists cl, List.nth_error s.(s_funcs) a = Some cl.
Proof.
  move => s C a t1s t2s HType.
  et_dependent_ind HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Hremes. destruct Hremes. subst.
    by eapply IHHType2 => //=.
  - by eapply IHHType => //=.
  - inversion Hremes; subst; by exists cl.
Qed.

Lemma Invoke_func_native_typing: forall s i C a cl tn tm ts es t1s t2s,
    e_typing s C [::AI_invoke a] (Tf t1s t2s) ->
    List.nth_error s.(s_funcs) a = Some cl ->
    cl = FC_func_native i (Tf tn tm) ts es ->
    exists ts' C', t1s = ts' ++ tn /\ t2s = ts' ++ tm /\
                inst_typing s i C' /\
               be_typing (upd_local_label_return C' (tc_local C' ++ tn ++ ts) ([::tm] ++ tc_label C') (Some tm)) es (Tf [::] tm).
Proof.
  move => s i C a cl tn tm ts es t1s t2s HType HNth Hcl.
  et_dependent_ind HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - inversion Hremtf; subst.
    edestruct IHHType => //=.
    destruct H as [C' [H1 [H2 [H3 H4]]]]. subst.
    exists (ts0 ++ x), C'.
    by repeat split => //; rewrite catA.
  - inversion Hremes; subst.
    rewrite H in HNth.
    inversion HNth; subst; clear HNth.
    inversion H0; subst.
    inversion H9; subst.
    by exists [::], C.
Qed.

Lemma Invoke_func_host_typing: forall s C a cl h tn tm t1s t2s,
    e_typing s C [::AI_invoke a] (Tf t1s t2s) ->
    List.nth_error s.(s_funcs) a = Some cl ->
    cl = FC_func_host (Tf tn tm) h ->
    exists ts, t1s = ts ++ tn /\ t2s = ts ++ tm.
Proof.
  move => s C a cl h tn tm t1s t2s HType HNth Hcl.
  et_dependent_ind HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - inversion Hremtf; subst.
    edestruct IHHType => //=.
    exists (ts ++ x). destruct H. subst.
    by split; repeat rewrite catA.
  - inversion Hremes; subst.
    rewrite H in HNth.
    inversion HNth; subst; clear HNth.
    inversion H0; subst.
    by exists [::].
Qed.

Lemma Get_local_typing: forall C i t1s t2s,
    be_typing C [::BI_get_local i] (Tf t1s t2s) ->
    exists t, List.nth_error (tc_local C) i = Some t /\
    t2s = t1s ++ [::t] /\
    i < length (tc_local C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Set_local_typing: forall C i t1s t2s,
    be_typing C [::BI_set_local i] (Tf t1s t2s) ->
    exists t, List.nth_error (tc_local C) i = Some t /\
    t1s = t2s ++ [::t] /\
    i < length (tc_local C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Get_global_typing: forall C i t1s t2s,
    be_typing C [::BI_get_global i] (Tf t1s t2s) ->
    exists t, option_map tg_t (List.nth_error (tc_global C) i) = Some t /\
    t2s = t1s ++ [::t] /\
    i < length (tc_global C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Set_global_typing: forall C i t1s t2s,
    be_typing C [::BI_set_global i] (Tf t1s t2s) ->
    exists g t, List.nth_error (tc_global C) i = Some g /\
    tg_t g = t /\
    is_mut g /\
    t1s = t2s ++ [::t] /\
    i < length (tc_global C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists g, (tg_t g).
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 [H3 [H4 H5]]]]]. subst.
    exists x, (tg_t x).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Load_typing: forall C t a off tp_sx t1s t2s,
    be_typing C [::BI_load t tp_sx a off] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_i32] /\ t2s = ts ++ [::t] /\
                    tc_memory C <> nil /\
                    load_store_t_bounds a (option_projl tp_sx) t.
Proof.
  move => C t a off tp_sx t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 [H3 H4]]]. subst.
    exists (ts ++ x).
    by repeat rewrite -catA.
Qed.

Lemma Store_typing: forall C t a off tp t1s t2s,
    be_typing C [::BI_store t tp a off] (Tf t1s t2s) ->
    t1s = t2s ++ [::T_i32; t] /\
    tc_memory C <> nil /\
    load_store_t_bounds a tp t.
Proof.
  move => C t a off tp t1s t2s HType.
  dependent induction HType; subst => //=.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Current_memory_typing: forall C t1s t2s,
    be_typing C [::BI_current_memory] (Tf t1s t2s) ->
    tc_memory C <> nil /\ t2s = t1s ++ [::T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Grow_memory_typing: forall C t1s t2s,
    be_typing C [::BI_grow_memory] (Tf t1s t2s) ->
    exists ts, tc_memory C <> nil /\ t2s = t1s /\ t1s = ts ++ [::T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    by repeat rewrite -catA.
Qed.

Lemma store_typed_cl_typed: forall s n f,
    List.nth_error (s_funcs s) n = Some f ->
    store_typing s ->
    cl_typing s f (cl_type f).
Proof.
  move => s n f HN HST.
  unfold store_typing in HST.
  destruct s => //=.
  remove_bools_options.
  simpl in HN.
  destruct HST.
  (* arrow actually required to avoid ssreflect hijacking the rewrite tactic! *)
  rewrite -> List.Forall_forall in H.
  apply List.nth_error_In in HN.
  apply H in HN. unfold cl_type_check_single in HN. destruct HN.
  by inversion H1; subst.
Qed.

(* inst_typing inversion *)
Lemma inst_t_context_local_empty: forall s i C,
    inst_typing s i C ->
    tc_local C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  by destruct tc_local.
Qed.

Lemma inst_t_context_label_empty: forall s i C,
    inst_typing s i C ->
    tc_label C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  by destruct tc_local; destruct tc_label.
Qed.

Lemma global_type_reference: forall s i j C v t,
    inst_typing s i C ->
    sglob_val s i j = Some v ->
    option_map tg_t (List.nth_error (tc_global C) j) = Some t ->
    typeof v = t.
Proof.
  move => s i j C v t HInstType Hvref Htref.
  unfold sglob_val in Hvref.
  unfold sglob in Hvref.
  unfold sglob_ind in Hvref.
  destruct (List.nth_error i.(inst_globs) j) eqn:Hi => //=.
  remove_bools_options.
  unfold option_bind in Hoption0.
  remove_bools_options.
  unfold inst_typing in HInstType.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  move/andP in HInstType. destruct HInstType.
  remove_bools_options.
  eapply all2_projection in H2; eauto.
  unfold globals_agree in H2. move/andP in H2. destruct H2.
  remove_bools_options.
  simpl in Hi. simpl in Hoption.
  unfold global_agree in H6.
  by remove_bools_options.
Qed.

Lemma func_context_store: forall s i C j x,
    inst_typing s i C ->
    j < length (tc_func_t C) ->
    List.nth_error (tc_func_t C) j = Some x ->
    exists a, List.nth_error i.(inst_funcs) j = Some a.
Proof.
  (* TODO: inst_funcs is a fragile name *)
  move => s i C j x HIT HLength HN.
  unfold sfunc. unfold operations.sfunc. unfold option_bind.
  unfold sfunc_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  remember H3 as H4. clear HeqH4.
  apply all2_size in H3.
  repeat rewrite -length_is_size in H3.
  simpl in HLength.
  rewrite -H3 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error inst_funcs j) eqn:HN1 => //=.
  by eexists.
Qed.

Lemma glob_context_store: forall s i C j g,
    inst_typing s i C ->
    j < length (tc_global C) ->
    List.nth_error (tc_global C) j = Some g ->
    sglob s i j <> None.
Proof.
  (* TODO: inst_globs is a fragile name *)
  move => s i C j g HIT HLength HN.
  unfold sglob. unfold operations.sglob. unfold option_bind.
  unfold sglob_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  remember H2 as H4. clear HeqH4.
  apply all2_size in H2.
  repeat rewrite -length_is_size in H2.
  simpl in HLength.
  rewrite -H2 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error inst_globs j) eqn:HN1 => //=.
  apply List.nth_error_Some.
  unfold globals_agree in H4.
  eapply all2_projection in H4; eauto.
  remove_bools_options.
  by move/ltP in H4.
Qed.

Lemma mem_context_store: forall s i C,
    inst_typing s i C ->
    tc_memory C <> [::] ->
    exists n, smem_ind s i = Some n /\
              List.nth_error (s_mems s) n <> None.
Proof.
  (* TODO: inst_memory is a fragile name *)
  move => s i C HIT HMemory.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  simpl in HMemory. unfold smem_ind. simpl.
  remember H0 as H4. clear HeqH4.
  apply all2_size in H0.
  destruct inst_memory => //=; first by destruct tc_memory.
  exists m. split => //.
  destruct tc_memory => //.
  simpl in H4.
  unfold memi_agree in H4.
  unfold s_mems.
  by remove_bools_options.
Qed.

Lemma store_typing_stabaddr: forall s f C c a,
  stab_addr s f c = Some a ->
  inst_typing s f.(f_inst) C ->
  store_typing s ->
  exists cl, List.nth_error s.(s_funcs) a = Some cl.
Proof.
  move => s f C c a HStab HIT HST.
  unfold inst_typing, typing.inst_typing in HIT.
  unfold store_typing, tab_agree, tabcl_agree in HST.
  unfold stab_addr in HStab.
  destruct s => //=. destruct f => //=. destruct f_inst. destruct f_inst. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  remove_bools_options.
  simpl in *. destruct inst_tab0 => //=.
  unfold stab_index in HStab. unfold option_bind in HStab.
  remove_bools_options.
  subst. simpl in *.
  destruct tc_table => //=.
  remove_bools_options.
  destruct HST.
  destruct H5.
  rewrite -> List.Forall_forall in H5.
  assert (HIN1: List.In t0 s_tables).
  { by apply List.nth_error_In in Hoption0. }
  apply H5 in HIN1. destruct HIN1 as [HIN1 _].
  rewrite -> List.Forall_forall in HIN1.
  assert (HIN2: List.In (Some a) (table_data t0)).
  { by apply List.nth_error_In in Hoption. }
  apply HIN1 in HIN2.
  move/ltP in HIN2.
  apply List.nth_error_Some in HIN2.
  destruct (List.nth_error s_funcs a) eqn:HNth => //.
  by eexists.
Qed.

Ltac auto_basic :=
  repeat lazymatch goal with
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- es_is_basic [::AI_basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::AI_basic _; AI_basic _] =>
    simpl; repeat split
  | |- operations.es_is_basic [::AI_basic _] =>
    simpl; repeat split
  | |- operations.e_is_basic (AI_basic ?e) =>
    by unfold e_is_basic; exists e
end.

Lemma Block_typing: forall C t1s t2s es tn tm,
    be_typing C [::BI_block (Tf t1s t2s) es] (Tf tn tm) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
               be_typing (upd_label C ([::t2s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C t1s t2s es tn tm HType.
  dependent induction HType => //=.
  - by exists [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma Loop_typing: forall C t1s t2s es tn tm,
    be_typing C [::BI_loop (Tf t1s t2s) es] (Tf tn tm) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
               be_typing (upd_label C ([::t1s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C t1s t2s es tn tm HType.
  dependent induction HType => //=.
  - by exists [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma Break_typing: forall n C t1s t2s,
    be_typing C [::BI_br n] (Tf t1s t2s) ->
    exists ts ts0, n < size (tc_label C) /\
               plop2 C n ts /\
               t1s = ts0 ++ ts.
Proof.
  move => n C t1s t2s HType.
  dependent induction HType => //=.
  - by exists ts, t1s0.
  - invert_be_typing.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts0 [H1 [H2 H3]]]. subst.
    exists x, (ts ++ ts0).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Label_typing: forall s C n es0 es ts1 ts2,
    e_typing s C [::AI_label n es0 es] (Tf ts1 ts2) ->
    exists ts ts2', ts2 = ts1 ++ ts2' /\
                    e_typing s C es0 (Tf ts ts2') /\
                    e_typing s (upd_label C ([::ts] ++ (tc_label C))) es (Tf [::] ts2') /\
                    length ts = n.
Proof.
  move => s C n es0 es ts1 ts2 HType.
(*  (* Without the powerful generalize_dependent tactic, we need to manually remember
     the dependent terms. However, it's very easy to mess up the induction hypothesis
     if variables are not correctly generalized.
     Reading source: https://stackoverflow.com/questions/58349365/coq-how-to-correctly-remember-dependent-values-without-messing-up-the-inductio 
     ( the missing letter n at the end of link is not a typo )
   *)
  remember ([::Label n es0 es]) as les.
  remember (Tf ts1 ts2) as tf.
  generalize dependent Heqtf. generalize dependent ts1. generalize dependent ts2.*)
  et_dependent_ind HType => //.
(*  induction HType => //. *)
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Hremes in H0. by basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType => //.
    inversion Hremtf; subst.
    destruct H as [ts2' [H1 [H2 [H3 H4]]]]. subst.
    by exists x, ts2'; try rewrite catA.     
  - (* ety_label *)
    inversion Hremes. inversion Hremtf. subst.
    by exists ts, ts2.
Qed.

(*
  Looking at what we want to prove in the Lfilled_break case, it might be tempting to
    prove the following:

Lemma Lfilled_break_typing: forall n lh vs LI ts s C t2s,
    e_typing s (upd_label C ([::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::AI_basic (Br n)]) LI ->
    e_typing s C vs (Tf [::] ts).

  The lemma itself is definitely correct, and an apparent approach is to do induction
    on n (or induction on the lfilled hypothesis).

  However, this will *NOT* work: the culprit is that there is no inductive relationship
    that changes the instruction (Br n+1) into (Br n), and we will get a useless
    induction hypothesis that can never be applied.

  We need to somehow avoid getting the parameter of Br into induction. By the lfilled
    hypothesis, we know LI is a nested Label which, at the innermost level, has (Br n)
    as its first non-constant instruction, and vs at the top of the value stack.

  Recall that (Br n) looks at the nth entry in the label of the typing context and
    needs to consume that type. Since we can only induct on the depth of lfilled
    (but not the n in the instruction), they have to be two separate numbers, say
    n and m. Now if n is 0, the instruction will basically look at the mth entry;
    what if n is not 0? In that case if we trace the expansion of LI and simulate
    how the typing is evaluated, we realize that there will be n entries prepended
    to the label of the typing context, after which we'll then find the mth element
    of it due to the (Br m).

  So a more sensible lemma to prove is the following, which the original lemma we
    wanted is a special case of:
*)

Lemma Lfilled_break_typing: forall n m k lh vs LI ts s C t2s tss,
    e_typing s (upd_label C (tss ++ [::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::AI_basic (BI_br m)]) LI ->
    length tss = k ->
    n + k = m ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n m k lh vs LI ts s C ts2 tss HType HConst HLength HLF HTSSLength HSum.
  apply const_es_exists in HConst. destruct HConst. subst.
  move/lfilledP in HLF.
  generalize dependent ts.
  generalize dependent ts2.
  generalize dependent LI.
  generalize dependent tss.
  generalize dependent lh.
  induction n.
  - move => lh tss LI HLF ts2 ts HType HTSSLength.
    rewrite add0n in HLF.
    repeat rewrite catA in HType.
    inversion HLF.
    apply const_es_exists in H. destruct H. subst.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    subst. clear H1.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst.
    apply e_composition_typing in H7.
    destruct H7 as [ts0'' [t1s'' [t2s'' [t3s'' [H9 [H10 [H11 H12]]]]]]].
    subst.
    apply et_to_bet in H12; try auto_basic.
    apply Break_typing in H12.
    destruct H12 as [ts0 [ts1 [H13 [H14 H15]]]]. clear H13.
    unfold plop2 in H14. simpl in H14. move/eqP in H14. inversion H14. subst.
    clear H14.
    apply et_to_bet in H11; last by (apply const_list_is_basic; apply v_to_e_is_const_list).
    apply Const_list_typing in H11.
    repeat rewrite length_is_size in HTSSLength.
    rewrite -catA in H0. rewrite list_nth_prefix in H0. inversion H0. subst. clear H0.
    assert ((ts1 == t1s'') && (ts0 == vs_to_vts x)).
    + apply concat_cancel_last_n => //=. rewrite size_map.
      by rewrite v_to_e_size in HTSSLength.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
      by apply Const_list_typing_empty.
  - move => lh tss LI HLF ts2 ts HType HTSSLength.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6 [H7 [H8 H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6. clear H7.
    apply Label_typing in H9.
    destruct H9 as [ts0'' [t2s'' [H10 [H11 [H12 H13]]]]]. subst.
    simpl in H12.
    rewrite upd_label_overwrite in H12.
    rewrite -cat1s in H12. repeat rewrite catA in H12.
    remember ([::ts0''] ++ tss) as tss'. rewrite -catA in H12.
    replace (n.+1+length tss) with (n + length tss') in H1.
    eapply IHn => //=.
    + by apply H1.
    + by apply H12.
    (* replace *)
    assert (length tss' = length tss + 1).
    { rewrite Heqtss'. rewrite cat1s. simpl. by rewrite addn1. }
    by lias.
Qed.

(*
  And yes, the above observation was obviously the result of some futile attempt
    to prove the unprovable version of the lemma.

Lemma Lfilled_break_typing: forall n lh vs LI ts s C t2s,
    e_typing s (upd_label C ([::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::AI_basic (Br n)]) LI ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n lh vs LI ts s C ts2 HType HConst HLength HLF.
  apply const_es_exists in HConst. destruct HConst. subst.
  move/lfilledP in HLF.
  generalize dependent ts2.
  generalize dependent LI.
  induction n.
  - move => LI HLF ts2 HType.
    repeat rewrite catA in HType.
    inversion HLF.
    apply const_es_exists in H. destruct H. subst.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    subst. clear H1.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst.
    apply e_composition_typing in H7.
    destruct H7 as [ts0'' [t1s'' [t2s'' [t3s'' [H9 [H10 [H11 H12]]]]]]].
    subst.
    apply et_to_bet in H12; last by auto_basic.
    apply Break_typing in H12.
    destruct H12 as [ts0 [ts1 [H13 [H14 H15]]]]. clear H13.
    unfold plop2 in H14. simpl in H14. move/eqP in H14. inversion H14. subst.
    clear H14.
    apply et_to_bet in H11; last by (apply const_list_is_basic; apply v_to_e_is_const_list).
    apply Const_list_typing in H11.
    repeat rewrite length_is_size in HLength.
    assert ((ts1 == t1s'') && (ts0 == vs_to_vts x)).
    + apply concat_cancel_last_n => //=. rewrite size_map.
      by rewrite v_to_e_size in HLength.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
      by apply Const_list_typing_empty.
  - move => LI HLF ts2 HType.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6 [H7 [H8 H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6. clear H7.
    apply Label_typing in H9.
    destruct H9 as [ts0'' [t2s'' [H10 [H11 [H12 H13]]]]]. subst.
    simpl in H12.

 *)

Lemma Local_typing: forall s C n f es t1s t2s,
    e_typing s C [::AI_local n f es] (Tf t1s t2s) ->
    exists ts, t2s = t1s ++ ts /\
               s_typing s (Some ts) f es ts /\
               length ts = n.
Proof.
  move => s C n f es t1s t2s HType.
  remember ([::AI_local n f es]) as les.
  remember (Tf t1s t2s) as tf.
  generalize dependent Heqtf. generalize dependent t1s. generalize dependent t2s.
  induction HType; subst => //.
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Heqles in H0. by basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Heqles. destruct Heqles. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    move => ts2 ts1 HTf.
    inversion HTf. subst.
    edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst. 
    exists x.
    repeat split => //=.
    by rewrite catA.
  - (* ety_local *)
    inversion Heqles. subst.
    move => t2s t1s HTf. inversion HTf. subst.
    by exists t2s.
Qed.

Lemma Return_typing: forall C t1s t2s,
    be_typing C [::BI_return] (Tf t1s t2s) ->
    exists ts ts', t1s = ts' ++ ts /\
                   tc_return C = Some ts.
Proof.
  move => C t1s t2s HType.
  dependent induction HType => //=.
  - by exists ts, t1s0.
  - invert_be_typing.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]]. subst.
    exists x, (ts ++ ts').
    split => //=.
    by rewrite -catA.
Qed.

(*
  Similarly, Local does not involve in induction either. So what we want to prove
    is also slightly different from what we desire. However, this one is easier
    to observe.

  The only thing that got me stuck for a while is to observe that label of the
    typing context plays no role in typing for this case; this is required since
    we'll get an extra label update from inverting the Label instruction.
 *)

Lemma Lfilled_return_typing: forall n lh vs LI ts s C lab t2s,
    e_typing s (upd_label C lab) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::AI_basic BI_return]) LI ->
    Some ts = tc_return C ->
    e_typing s C vs (Tf [::] ts).
Proof.
  induction n; move => lh vs LI ts s C lab t2s HType HConst HLength HLF HReturn; move/lfilledP in HLF; inversion HLF; subst => //=.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H1.
    apply e_composition_typing in H3.
    destruct H3 as [ts1 [t1s1 [t2s1 [t3s1 [H5 [H6 [H7 H8]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. clear H5.
    apply e_composition_typing in H7.
    destruct H7 as [ts2 [t1s2 [t2s2 [t3s2 [H9 [H10 [H11 H12]]]]]]].
    destruct ts2 => //=.
    destruct t1s2 => //=.
    subst. clear H9. simpl in H8. simpl in H4.
    apply et_to_bet in H8; auto_basic. apply Return_typing in H8.
    destruct H8 as [ts1 [ts2 [H13 H14]]]. subst t2s2.

    assert (ts = ts1). { rewrite -HReturn in H14. by inversion H14. }
    subst ts1. clear H14.

    (* from H11 : typing.e_typing s (upd_label C lab) vs0 (Tf [::] t3s2) *)
    (* show : t3s2 = map typeof vs0' *)
    apply et_to_bet in H11; last by apply const_list_is_basic.
    (* XXX fragile name H *)
    apply const_es_exists in H. destruct H as [vs0' ?]. subst vs0.
    apply Const_list_typing in H11.
    simpl in H11. subst t3s2.

    (* from H12 : typing.e_typing s (upd_label C lab) vs (Tf t3s2 (ts2 ++ ts1)) *)
    (* show : ts2 ++ ts1 = t3s2 ++ [seq typeof i | i <- vs'] *)
    apply et_to_bet in H12; last by apply const_list_is_basic.
    apply const_es_exists in HConst. destruct HConst as [vs' ?]. subst vs.
    apply Const_list_typing in H12.
    simpl in H12.

    assert (ts = vs_to_vts vs') => //. {
      repeat rewrite length_is_size in HLength.
      rewrite v_to_e_size in HLength.
      apply concat_cancel_last_n in H12;
        last by rewrite size_map.
      move/andP in H12. destruct H12 as [? H12]. move/eqP in H12.
      by subst ts.
    }

    subst ts.
    apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
    by apply Const_list_typing_empty.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H2.
    apply e_composition_typing in H4.
    destruct H4 as [ts1 [t1s1 [t2s1 [t3s1 [H6 [H7 [H8 H9]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. clear H6.
    apply Label_typing in H9.
    destruct H9 as [ts' [ts2' [H10 [H11 [H12 H13]]]]].
    subst. simpl in H5.
    eapply IHn => //.
    simpl in H12.
    apply H12.
    apply/lfilledP.
    by apply H1.
Qed.

Lemma Local_return_typing: forall s C vs f LI tf n lh,
    e_typing s C [:: AI_local (length vs) f LI] tf ->
    const_list vs ->
    lfilled n lh (vs ++ [::AI_basic BI_return]) LI ->
    e_typing s C vs tf.
Proof.
  move => s C vs f LI tf n lh HType HConst HLF.
  destruct tf as [t1s t2s].
  apply Local_typing in HType.
  destruct HType as [ts [H1 [H2 H3]]]. subst.
  inversion H2. inversion H. subst. clear H4. clear H2. clear H.
  apply et_weakening_empty_1.
  assert (HET: e_typing s (upd_local_return C2 (tc_local C2 ++ map typeof f.(f_locs)) (Some ts)) vs (Tf [::] ts)).
  { eapply Lfilled_return_typing; eauto. }
  apply et_to_bet in HET; last by apply const_list_is_basic.
  apply const_es_exists in HConst. destruct HConst. subst.
  apply Const_list_typing in HET; subst => /=.
  apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
  by apply Const_list_typing_empty.
Qed.

Lemma Call_typing: forall j C t1s t2s,
    be_typing C [::BI_call j] (Tf t1s t2s) ->
    exists ts t1s' t2s', j < length (tc_func_t C) /\
    List.nth_error (tc_func_t C) j = Some (Tf t1s' t2s') /\
                         t1s = ts ++ t1s' /\
                         t2s = ts ++ t2s'.
Proof.
  move => j C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::], t1s, t2s.
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t1s' [t2s' [H1 [H2 [H3 H4]]]]].
    subst.
    exists (ts ++ x), t1s', t2s'.
    repeat rewrite -catA.
    by repeat (split => //=).
Qed.

Lemma Call_indirect_typing: forall i C t1s t2s,
    be_typing C [::BI_call_indirect i] (Tf t1s t2s) ->
    exists tn tm ts, tc_table C <> nil /\
    i < length (tc_types_t C) /\
    List.nth_error (tc_types_t C) i = Some (Tf tn tm) /\
    t1s = ts ++ tn ++ [::T_i32] /\ t2s = ts ++ tm.
Proof.
  move => i C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t1s0, t2s, [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [tm [ts' [H1 [H2 [H3 [H4 H5]]]]]]. subst.
    exists x, tm, (ts ++ ts').
    by repeat rewrite -catA.
Qed.

End Host.
