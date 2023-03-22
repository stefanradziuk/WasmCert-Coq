(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "theories" "Wasm" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-top" "Wasm.type_checker_reflects_typing" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2047 lines to 693 lines *)
(* coqc version 8.13.2 (March 2023) compiled on Mar 2 2023 16:53:07 with OCaml 4.14.0
   coqtop version 8.13.2 (March 2023)
   Expected coqc runtime on this file: 16.798 sec *)
Require mathcomp.ssreflect.ssreflect.
Require mathcomp.ssreflect.ssrfun.
Require mathcomp.ssreflect.ssrnat.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.eqtype.
Require mathcomp.ssreflect.seq.
Require Coq.Program.Program.
Require StrongInduction.StrongInduction.
Require StrongInduction.Inductions.
Require Coq.micromega.Lia.
Require Wasm.common.
Require Wasm.operations.
Require Wasm.typing.
Require Wasm.type_checker.
Require Wasm.properties.
Require Coq.extraction.Extraction.

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.seq.
Import Coq.Program.Program.
Import StrongInduction.StrongInduction.
Import StrongInduction.Inductions.
Import Coq.micromega.Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Wasm.common.
Import Wasm.operations.
Import Wasm.typing.
Import Wasm.type_checker.
Import Wasm.properties.

Section Host.

Lemma result_typingP : forall r ts,
  reflect (result_typing r ts) (result_types_agree ts r).
Admitted.

Lemma nth_error_ssr: forall {T: Type} (l: list T) n (x x0:T),
  List.nth_error l n = Some x -> nth x0 l n = x.
Admitted.

Lemma size_ct_list: forall l,
  size (to_ct_list l) = size l.
Admitted.

Lemma ssr_nth_error: forall {T: Type} (l: list T) n (x x0:T),
  nth x0 l n = x ->
  n < size l ->
  List.nth_error l n = Some x.
Admitted.

Lemma ct_compat_symmetry: forall c1 c2,
  ct_compat c1 c2 ->
  ct_compat c2 c1.
Admitted.

Lemma ct_list_compat_rcons_bool: forall l1 l2 x1 x2,
  ct_list_compat (rcons l1 x1) (rcons l2 x2) =
  ct_compat x1 x2 && ct_list_compat l1 l2.
Admitted.

Lemma ct_list_compat_rcons: forall l1 l2 x1 x2,
  ct_list_compat (rcons l1 x1) (rcons l2 x2) <->
  ct_compat x1 x2 /\ ct_list_compat l1 l2.
Admitted.

Lemma ct_suffix_rcons: forall l1 l2 x1 x2,
  ct_suffix (rcons l1 x1) (rcons l2 x2) <->
  ct_compat x1 x2 /\ ct_suffix l1 l2.
Admitted.

Lemma ct_suffix_empty: forall l,
  ct_suffix [::] l.
Admitted.

Lemma ct_suffix_any_grow: forall l1 l2,
  ct_suffix l1 l2 ->
  size l1 < size l2 ->
  ct_suffix [::CTA_any & l1] l2.
Admitted.

Lemma ct_suffix_any_1: forall l,
  size l > 0 ->
  ct_suffix [::CTA_any] l.
Admitted.

Lemma ct_list_compat_self: forall l,
  ct_list_compat l l.
Admitted.

Lemma ct_suffix_self: forall l,
  ct_suffix l l.
Admitted.

Lemma ct_suffix_suffix: forall l1 l2,
  ct_suffix (to_ct_list l2) (to_ct_list (l1 ++ l2)).
Admitted.

Lemma ct_suffix_prefix: forall l1 l2 l3,
  ct_suffix (l1 ++ l2) l3 ->
  ct_suffix l2 l3.
Admitted.

Lemma ct_suffix_extend: forall l1 l2 l3,
  ct_suffix l1 l2 ->
  ct_suffix l1 (l3 ++ l2).
Admitted.

Lemma ct_suffix_size: forall ct1 ct2,
  ct_suffix ct1 ct2 ->
  size ct1 <= size ct2.
Admitted.

Lemma upd_label_overwrite: forall C loc lab ret lab',
  upd_label (upd_local_label_return C loc lab ret) lab'
  = upd_local_label_return C loc lab' ret.
Admitted.

Lemma consume_empty: forall l,
  consume l [::] = l.
Admitted.

Lemma produce_empty: forall l,
  produce l (CT_type [::]) = l.
Admitted.

Lemma produce_empty_top: forall l,
  l <> CT_bot ->
  produce l (CT_top_type [::]) = CT_top_type [::].
Admitted.

Lemma type_update_empty_cons: forall l ct,
  type_update l [::] ct = produce l ct.
Admitted.

Lemma type_update_empty_prod: forall l ts,
  type_update l ts (CT_type [::]) = consume l ts.
Admitted.

Ltac simplify_hypothesis Hb :=
  repeat match type of Hb with
  | is_true (es_is_trap _) => move/es_is_trapP: Hb => Hb
  | ?b = true => fold (is_true b) in Hb
  | (_ == _) = false => move/eqP in Hb
  | context C [size (rev _)] => rewrite size_rev in Hb
  | context C [take _ (rev _)] => rewrite take_rev in Hb
  | context C [rev (rev _)] => rewrite revK in Hb
  | context C [true && _] => rewrite Bool.andb_true_l in Hb
  | context C [_ && true] => rewrite Bool.andb_true_r in Hb
  | context C [false || _] => rewrite Bool.orb_false_l in Hb
  | context C [_ || false] => rewrite Bool.orb_false_r in Hb
   
 
  | context C [ct_suffix [::] _] => rewrite ct_suffix_empty in Hb; try simpl in Hb
  | context C [ct_suffix [::CTA_any] (_::_)] => rewrite ct_suffix_any_1 in Hb => //; try simpl in Hb
  | context C [ct_suffix ?l ?l] => rewrite ct_suffix_self in Hb => //; try simpl in Hb
  | context C [size (map _ _)] => rewrite size_map in Hb
  | context C [size (_ ++ _)] => rewrite size_cat in Hb
  | context C [size (to_ct_list _)] => rewrite size_ct_list in Hb
  | context C [?x - 0] => rewrite subn0 in Hb; simpl in Hb
  | context C [?x - ?x] => rewrite subnn in Hb; simpl in Hb
  | context C [take (size ?x) ?x] => rewrite take_size in Hb; simpl in Hb
  | context C [drop (size ?x) ?x] => rewrite drop_size in Hb; simpl in Hb
  | context C [take 0 ?x] => rewrite take0 in Hb; simpl in Hb
  | context C [drop 0 ?x] => rewrite drop0 in Hb; simpl in Hb
  | context C [produce _ _] => unfold produce in Hb; simpl in Hb
  | context C [ match ?u with | Unop_i _ => _ | Unop_f _ => _ end ] => destruct u => //=
  | context C [ match ?b with | Binop_i _ => _ | Binop_f _ => _ end ] => destruct b => //=
  | context C [ match ?r with | Relop_i _ => _ | Relop_f _ => _ end ] => destruct r => //=
  | context C [ match ?c with | CVO_convert => _ | _ => _ end ] => destruct c => //=
  | context C [ if ?expr then _ else _ ] => let if_expr := fresh "if_expr" in destruct expr eqn:if_expr => //=; simpl in Hb => //=
  | context C [ match ?expr with | Some _ => _ | None => _ end ] => let match_expr := fresh "match_expr" in destruct expr eqn:match_expr => //=; simpl in Hb => //=
  | exists _, _ /\ _ => let tx := fresh "tx" in
                        let Hsuffix := fresh "Hsuffix" in
                        let Hbet := fresh "Hbet" in
                        destruct Hb as [tx [Hsuffix Hbet]]
  | is_true true => clear Hb
  | is_true false => exfalso; apply: notF; apply: Hb
  | is_true (_ == _) => move/eqP in Hb
  | is_true (_ && _) => move/andP in Hb; destruct Hb
  | is_true (_ || _) => move/orP in Hb; destruct Hb
  | ?x = ?x => clear Hb
  | _ = _ => rewrite Hb in *; subst => //=
  | _ => simpl in Hb => /=
         end.

Ltac simplify_goal :=
  repeat match goal with H: _ |- _ => progress simplify_hypothesis H end.

Lemma CT_top_empty_consume: forall tf,
  consume (CT_top_type [::]) tf = CT_top_type [::].
Admitted.
Definition populate_ct_aux_single (cta: checker_type_aux): value_type. exact (match cta with
  | CTA_any => T_i32
  | CTA_some vt => vt
  end). Defined.
Definition populate_ct_aux (l: list checker_type_aux): list value_type. exact (map populate_ct_aux_single l). Defined.
Definition populate_ct (ct: checker_type) : list value_type. exact (match ct with
  | CT_type tn => tn
  | CT_top_type tn => populate_ct_aux tn
  | CT_bot => [::]
  end). Defined.

Ltac auto_rewrite_cond:=
  repeat match goal with
         | H: is_true ?expr |- context C [ ?expr ] =>
           rewrite H => //=
         | H: ?x <> ?y |- context C [?x != ?y ] =>
           move/eqP in H; rewrite H => //=
         | H: is_true (Nat.eqb ?x ?y) |- _ =>
           move/eqP in H; rewrite H => //=
         | H: is_true (b_e_type_checker _ _ _) |- _ => simpl in H => //=
         | |- context C [ ?x == ?x ] =>
           rewrite eq_refl => //=
         | |- context C [ true && true ] =>
           unfold andb => //=
         | |- context C [ct_suffix [::] _] => rewrite ct_suffix_empty => //=
         | |- context C [ct_suffix [::CTA_any] (_::_)] => rewrite ct_suffix_any_1 => //=
         | |- context C [ct_suffix ?l ?l] => rewrite ct_suffix_self => //=
         | |- context C [ct_suffix ?l (?l)%list] => rewrite ct_suffix_self => //=
         | |- context C [size (to_ct_list _)] => rewrite size_ct_list => //=
         | |- context C [?x - ?x] => rewrite subnn => //=
         | |- context C [?x - 0] => rewrite subn0 => //=
         | |- context C [take 0 _] => rewrite take0 => //=
         | |- context C [take (size ?x) ?x] => rewrite take_size => //=
         | |- context C [drop 0 _] => rewrite drop0 => //=
         | |- context C [take (drop ?x) ?x] => rewrite drop_size => //=
         | |- context C [_ :: (tc_label _)] => rewrite - cat1s => //=
         | |- context C [_ ++ [::]] => rewrite cats0 => //=
         | |- context C [size (_ ++ _)] => rewrite size_cat => //=
         | |- context C [size (_ ++ _)%list] => rewrite size_cat => //=
         | |- context C [?x + ?n - ?n] => replace (x + n - n) with x; last by lias => //=
         | |- context C [match ?f with | (Tf _ _) => _ end ] => destruct f => //=
 
         | H: match ?expr with | _ => _ end = CT_type _ |- _ => let Hexpr := fresh "Hexpr" in destruct expr eqn: Hexpr => //=
         | H: match ?expr with | _ => _ end = CT_top_type _ |- _ => let Hexpr := fresh "Hexpr" in destruct expr eqn: Hexpr => //=
         | H: option_map _ _ = _ |- _ => unfold option_map in H
         | H: Some _ = Some _ |- _ => inversion H; subst; clear H => //=
         | H: CT_type _ = CT_type _ |- _ => inversion H; subst; clear H => //=
         | H: is_true (plop2 _ _ _) |- _ => unfold plop2 in H => //=
         | H: is_true (List.nth_error _ _ == _) |- _ => move/eqP in H; rewrite H => //=
         | H: is_true (_ == _) |- _ => move/eqP in H
         | H: ?x = ?x |- _ => clear H
         | H: _ = _ |- _=> progress (rewrite H; subst => //=)
         | _ => simplify_goal => //=; (try rewrite ct_suffix_suffix => //=); (try rewrite ct_suffix_self => //=); (try subst => //=)
         end.

 
Lemma populate_ct_aux_suffix: forall l,
  ct_suffix l (to_ct_list (populate_ct_aux l)).
Admitted.

Lemma populate_ct_agree: forall l,
  l <> CT_bot ->
  c_types_agree l (populate_ct l).
Admitted.

Lemma type_update_prefix: forall l1 l2 l3 cons prod,
  type_update (CT_type l1) cons prod = CT_type l2 ->
  type_update (CT_type (l3 ++ l1)) cons prod = CT_type (l3 ++ l2).
Admitted.

Lemma type_update_prefix_top: forall l1 l2 l3 cons prod,
  type_update (CT_type l1) cons prod = CT_top_type l2 ->
  type_update (CT_type (l3 ++ l1)) cons prod = CT_top_type l2.
Admitted.

Lemma check_rcons: forall es e C ts,
  check C (es ++ [::e]) ts = check_single C (check C es ts) e.
Admitted.

Lemma check_single_notop: forall C ct ts e,
  check_single C ct e = CT_type ts ->
  exists ts', ct = CT_type ts'.
Admitted.

Lemma check_single_bot: forall C e,
  check_single C CT_bot e = CT_bot.
Admitted.

Lemma check_single_weaken: forall C e ts ts2 ts0,
  check_single C (CT_type ts) e = CT_type ts0 ->
  check_single C (CT_type (ts2 ++ ts)) e = CT_type (ts2 ++ ts0).
Admitted.

Lemma check_single_weaken_top: forall C e ts ts2 ts0,
  check_single C (CT_type ts) e = CT_top_type ts0 ->
  check_single C (CT_type (ts2 ++ ts)) e = CT_top_type ts0.
Admitted.

Lemma check_weaken: forall C es ts ts2 ts0,
  check C es (CT_type ts) = CT_type ts0 ->
  check C es (CT_type (ts2 ++ ts)) = CT_type (ts2 ++ ts0).
Admitted.

Lemma check_weaken_top: forall C es ts ts2 ts0,
  check C es (CT_type ts) = CT_top_type ts0 ->
  check C es (CT_type (ts2 ++ ts)) = CT_top_type ts0.
Admitted.

Lemma same_lab_h_condition: forall C ts l,
  all (fun i: nat => (i < length (tc_label C)) && plop2 C i ts) l ->
  same_lab_h l (tc_label C) ts = Some ts.
Admitted.

Lemma same_lab_h_all: forall C ts l,
  same_lab_h l (tc_label C) ts = Some ts ->
  all (fun i: nat => (i < length (tc_label C)) && plop2 C i ts) l.
Admitted.

Lemma same_lab_h_rec: forall x l C ts,
  same_lab_h (x :: l) (tc_label C) ts = Some ts ->
  same_lab_h l (tc_label C) ts = Some ts.
Admitted.

Lemma same_lab_h_consistent: forall l lab ts ts',
  same_lab_h l lab ts' = Some ts ->
  ts = ts'.
Admitted.

Lemma same_lab_same_lab_h: forall l lab ts,
  same_lab l lab = Some ts ->
  same_lab_h l lab ts = Some ts.
Admitted.

Lemma ct_list_compat_trans: forall ts1 ts2 ts,
  ct_list_compat (to_ct_list ts) ts1 ->
  ct_list_compat (to_ct_list ts) ts2 ->
  ct_list_compat ts1 ts2.
Admitted.

Lemma ct_suffix_take: forall l1 l2 n,
  ct_suffix l1 l2 ->
  n <= size l1 ->
  ct_suffix (take (size l1 - n) l1) (take (size l2 - n) l2).
Admitted.

Lemma ct_list_compat_cat: forall l1 l2 l3 l4,
  ct_list_compat l1 l2 ->
  ct_list_compat l3 l4 ->
  ct_list_compat (l1 ++ l3) (l2 ++ l4).
Admitted.

Lemma ct_list_compat_extend: forall l1 l2 l3,
  ct_list_compat l1 l2 ->
  ct_list_compat (l1 ++ l3) (l2 ++ l3).
Admitted.

Lemma ct_list_compat_take: forall l1 l2 n,
  ct_list_compat l1 l2 ->
  ct_list_compat (take n l1) (take n l2).
Admitted.

Lemma ct_list_compat_drop: forall l1 l2 n,
  ct_list_compat l1 l2 ->
  ct_list_compat (drop n l1) (drop n l2).
Admitted.

Lemma ct_list_compat_drop_shift: forall l1 l2 n a b c1 c2,
  ct_list_compat (drop n l1) l2 ->
  a < size l1 ->
  b < size l2 ->
  a = b + n ->
  ct_compat (nth c1 l1 a) (nth c2 l2 b).
Admitted.

Lemma ct_list_nth_type: forall l c n,
  n < size l ->
  exists t, nth c (to_ct_list l) n = CTA_some t.
Admitted.

 
Lemma ct_compat_mutual: forall ts1 ts2 ts_mutual ts,
  ts_mutual = to_ct_list ts ->
  size ts1 <= size ts_mutual ->
  size ts2 <= size ts_mutual ->
  ct_list_compat (drop (size ts_mutual - size ts1) ts_mutual) ts1 ->
  ct_list_compat (drop (size ts_mutual - size ts2) ts_mutual) ts2 ->
  size ts1 <= size ts2 ->
  ct_list_compat (drop (size ts2 - size ts1) ts2) ts1.
Admitted.

Lemma ct_suffix_mutual_compat: forall ts1 ts2 ts_mutual ts,
  ts_mutual = to_ct_list ts ->
  ct_suffix ts1 ts_mutual ->
  ct_suffix ts2 ts_mutual ->
  size ts1 <= size ts2 ->
  ct_list_compat (drop (size ts2 - size ts1) ts2) ts1.
Admitted.

Lemma ct_suffix_mutual_suffix: forall ts1 ts2 ts_mutual ts,
  ts_mutual = to_ct_list ts ->
  ct_suffix ts1 ts_mutual ->
  ct_suffix ts2 ts_mutual ->
  size ts1 <= size ts2 ->
  ct_suffix ts1 ts2.
Admitted.

Lemma le_neq_lt: forall a b,
    a <= b ->
    a <> b ->
    a < b.
Admitted.

Lemma sub_if: forall a b,
  (if a-b < a then a-b else a) = a-b.
Admitted.

Lemma type_update_agree_suffix: forall ts cons prod ts2 topt,
  c_types_agree (type_update (CT_type ts) cons prod) ts2 ->
  ct_suffix topt (to_ct_list ts) ->
  c_types_agree (type_update (CT_top_type topt) cons prod) ts2.
Admitted.

Lemma ct_suffix_any_take_2: forall ts,
  2 < size ts ->
  ct_suffix [::CTA_any] (to_ct_list (take (size ts - 2) ts)).
Admitted.

Lemma ct_suffix_compat_index: forall l1 l2 n t1 t2,
  ct_suffix l1 l2 ->
  n >= 1 ->
  n <= size l1 ->
  List.nth_error l1 (length l1 - n) = Some t1 ->
  List.nth_error l2 (length l2 - n) = Some t2 ->
  ct_compat t1 t2.
Admitted.

Lemma ct_suffix_append_compat: forall l1 l2 l3 l4,
  ct_suffix l1 l2 ->
  ct_list_compat l3 l4 ->
  ct_suffix (l1 ++ l3) (l2 ++ l4).
Admitted.

Lemma nth_to_ct_list: forall ts n x,
  List.nth_error ts n = Some x ->
  List.nth_error (to_ct_list ts) n = Some (CTA_some x).
Admitted.

Lemma select_return_top_suffix: forall c2 c3 ts topt topts,
  select_return_top topt c2 c3 = CT_top_type topts ->
  ct_suffix topt (to_ct_list ts) ->
  List.nth_error topt (length topt - 2) = Some c2 ->
  List.nth_error topt (length topt - 3) = Some c3 ->
  List.nth_error ts (length ts - 2) = List.nth_error ts (length ts - 3) ->
  2 < length topt ->
  2 < size ts ->
  ct_suffix topts (to_ct_list (take (size ts - 2) ts)).
Admitted.

 
Lemma type_update_select_agree: forall topt ts,
  ct_suffix [::CTA_any; CTA_some T_i32] (to_ct_list ts) ->
  ct_suffix topt (to_ct_list ts) ->
  2 < length ts ->
  List.nth_error ts (length ts-2) = List.nth_error ts (length ts-3) ->
  c_types_agree (type_update_select (CT_top_type topt)) (take (size ts-2) ts).
Admitted.

Lemma c_types_agree_suffix_single: forall l C ts ts2 e,
  c_types_agree (check_single C (CT_type ts) e) ts2 ->
  ct_suffix l (to_ct_list ts) ->
  c_types_agree (check_single C (CT_top_type l) e) ts2.
Admitted.

Lemma c_types_agree_weakening: forall C es ts ts' ts2,
  c_types_agree (check C es (CT_type ts)) ts2 ->
  c_types_agree (check C es (CT_type (ts' ++ ts))) (ts' ++ ts2).
Admitted.

Lemma ct_list_compat_to_ct: forall tn tm,
  ct_list_compat (to_ct_list tn) (to_ct_list tm) ->
  tn = tm.
Admitted.

Lemma ct_list_compat_symmetry: forall l1 l2,
  ct_list_compat l1 l2 ->
  ct_list_compat l2 l1.
Admitted.

Lemma ct_list_compat_cat1: forall l1 l2 l3,
  ct_list_compat (l2 ++ l3) l1 <->
  ct_list_compat l2 (take (size l2) l1) /\ ct_list_compat l3 (drop (size l2) l1).
Admitted.

Lemma ct_list_compat_cat2: forall l1 l2 l3,
  ct_list_compat l1 (l2 ++ l3) <->
  ct_list_compat (take (size l2) l1) l2 /\ ct_list_compat (drop (size l2) l1) l3.
Admitted.

Lemma ct_suffix_1_impl: forall tm,
  ct_suffix [::CTA_any] (to_ct_list tm) ->
  {v & {tm' & tm = tm' ++ [::v]}}.
Admitted.

Lemma lemma_1: forall C tm x1 x2 l x3,
  (c_types_agree
  match size (rcons l x3) with
  | 0 =>
      if ct_suffix [:: CTA_some T_i32] (rcons (rcons (rcons l x3) x2) x1)
      then
      CT_top_type
      (take ((size (rcons l x3)).+2 - 1)
      (rcons (rcons (rcons l x3) x2) x1))
      else
      if ct_suffix (rcons (rcons (rcons l x3) x2) x1) [:: CTA_some T_i32]
      then CT_top_type [::]
      else CT_bot
  | _.+1 =>
  match
  List.nth_error (rcons (rcons (rcons l x3) x2) x1)
  ((size (rcons l x3)).+2 - 2)
  with
  | Some ts_at_2 =>
      match
      List.nth_error (rcons (rcons (rcons l x3) x2) x1)
      ((size (rcons l x3)).+2 - 3)
      with
      | Some ts_at_3 =>
          type_update (CT_top_type (rcons (rcons (rcons l x3) x2) x1))
          [:: CTA_any; CTA_any; CTA_some T_i32]
          (select_return_top (rcons (rcons (rcons l x3) x2) x1) ts_at_2
          ts_at_3)
      | None => CT_bot
      end
  | None => CT_bot
  end
  end tm) ->
  {tn : seq value_type &
    (ct_suffix (rcons (rcons (rcons l x3) x2) x1) (to_ct_list tn)) **
    (be_typing C [:: BI_select] (Tf tn tm))}.
Proof with auto_rewrite_cond.
  intros C tm x1 x2 l x3.
  rewrite size_rcons.
  repeat rewrite -cats1.
  repeat rewrite -catA.
  intros Hct...
  assert (List.nth_error (l ++ [::x3;x2;x1]) (1+size l) = Some c) as Hnth => //.
  clear match_expr.
  apply nth_error_ssr with (x0 := c) in Hnth.
  apply nth_error_ssr with (x0 := c) in match_expr0.
  replace (_-_) with (size l) in match_expr0; last by lias.
  rewrite nth_cat subnn in match_expr0.
  replace (_<_) with false in match_expr0; last by lias.
  simpl in match_expr0; subst.
  rewrite nth_cat in Hnth.
  replace (_<_) with false in Hnth; last by lias.
  replace (_-_) with 1 in Hnth; last by lias.
  simpl in Hnth; subst.
  unfold select_return_top, type_update in Hct...
  -
    repeat rewrite length_is_size size_cat in Hct.
    replace (size l + size _ - 3) with (size l) in Hct; last by simpl; lias.
    rewrite take_cat subnn take0 cats0 take_size in Hct.
    replace (_<_) with false in Hct; last by lias.
    unfold ct_suffix in if_expr...
    replace (size l + 3 - 3) with (size l) in H0; last by lias.
    rewrite drop_cat subnn drop0 in H0.
    replace (_<_) with false in H0; last by lias.
    auto_rewrite_cond.
    move : Hct.
    case/lastP: tm => [|tm x] => //=; move => Hct.
    +
      destruct c, c0; unfold c_types_agree, ct_suffix; auto_rewrite_cond; by destruct l => //=.
    +
      replace (_+_-_) with (size l) in Hct; last by lias.
      rewrite take_cat subnn take0 cats0 in Hct.
      replace (_<_) with false in Hct; last by lias.
      exists (tm ++ [::x; x; T_i32]).
      repeat rewrite cats1 in Hct.
      split; last by rewrite - cats1; apply bet_weakening; apply bet_select.
      destruct c , c0 => //=; auto_rewrite_cond; unfold to_ct_list in Hct; rewrite map_rcons in Hct; (try rewrite cats1 in Hct); apply ct_suffix_rcons in Hct; destruct Hct; unfold to_ct_list; rewrite map_cat; apply ct_suffix_append_compat => //=...
  -
    unfold ct_suffix in *; destruct l; auto_rewrite_cond; last by lias.
    replace (ct_compat c0 CTA_any) with true in if_expr; last by destruct c0.
    replace (ct_compat c CTA_any) with true in if_expr; last by destruct c.
    simpl in if_expr.
    destruct x1 => //=...
Qed.

Lemma lemma_1_aux: forall C tm x1 l c c0,
  (ct_suffix [:: CTA_any; CTA_any; CTA_some T_i32] (l ++ [:: c0; c; x1])) ->
  (c_types_agree
  match
  match c with
  | CTA_any =>
      match c0 with
      | CTA_any =>
          CT_top_type
          (take (length (l ++ [:: c0; c; x1]) - 3)
          (l ++ [:: c0; c; x1]) ++ [:: c])
      | CTA_some _ =>
          CT_top_type
          (take (length (l ++ [:: c0; c; x1]) - 3)
          (l ++ [:: c0; c; x1]) ++ [:: c0])
      end
  | CTA_some t1 =>
      match c0 with
      | CTA_any =>
          CT_top_type
          (take (length (l ++ [:: c0; c; x1]) - 3)
          (l ++ [:: c0; c; x1]) ++ [:: c])
      | CTA_some t2 =>
          if t1 == t2
          then
          CT_top_type
          (take (length (l ++ [:: c0; c; x1]) - 3)
          (l ++ [:: c0; c; x1]) ++ [:: 
          CTA_some t1])
          else CT_bot
      end
  end
  with
  | CT_top_type ts => CT_top_type ts
  | CT_type ts' =>
      CT_top_type
      (take (size l + 3 - 3) (l ++ [:: c0; c; x1]) ++ to_ct_list ts')
  | CT_bot => CT_bot
  end tm) ->
  {tn : seq value_type &
    (ct_suffix (l ++ [:: c0; c; x1]) (to_ct_list tn)) **
    (be_typing C [:: BI_select] (Tf tn tm))}.
Proof with auto_rewrite_cond.
  intros C tm x1 l c c0 if_expr Hct.
  repeat rewrite length_is_size size_cat in Hct.
  replace (size l + size _ - 3) with (size l) in Hct; last by simpl; lias.
  rewrite take_cat subnn take0 cats0 take_size in Hct.
  replace (_<_) with false in Hct; last by lias.
  unfold ct_suffix in if_expr...
  replace (size l + 3 - 3) with (size l) in H0; last by lias.
  rewrite drop_cat subnn drop0 in H0.
  replace (_<_) with false in H0; last by lias.
  auto_rewrite_cond.
  move : Hct.
  case/lastP: tm => [|tm x] => //=; move => Hct.
  +
    destruct c, c0; unfold c_types_agree, ct_suffix; auto_rewrite_cond; by destruct l => //=.
  +
    replace (_+_-_) with (size l) in Hct; last by lias.
    rewrite take_cat subnn take0 cats0 in Hct.
    replace (_<_) with false in Hct; last by lias.
    exists (tm ++ [::x; x; T_i32]).
    repeat rewrite cats1 in Hct.
    split; last by rewrite - cats1; apply bet_weakening; apply bet_select.
    destruct c , c0 => //=; auto_rewrite_cond; unfold to_ct_list in Hct; rewrite map_rcons in Hct; (try rewrite cats1 in Hct); apply ct_suffix_rcons in Hct; destruct Hct; unfold to_ct_list; rewrite map_cat; apply ct_suffix_append_compat => //=...
Qed.

Lemma lemma_1_using_aux: forall C tm x1 x2 l x3,
  (c_types_agree
  match size (rcons l x3) with
  | 0 =>
      if ct_suffix [:: CTA_some T_i32] (rcons (rcons (rcons l x3) x2) x1)
      then
      CT_top_type
      (take ((size (rcons l x3)).+2 - 1)
      (rcons (rcons (rcons l x3) x2) x1))
      else
      if ct_suffix (rcons (rcons (rcons l x3) x2) x1) [:: CTA_some T_i32]
      then CT_top_type [::]
      else CT_bot
  | _.+1 =>
  match
  List.nth_error (rcons (rcons (rcons l x3) x2) x1)
  ((size (rcons l x3)).+2 - 2)
  with
  | Some ts_at_2 =>
      match
      List.nth_error (rcons (rcons (rcons l x3) x2) x1)
      ((size (rcons l x3)).+2 - 3)
      with
      | Some ts_at_3 =>
          type_update (CT_top_type (rcons (rcons (rcons l x3) x2) x1))
          [:: CTA_any; CTA_any; CTA_some T_i32]
          (select_return_top (rcons (rcons (rcons l x3) x2) x1) ts_at_2
          ts_at_3)
      | None => CT_bot
      end
  | None => CT_bot
  end
  end tm) ->
  {tn : seq value_type &
    (ct_suffix (rcons (rcons (rcons l x3) x2) x1) (to_ct_list tn)) **
    (be_typing C [:: BI_select] (Tf tn tm))}.
Proof with auto_rewrite_cond.
  intros C tm x1 x2 l x3.
  rewrite size_rcons.
  repeat rewrite -cats1.
  repeat rewrite -catA.
  intros Hct...
  assert (List.nth_error (l ++ [::x3;x2;x1]) (1+size l) = Some c) as Hnth => //.
  clear match_expr.
  apply nth_error_ssr with (x0 := c) in Hnth.
  apply nth_error_ssr with (x0 := c) in match_expr0.
  replace (_-_) with (size l) in match_expr0; last by lias.
  rewrite nth_cat subnn in match_expr0.
  replace (_<_) with false in match_expr0; last by lias.
  simpl in match_expr0; subst.
  rewrite nth_cat in Hnth.
  replace (_<_) with false in Hnth; last by lias.
  replace (_-_) with 1 in Hnth; last by lias.
  simpl in Hnth; subst.
  unfold select_return_top, type_update in Hct...
  - by apply lemma_1_aux. (* NOTE *)
  -
    unfold ct_suffix in *; destruct l; auto_rewrite_cond; last by lias.
    replace (ct_compat c0 CTA_any) with true in if_expr; last by destruct c0.
    replace (ct_compat c CTA_any) with true in if_expr; last by destruct c.
    simpl in if_expr.
    destruct x1 => //=...
Qed.

End Host.

Extraction Language Haskell.
(* Time Recursive Extraction lemma_1. *)
(* Finished transaction in 9.562 secs (9.564u,0.s) (successful) *)
Time Recursive Extraction lemma_1_using_aux.
(* Finished transaction in 0.175 secs (0.175u,0.s) (successful) *)

