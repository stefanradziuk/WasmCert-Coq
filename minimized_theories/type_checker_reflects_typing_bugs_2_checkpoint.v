(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "theories" "Wasm" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-top" "Wasm.type_checker_reflects_typing" "-native-compiler" "ondemand" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2047 lines to 693 lines, then from 735 lines to 233 lines, then from 246 lines to 1505 lines, then from 1504 lines to 243 lines, then from 256 lines to 747 lines, then from 748 lines to 588 lines *)
(* coqc version 8.13.2 (March 2023) compiled on Mar 2 2023 16:53:07 with OCaml 4.14.0
   coqtop version 8.13.2 (March 2023)
   Expected coqc runtime on this file: 8.174 sec *)
Require Wasm.typing.
 
 
Import Wasm.common.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.seq.
Import Wasm.operations.
Import Wasm.typing.

Section Host.
 

Inductive checker_type_aux : Type :=
| CTA_any : checker_type_aux
| CTA_some : value_type -> checker_type_aux.

Inductive checker_type : Type :=
| CT_top_type : seq checker_type_aux -> checker_type
| CT_type : seq value_type -> checker_type
| CT_bot : checker_type.

Definition checker_type_eq_dec : forall v1 v2 : checker_type, {v1 = v2} + {v1 <> v2}.
Admitted.

Definition checker_type_eqb v1 v2 : bool := checker_type_eq_dec v1 v2.
Definition eqchecker_typeP : Equality.axiom checker_type_eqb.
exact (eq_dec_Equality_axiom checker_type_eq_dec).
Defined.

Canonical Structure checker_type_eqMixin := EqMixin eqchecker_typeP.
Canonical Structure checker_type_eqType := Eval hnf in EqType checker_type checker_type_eqMixin.
Definition to_ct_list (ts : seq value_type) : seq checker_type_aux.
exact (map CTA_some ts).
Defined.
Definition ct_compat (t1 t2: checker_type_aux) : bool.
exact (match t1 with
  | CTA_any => true
  | CTA_some vt1 =>
    match t2 with
    | CTA_any => true
    | CTA_some vt2 => (vt1 == vt2)
    end
  end).
Defined.
Definition ct_list_compat (l1 l2: list checker_type_aux) : bool.
exact (all2 ct_compat l1 l2).
Defined.
Definition ct_suffix (ts ts' : list checker_type_aux) : bool.
exact ((size ts <= size ts') && (ct_list_compat (drop (size ts' - size ts) ts') ts)).
Defined.
Definition consume (t : checker_type) (cons : seq checker_type_aux) : checker_type.
exact (match t with
  | CT_type ts =>
    if ct_suffix cons (to_ct_list ts)
    then CT_type (take (size ts - size cons) ts)
    else CT_bot
  | CT_top_type cts =>
    if ct_suffix cons cts
    then CT_top_type (take (size cts - size cons) cts)
    else
      (if ct_suffix cts cons
       then CT_top_type [::]
       else CT_bot)
  | _ => CT_bot
  end).
Defined.
Definition produce (t1 t2 : checker_type) : checker_type.
exact (match (t1, t2) with
  | (CT_top_type ts, CT_type ts') => CT_top_type (ts ++ (to_ct_list ts'))
  | (CT_type ts, CT_type ts') => CT_type (ts ++ ts')
  | (CT_type ts', CT_top_type ts) => CT_top_type ts
  | (CT_top_type ts', CT_top_type ts) => CT_top_type ts
  | _ => CT_bot
  end).
Defined.
Definition type_update (curr_type : checker_type) (cons : seq checker_type_aux) (prods : checker_type) : checker_type.
exact (produce (consume curr_type cons) prods).
Defined.
Definition select_return_top (ts : seq checker_type_aux) (cta1 cta2 : checker_type_aux) : checker_type.
exact (match (cta1, cta2) with
  | (_, CTA_any) => CT_top_type (take (length ts - 3) ts ++ [::cta1])
  | (CTA_any, _) => CT_top_type (take (length ts - 3) ts ++ [::cta2])
  | (CTA_some t1, CTA_some t2) =>
    if t1 == t2
    then CT_top_type (take (length ts - 3) ts ++ [::CTA_some t1])
    else CT_bot
  end).
Defined.
Definition type_update_select (t : checker_type) : checker_type.
exact (match t with
  | CT_type ts =>
    if (length ts >= 3) && (List.nth_error ts (length ts - 2) == List.nth_error ts (length ts - 3))
    then (consume (CT_type ts) [::CTA_any; CTA_some T_i32])
    else CT_bot
  | CT_top_type ts =>
    match length ts with
    | 0 => CT_top_type [::CTA_any]
    | 1 => type_update (CT_top_type ts) [::CTA_some T_i32] (CT_top_type [::CTA_any])
    | 2 => consume (CT_top_type ts) [::CTA_some T_i32]
    | _ =>
      match List.nth_error ts (length ts - 2), List.nth_error ts (length ts - 3) with
      | Some ts_at_2, Some ts_at_3 =>
        type_update (CT_top_type ts) [::CTA_any; CTA_any; CTA_some T_i32]
                    (select_return_top ts ts_at_2 ts_at_3)
                 

      | _, _ => CT_bot  
      end
    end
  | CT_bot => CT_bot
  end).
Defined.
Fixpoint same_lab_h (iss : seq nat) (lab_c : seq (seq value_type)) (ts : seq value_type) : option (seq value_type).
exact (match iss with
  | [::] => Some ts
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | None => None  
                   
      | Some xx =>
        if xx == ts then same_lab_h iss' lab_c xx
        else None
      end
  end).
Defined.
Definition same_lab (iss : seq nat) (lab_c : seq (seq value_type)) : option (seq value_type).
exact (match iss with
  | [::] => None
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | Some xx => same_lab_h iss' lab_c xx
      | None => None  
                   
                   
      end
  end).
Defined.
Definition c_types_agree (ct : checker_type) (ts' : seq value_type) : bool.
exact (match ct with
  | CT_type ts => ts == ts'
  | CT_top_type ts => ct_suffix ts (to_ct_list ts')
  | CT_bot => false
  end).
Defined.

Definition is_int (t: value_type) :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  end.

Definition is_float (t: value_type) :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  end.
Fixpoint check_single (C : t_context) (ts : checker_type) (be : basic_instruction) : checker_type.
exact (let b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
    let: (Tf tn tm) := tf in
      c_types_agree (List.fold_left (check_single C) es (CT_type tn)) tm
in
  if ts == CT_bot then CT_bot
  else
  match be with
  | BI_const v => type_update ts [::] (CT_type [::typeof v])
  | BI_unop t op =>
    match op with
    | Unop_i _ => if is_int t
                  then type_update ts [::CTA_some t] (CT_type [::t])
                  else CT_bot
    | Unop_f _ => if is_float t
                  then type_update ts [::CTA_some t] (CT_type [::t])
                  else CT_bot
    end
  | BI_binop t op =>
    match op with
    | Binop_i _ => if is_int t
                  then type_update ts [::CTA_some t; CTA_some t] (CT_type [::t])
                  else CT_bot
    | Binop_f _ => if is_float t
                  then type_update ts [::CTA_some t; CTA_some t] (CT_type [::t])
                  else CT_bot
    end
  | BI_testop t _ =>
    if is_int_t t
    then type_update ts [::CTA_some t] (CT_type [::T_i32])
    else CT_bot
  | BI_relop t op =>
    match op with
    | Relop_i _ => if is_int t
                  then type_update ts [::CTA_some t; CTA_some t] (CT_type [::T_i32])
                  else CT_bot
    | Relop_f _ => if is_float t
                  then type_update ts [::CTA_some t; CTA_some t] (CT_type [::T_i32])
                  else CT_bot
    end
  | BI_cvtop t1 CVO_convert t2 sx =>
    if typing.convert_cond t1 t2 sx
    then type_update ts [::CTA_some t2] (CT_type [::t1])
    else CT_bot
  | BI_cvtop t1 CVO_reinterpret t2 sxo =>
    if (t1 != t2) && (t_length t1 == t_length t2) && (sxo == None)
    then type_update ts [::CTA_some t2] (CT_type [::t1])
    else CT_bot
  | BI_unreachable => type_update ts [::] (CT_top_type [::])
  | BI_nop => ts
  | BI_drop => type_update ts [::CTA_any] (CT_type [::])
  | BI_select => type_update_select ts
  | BI_block (Tf tn tm) es =>
    if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es (Tf tn tm)
    then type_update ts (to_ct_list tn) (CT_type tm)
    else CT_bot
  | BI_loop (Tf tn tm) es =>
    if b_e_type_checker (upd_label C ([::tn] ++ tc_label C)) es (Tf tn tm)
    then type_update ts (to_ct_list tn) (CT_type tm)
    else CT_bot
  | BI_if (Tf tn tm) es1 es2 =>
    if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es1 (Tf tn tm)
                        && b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es2 (Tf tn tm)
    then type_update ts (to_ct_list (tn ++ [::T_i32])) (CT_type tm)
    else CT_bot
  | BI_br i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list xx) (CT_top_type [::])
      | None => CT_bot  
                   
      end
    else CT_bot
  | BI_br_if i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list (xx ++ [::T_i32])) (CT_type xx)
      | None => CT_bot  
      end
    else CT_bot
  | BI_br_table iss i =>
    match same_lab (iss ++ [::i]) (tc_label C) with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list (tls ++ [::T_i32])) (CT_top_type [::])
    end
  | BI_return =>
    match tc_return C with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list tls) (CT_top_type [::])
    end
  | BI_call i =>
    if i < length (tc_func_t C)
    then
      match List.nth_error (tc_func_t C) i with
      | None => CT_bot  
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list tn) (CT_type tm)
      end
    else CT_bot
  | BI_call_indirect i =>
    if (1 <= length C.(tc_table)) && (i < length C.(tc_types_t))
    then
      match List.nth_error (tc_types_t C) i with
      | None => CT_bot  
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list (tn ++ [::T_i32])) (CT_type tm)
      end
    else CT_bot
  | BI_get_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot  
      | Some xx => type_update ts [::] (CT_type [::xx])
      end
    else CT_bot
  | BI_set_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot  
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::])
      end
    else CT_bot
  | BI_tee_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot  
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::xx])
      end
    else CT_bot
  | BI_get_global i =>
    if i < length (tc_global C)
    then
      match List.nth_error (tc_global C) i with
      | None => CT_bot  
      | Some xx => type_update ts [::] (CT_type [::tg_t xx])
      end
    else CT_bot
  | BI_set_global i =>
    if i < length (tc_global C)
    then
      match List.nth_error (tc_global C) i with
      | None => CT_bot  
      | Some xx =>
        if is_mut xx
        then type_update ts [::CTA_some (tg_t xx)] (CT_type [::])
        else CT_bot
      end
    else CT_bot
  | BI_load t tp_sx a off =>
    if (C.(tc_memory) != nil) && load_store_t_bounds a (option_projl tp_sx) t
    then type_update ts [::CTA_some T_i32] (CT_type [::t])
    else CT_bot
  | BI_store t tp a off =>
    if (C.(tc_memory) != nil) && load_store_t_bounds a tp t
    then type_update ts [::CTA_some T_i32; CTA_some t] (CT_type [::])
    else CT_bot
  | BI_current_memory =>
    if C.(tc_memory) != nil
    then type_update ts [::] (CT_type [::T_i32])
    else CT_bot
  | BI_grow_memory =>
    if C.(tc_memory) != nil
    then type_update ts [::CTA_some T_i32] (CT_type [::T_i32])
    else CT_bot
  end).
Defined.
Definition b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool.
Admitted.

 

 
 
End Host.
Export Wasm.operations.
Export Wasm.typing.
Export Wasm.common.
Import mathcomp.ssreflect.seq.

Section Host.

Lemma length_is_size: forall {X:Type} (l: list X),
    length l = size l.
Admitted.

End Host.

Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.

Section Host.

Lemma nth_error_ssr: forall {T: Type} (l: list T) n (x x0:T),
  List.nth_error l n = Some x -> nth x0 l n = x.
Admitted.

Lemma size_ct_list: forall l,
  size (to_ct_list l) = size l.
Admitted.

Lemma ct_suffix_rcons: forall l1 l2 x1 x2,
  ct_suffix (rcons l1 x1) (rcons l2 x2) <->
  ct_compat x1 x2 /\ ct_suffix l1 l2.
Admitted.

Lemma ct_suffix_empty: forall l,
  ct_suffix [::] l.
Admitted.

Lemma ct_suffix_any_1: forall l,
  size l > 0 ->
  ct_suffix [::CTA_any] l.
Admitted.

Lemma ct_suffix_self: forall l,
  ct_suffix l l.
Admitted.

Lemma ct_suffix_suffix: forall l1 l2,
  ct_suffix (to_ct_list l2) (to_ct_list (l1 ++ l2)).
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

Lemma ct_suffix_append_compat: forall l1 l2 l3 l4,
  ct_suffix l1 l2 ->
  ct_list_compat l3 l4 ->
  ct_suffix (l1 ++ l3) (l2 ++ l4).
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

End Host.

Extraction Language Haskell.

Time Timeout 7 Recursive Extraction lemma_1.

