(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "theories" "Wasm" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-top" "Wasm.type_checker_reflects_typing" "-native-compiler" "ondemand" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2047 lines to 693 lines, then from 735 lines to 233 lines, then from 246 lines to 1505 lines, then from 1504 lines to 243 lines, then from 256 lines to 747 lines, then from 748 lines to 322 lines, then from 335 lines to 984 lines, then from 983 lines to 640 lines *)
(* coqc version 8.13.2 (March 2023) compiled on Mar 2 2023 16:53:07 with OCaml 4.14.0
   coqtop version 8.13.2 (March 2023)
   Expected coqc runtime on this file: 8.285 sec *)
Require Coq.Arith.Le.
Require Coq.Bool.Bool.
Require Coq.Lists.List.
Require Coq.NArith.BinNat.
Require Coq.NArith.NArith.
Require Coq.Program.Equality.
Require Coq.ZArith.BinInt.
Require Coq.ZArith.Int.
Require Coq.micromega.Lia.
Require ITree.ITree.
Require ITree.ITreeFacts.
Require Wasm.array.
Require compcert.common.Memdata.
Require compcert.lib.Floats.
Require compcert.lib.Integers.
Require mathcomp.ssreflect.eqtype.
Require mathcomp.ssreflect.seq.
Require mathcomp.ssreflect.ssrbool.
Require mathcomp.ssreflect.ssreflect.
Require mathcomp.ssreflect.ssrfun.
Require mathcomp.ssreflect.ssrnat.
Require parseque.Char.
Require Wasm.extraction_utils.
Require Wasm.list_extra.
Require Wasm.pickability.
Require Wasm.common.
Require Wasm.bytes.
Require Wasm.numerics.
Require Wasm.memory.
Require Wasm.memory_list.
Require Wasm.datatypes.
Require Wasm.datatypes_properties.
Require Wasm.operations.

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Wasm_DOT_typing_WRAPPED.
Module typing.
 
 
Import mathcomp.ssreflect.ssreflect mathcomp.ssreflect.ssrfun mathcomp.ssreflect.ssrnat mathcomp.ssreflect.ssrbool mathcomp.ssreflect.eqtype mathcomp.ssreflect.seq.
Import Wasm.operations.
Import Coq.NArith.NArith.

 

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let function_closure := function_closure host_function.
Let store_record := store_record host_function.
 

 

 

 
Definition convert_helper (sxo : option sx) t1 t2 : bool :=
  (sxo == None) ==
  ((is_float_t t1 && is_float_t t2) || (is_int_t t1 && is_int_t t2 && (t_length t1 < t_length t2))).

Definition upd_label C lab :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    (tc_local C)
    lab
    (tc_return C).

 
 
Definition plop2 C i ts :=
  List.nth_error (tc_label C) i == Some ts.

Inductive unop_type_agree: value_type -> unop -> Prop :=
  | Unop_i32_agree: forall op, unop_type_agree T_i32 (Unop_i op)
  | Unop_i64_agree: forall op, unop_type_agree T_i64 (Unop_i op)
  | Unop_f32_agree: forall op, unop_type_agree T_f32 (Unop_f op)
  | Unop_f64_agree: forall op, unop_type_agree T_f64 (Unop_f op)
  .

Inductive binop_type_agree: value_type -> binop -> Prop :=
  | Binop_i32_agree: forall op, binop_type_agree T_i32 (Binop_i op)
  | Binop_i64_agree: forall op, binop_type_agree T_i64 (Binop_i op)
  | Binop_f32_agree: forall op, binop_type_agree T_f32 (Binop_f op)
  | Binop_f64_agree: forall op, binop_type_agree T_f64 (Binop_f op)
  .

Inductive relop_type_agree: value_type -> relop -> Prop :=
  | Relop_i32_agree: forall op, relop_type_agree T_i32 (Relop_i op)
  | Relop_i64_agree: forall op, relop_type_agree T_i64 (Relop_i op)
  | Relop_f32_agree: forall op, relop_type_agree T_f32 (Relop_f op)
  | Relop_f64_agree: forall op, relop_type_agree T_f64 (Relop_f op)
  .

Inductive be_typing : t_context -> seq basic_instruction -> function_type -> Type :=
 
| bet_const : forall C v, be_typing C [::BI_const v] (Tf [::] [::typeof v])
| bet_unop : forall C t op,
    unop_type_agree t op -> be_typing C [::BI_unop t op] (Tf [::t] [::t])
| bet_binop : forall C t op,
    binop_type_agree t op -> be_typing C [::BI_binop t op] (Tf [::t; t] [::t])
| bet_testop : forall C t op, is_int_t t -> be_typing C [::BI_testop t op] (Tf [::t] [::T_i32])
| bet_relop: forall C t op,
    relop_type_agree t op -> be_typing C [::BI_relop t op] (Tf [::t; t] [::T_i32])
| bet_convert : forall C t1 t2 sx, t1 <> t2 -> convert_helper sx t1 t2 ->
  be_typing C [::BI_cvtop t1 CVO_convert t2 sx] (Tf [::t2] [::t1])  
| bet_reinterpret : forall C t1 t2, t1 <> t2 -> Nat.eqb (t_length t1) (t_length t2) ->
  be_typing C [::BI_cvtop t1 CVO_reinterpret t2 None] (Tf [::t2] [::t1])
| bet_unreachable : forall C ts ts',
  be_typing C [::BI_unreachable] (Tf ts ts')
| bet_nop : forall C, be_typing C [::BI_nop] (Tf [::] [::])
| bet_drop : forall C t, be_typing C [::BI_drop] (Tf [::t] [::])
| bet_select : forall C t, be_typing C [::BI_select] (Tf [::t; t; T_i32] [::t])
| bet_block : forall C tn tm es,
  let tf := Tf tn tm in
  be_typing (upd_label C (app [::tm] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::BI_block tf es] (Tf tn tm)
| bet_loop : forall C tn tm es,
  be_typing (upd_label C (app [::tn] (tc_label C))) es (Tf tn tm) ->
  be_typing C [::BI_loop (Tf tn tm) es] (Tf tn tm)
| bet_if_wasm : forall C tn tm es1 es2,
  be_typing (upd_label C (app [::tm] (tc_label C))) es1 (Tf tn tm) ->
  be_typing (upd_label C (app [::tm] (tc_label C))) es2 (Tf tn tm) ->
  be_typing C [::BI_if (Tf tn tm) es1 es2] (Tf (app tn [::T_i32]) tm)
| bet_br : forall C i t1s ts t2s,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::BI_br i] (Tf (app t1s ts) t2s)
| bet_br_if : forall C i ts,
  i < length (tc_label C) ->
  plop2 C i ts ->
  be_typing C [::BI_br_if i] (Tf (app ts [::T_i32]) ts)
| bet_br_table : forall C i ins ts t1s t2s,
  all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (app ins [::i])  ->
  be_typing C [::BI_br_table ins i] (Tf (app t1s (app ts [::T_i32])) t2s)
| bet_return : forall C ts t1s t2s,
  tc_return C = Some ts ->
  be_typing C [::BI_return] (Tf (app t1s ts) t2s)
| bet_call : forall C i tf,
  i < length (tc_func_t C) ->
  List.nth_error (tc_func_t C) i = Some tf ->
  be_typing C [::BI_call i] tf
| bet_call_indirect : forall C i t1s t2s,
  i < length (tc_types_t C) ->
  List.nth_error (tc_types_t C) i = Some (Tf t1s t2s) ->
  tc_table C <> nil ->  
  be_typing C [::BI_call_indirect i] (Tf (app t1s [::T_i32]) t2s)
| bet_get_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::BI_get_local i] (Tf [::] [::t])
| bet_set_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::BI_set_local i] (Tf [::t] [::])
| bet_tee_local : forall C i t,
  i < length (tc_local C) ->
  List.nth_error (tc_local C) i = Some t ->
  be_typing C [::BI_tee_local i] (Tf [::t] [::t])
| bet_get_global : forall C i t,
  i < length (tc_global C) ->
  option_map tg_t (List.nth_error (tc_global C) i) = Some t ->
  be_typing C [::BI_get_global i] (Tf [::] [::t])
| bet_set_global : forall C i g t,
  i < length (tc_global C) ->
  List.nth_error (tc_global C) i = Some g ->
  tg_t g = t ->
  is_mut g ->
  be_typing C [::BI_set_global i] (Tf [::t] [::])
| bet_load : forall C a off tp_sx t,
  tc_memory C <> nil ->
  load_store_t_bounds a (option_projl tp_sx) t ->
  be_typing C [::BI_load t tp_sx a off] (Tf [::T_i32] [::t])
| bet_store : forall C a off tp t,
  tc_memory C <> nil ->
  load_store_t_bounds a tp t ->
  be_typing C [::BI_store t tp a off] (Tf [::T_i32; t] [::])  
| bet_current_memory : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_current_memory] (Tf [::] [::T_i32])
| bet_grow_memory : forall C,
  tc_memory C <> nil ->
  be_typing C [::BI_grow_memory] (Tf [::T_i32] [::T_i32])
| bet_empty : forall C,
  be_typing C [::] (Tf [::] [::])
| bet_composition : forall C es e t1s t2s t3s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C [::e] (Tf t2s t3s) ->
  be_typing C (app es [::e]) (Tf t1s t3s)
| bet_weakening : forall C es ts t1s t2s,
  be_typing C es (Tf t1s t2s) ->
  be_typing C es (Tf (app ts t1s) (app ts t2s))
.

Definition upd_local_label_return C loc lab ret :=
  Build_t_context
    (tc_types_t C)
    (tc_func_t C)
    (tc_global C)
    (tc_table C)
    (tc_memory C)
    loc
    lab
    ret.

 

Definition global_agree (g : global) (tg : global_type) : bool :=
  (tg_mut tg == g_mut g) && (tg_t tg == typeof (g_val g)).

 
Definition globals_agree (gs : seq global) (n : nat) (tg : global_type) : bool :=
  (n < length gs) && (option_map (fun g => global_agree g tg) (List.nth_error gs n) == Some true).

Definition mem_typing (m : memory) (m_t : memory_type) : bool :=
  (N.leb m_t.(lim_min) (mem_size m)) &&
  (m.(mem_max_opt) == m_t.(lim_max))  .

Definition memi_agree (ms : list memory) (n : nat) (mem_t : memory_type) : bool :=
  (n < length ms) &&
  match List.nth_error ms n with
  | Some mem => mem_typing mem mem_t
  | None => false
  end.

Definition functions_agree (fs : seq function_closure) (n : nat) (f : function_type) : bool :=
  (n < length fs) && (option_map cl_type (List.nth_error fs n) == Some f).

 

 

Definition tab_typing (t : tableinst) (tt : table_type) : bool :=
  (tt.(tt_limits).(lim_min) <= tab_size t) &&
  (t.(table_max_opt) <= tt.(tt_limits).(lim_max)).

Definition tabi_agree ts (n : nat) (tab_t : table_type) : bool :=
  (n < List.length ts) &&
  match List.nth_error ts n with
  | None => false
  | Some x => tab_typing x tab_t
  end.

Definition inst_typing (s : store_record) (inst : instance) (C : t_context) : bool :=
  let '{| inst_types := ts; inst_funcs := fs; inst_tab := tbs; inst_memory := ms; inst_globs := gs; |} := inst in
  match C with
  | {| tc_types_t := ts'; tc_func_t := tfs; tc_global := tgs; tc_table := tabs_t; tc_memory := mems_t; tc_local := nil; tc_label := nil; tc_return := None |} =>
    (ts == ts') &&
    (all2 (functions_agree s.(s_funcs)) fs tfs) &&
    (all2 (globals_agree s.(s_globals)) gs tgs) &&
    (all2 (tabi_agree s.(s_tables)) tbs tabs_t) &&
    (all2 (memi_agree s.(s_mems)) ms mems_t)
  | _ => false
  end.

Lemma functions_agree_injective: forall s i t t',
  functions_agree s i t ->
  functions_agree s i t' ->
  t = t'.
Proof.
  move => s i t t' H1 H2.
  unfold functions_agree in H1.
unfold functions_agree in H2.
   
  move/andP: H1 => [_ H1].
  move/andP: H2 => [_ H3].
  move/eqP in H1.
move/eqP in H3.
  rewrite H3 in H1 => {H3}.
  by move: H1 => [H1].
Qed.

 
Inductive cl_typing : store_record -> function_closure -> function_type -> Type :=
  | cl_typing_native : forall i s C C' ts t1s t2s es tf,
    inst_typing s i C ->
    tf = Tf t1s t2s ->
    C' = upd_local_label_return C (tc_local C ++ t1s ++ ts) ([::t2s] ++ tc_label C) (Some t2s) ->
    be_typing C' es (Tf [::] t2s) ->
    cl_typing s (FC_func_native i tf ts es) (Tf t1s t2s)
  | cl_typing_host : forall s tf h,
    cl_typing s (FC_func_host tf h) tf
  .

Lemma cl_typing_unique : forall s cl tf, cl_typing s cl tf -> tf = cl_type cl.
Admitted.

End Host.

End typing.

End Wasm_DOT_typing_WRAPPED.
Module Export Wasm_DOT_typing.
Module Export Wasm.
Module typing.
Include Wasm_DOT_typing_WRAPPED.typing.
End typing.

End Wasm.

End Wasm_DOT_typing.

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
Definition c_types_agree (ct : checker_type) (ts' : seq value_type) : bool.
exact (match ct with
  | CT_type ts => ts == ts'
  | CT_top_type ts => ct_suffix ts (to_ct_list ts')
  | CT_bot => false
  end).
Defined.
Definition b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool.
Admitted.

End Host.

Section Host.

Lemma length_is_size: forall {X:Type} (l: list X),
    length l = size l.
Admitted.

End Host.

Import mathcomp.ssreflect.ssreflect.

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

