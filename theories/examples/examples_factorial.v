From Coq Require Import ZArith Strings.String Lists.List.
From Wasm Require Import interpreter_func_sound instantiation.
From mathcomp Require Import ssreflect eqtype seq ssrbool.
(* From iris.program_logic Require Import language. *)
(* From iris.proofmode Require Import base tactics classes. *)
(* From iris.base_logic Require Export gen_heap ghost_map proph_map. *)
(* From iris.base_logic.lib Require Export fancy_updates. *)
(* From iris.bi Require Export weakestpre. *)
(* Require Export iris iris_locations iris_properties iris_atomicity stdpp_aux. *)
(* Require Export iris_rules iris_example_helper iris_host proofmode. *)
Require Export datatypes operations properties opsem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Close Scope byte_scope.

Section Helper.
  (* Shorthands for common constructors *)
  Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
  Definition xb b := (VAL_int32 (wasm_bool b)).
  Definition yy i := (Wasm_int.nat_of_uint i32m (Wasm_int.int_of_Z i32m i)).
End Helper.

(* Example Programs *)
Section Factorial.
  (* Context `{!wasmG Σ}. *)

  (* --------------------------------------------------------------------------------------------- *)
  (* ------------------------- LOCAL STATE EXAMPLE: FACTORIAL ------------------------------------ *)
  (* --------------------------------------------------------------------------------------------- *)

  Definition factorial_instrs fact : seq.seq basic_instruction :=
    [::(BI_get_local 0);
     (BI_const (xx 1));
     (BI_relop T_i32 (Relop_i (ROI_le SX_U)));
     (BI_if (Tf [::] [::T_i32])
        [::BI_const (xx 1)]

        [::BI_get_local 0;
         BI_const (xx 1);
         BI_binop T_i32 (Binop_i BOI_sub);
         BI_call fact;
         BI_get_local 0;
         BI_binop T_i32 (Binop_i BOI_mul)])].

  Definition factorial fact := to_e_list (factorial_instrs fact).

End Factorial.

Section Factorial.
  (* Context `{!wasmG Σ}. *)
  
  (* --------------------------------------------------------------------------------------------- *)
  (* ------------------------- LANDIN'S KNOT EXAMPLE: FACTORIAL ---------------------------------- *)
  (* --------------------------------------------------------------------------------------------- *)


  Definition myrec_instr h_mut_tab :=
    [::BI_const (xx 0);
     BI_get_local 0;
     BI_call h_mut_tab].
  Definition myrec h_mut_tab := to_e_list (myrec_instr h_mut_tab).

  Definition F_instr rec_typ :=
    [::(BI_get_local 0);
     (BI_const (xx 1));
     (BI_relop T_i32 (Relop_i (ROI_le SX_U)));
     (BI_if (Tf [::] [::T_i32])
        [::BI_const (xx 1)]
        
        [::BI_get_local 0;
         BI_const (xx 1);
         BI_binop T_i32 (Binop_i BOI_sub);
         BI_const (xx 0);
         BI_call_indirect rec_typ;
         BI_get_local 0;
         BI_binop T_i32 (Binop_i BOI_mul)])].
  Definition F rec_typ :=
    to_e_list (F_instr rec_typ).

  Definition fact_instr F myrec fact_typ :=
    [::BI_get_local 0;
     BI_const F;
     BI_call myrec;
     BI_const (xx 0);
     BI_call_indirect fact_typ].
  Definition fact F myrec fact_typ :=
    to_e_list (fact_instr F myrec fact_typ).

End Factorial.

Section FactorialHostMain.
  (* Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}. *)

  Definition main_instr fact glob :=
    [::BI_get_global glob;
     BI_call fact;
     BI_set_global glob].
  Definition main fact glob := to_e_list (main_instr fact glob).

End FactorialHostMain.

Section FactorialHost.
  (* Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}. *)

  Definition factorial_module :=
    {|
      mod_types := [:: Tf [::T_i32] [::T_i32] ; Tf [::T_i32] [::] ; Tf [::T_i32; T_i32] [::] ; Tf [::] [::] ] ;
      mod_funcs :=
      [:: {|
          modfunc_type := Mk_typeidx 1 ;
          modfunc_locals := [::] ;
          modfunc_body := myrec_instr 0
        |};
        {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [::] ;
          modfunc_body := F_instr 0
        |};
        {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [::] ;
          modfunc_body := fact_instr (xx 2) 1 0
        |};
        {|
          modfunc_type := Mk_typeidx 3 ;
          modfunc_locals := [::] ;
          modfunc_body := main_instr 3 0
        |}
      ] ;
      mod_tables := [:: {| modtab_type := {| tt_limits := {| lim_min := 1 ; lim_max := None |} ; tt_elem_type := ELT_funcref |} |} ] ; 
      mod_mems := [::] ;
      mod_globals := [:: (* {| modglob_type := {| tg_mut := MUT_mut ; tg_t := T_i32 |} ; modglob_init := [::BI_const (xx 0)] |} *) ] ;
      mod_elem := [::] ;
      mod_data := [::] ;
      mod_start := Some (Build_module_start (Mk_funcidx 4)) ;
      mod_imports :=
        [:: {|
            imp_module := list_byte_of_string "Host" ;
            imp_name := list_byte_of_string "modify_table" ;
            imp_desc := ID_func 2
          |};
          {|
            imp_module := list_byte_of_string "Host" ;
            imp_name := list_byte_of_string "ret" ;
            imp_desc := ID_global {| tg_mut := MUT_mut ; tg_t := T_i32 |}
          |}
        ];
      mod_exports := [::]
    |}.

  Definition factorial_impts : seq.seq extern_t := [::ET_func (Tf [::T_i32; T_i32] [::]); ET_glob {| tg_mut := MUT_mut ; tg_t := T_i32 |}].

  Ltac type_next_rewrite :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(take_drop (length e - 1) e);simpl take; simpl drop
  end.
  Ltac type_next :=
  match goal with
  | |- context [ be_typing _ ?e _  ] =>
      rewrite -(take_drop (length e - 1) e);simpl take; simpl drop;
      eapply bet_composition;[|econstructor;eauto];simpl
  end.
  Ltac weaken :=
  match goal with
  | |- context [ be_typing _ ?e (Tf ?t1 ?t)  ] =>
      try rewrite <- (app_nil_r t1);
      rewrite -(take_drop (length t - 1) t);simpl take; simpl drop;
      eapply bet_weakening;constructor;auto
  end.
  Ltac type_go := repeat (constructor || type_next || weaken || (type_next_rewrite; eapply bet_composition; [constructor|])).

  Definition bt0 : be_typing {|
    tc_types_t :=
      [::Tf [::T_i32] [::T_i32]; Tf [::T_i32] [::]; Tf [::T_i32; T_i32] [::]; Tf [::] [::]];
    tc_func_t :=
      [::Tf [::T_i32; T_i32] [::]; Tf [::T_i32] [::]; Tf [::T_i32] [::T_i32];
      Tf [::T_i32] [::T_i32]; Tf [::] [::]];
    tc_global := [::{| tg_mut := MUT_mut; tg_t := T_i32 |}];
    tc_table :=
      [::{|
         tt_limits := {| lim_min := 1; lim_max := None |};
         tt_elem_type := ELT_funcref
       |}];
    tc_memory := [::];
    tc_local := [::T_i32];
    tc_label := [::[::T_i32]];
    tc_return := Some [::T_i32]
  |} (F_instr 0) (Tf [::] [::T_i32]).
  Proof.
    type_go.
    Fail type_next_rewrite.
  Admitted. (*
    eapply bet_composition. instantiate (1:=[::T_i32]).
    type_next_rewrite.
    eapply bet_composition. instantiate (1:=[::T_i32;T_i32]).
    type_next_rewrite.
    eapply bet_composition. instantiate (1:=[::T_i32]).
    type_next_rewrite.
    eapply bet_composition. instantiate (1:=[::T_i32;T_i32]).
               all: type_go. *)


  Lemma factorial_module_typing :
    module_typing factorial_module (factorial_impts) [::].
  Proof. unfold module_typing.
    exists [::Tf [::T_i32] [::]; Tf [::T_i32] [::T_i32]; Tf [::T_i32] [::T_i32]; Tf [::] [::]],[:: (* {| tg_mut := MUT_mut ; tg_t := T_i32 |} *) ]. simpl.
    repeat split;eauto.
    { rewrite ! Forall2_cons. repeat split;auto; cbn;auto.
      { type_go. }
      { type_go.
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[::T_i32]).
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[::T_i32;T_i32]).
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[::T_i32]).
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[::T_i32;T_i32]).
        all: type_go. }
      { type_go.
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[::T_i32]).
        type_next_rewrite.
        eapply bet_composition. instantiate (1:=[::T_i32;T_i32]).
        type_go. rewrite <- (app_nil_r [::T_i32]).
        rewrite -(take_drop (1) [::T_i32;T_i32]);simpl take; simpl drop.
        eapply bet_weakening.
        type_go.
        weaken. }
      { type_go. }
    }
    { rewrite ! Forall2_cons. repeat split;auto; cbn;auto. }
  Qed.

  Definition factorial_module_instantiate :=
    [ ID_instantiate [] 0 [0%N;1%N] ].

  Notation "{{{ P }}} es {{{ v , Q }}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Lemma instantiate_factorial hidx gidx mod_tab n :
    (ssrnat.factorial (Wasm_int.nat_of_uint i32m n) < Wasm_int.Int32.modulus)%Z -> (* no overflow *)
    (0 <= (Wasm_int.Int32.intval n))%Z -> (* the parameter must be positive *)
    
    ⊢ {{{ (N.of_nat hidx) ↦[wf] (FC_func_host (Tf [T_i32; T_i32] []) (Mk_hostfuncidx mod_tab)) ∗
          (N.of_nat mod_tab) ↦[ha] HA_modify_table ∗
          (N.of_nat gidx) ↦[wg] {| g_mut := MUT_mut; g_val := VAL_int32 n |} ∗
          0%N ↪[mods] factorial_module ∗
          (∃ name, 0%N ↪[vis] {| modexp_name := name; modexp_desc := MED_func (Mk_funcidx hidx) |}) ∗
          (∃ name, 1%N ↪[vis] {| modexp_name := name; modexp_desc := MED_global (Mk_globalidx gidx) |}) ∗
          ↪[frame] empty_frame
      }}}
        ((factorial_module_instantiate,[]) : host_expr) 
      {{{ v, ⌜v = immHV []⌝ ∗ ∃ w, fact_val n (immV [w]) ∗ (N.of_nat gidx) ↦[wg] {| g_mut := MUT_mut; g_val := w |} }}} .
  Proof.
    iIntros (Hoverflow Hpos Φ). iModIntro. iIntros "(Hmod_tab & HA & Hglob & Hmod & Hvis1 & Hvis2 & Hf) HΦ".
    iDestruct "Hvis1" as (name1) "Hvis1".
    iDestruct "Hvis2" as (name2) "Hvis2".
    iApply (instantiation_spec_operational_start_seq with "[$Hf] [$Hmod Hvis1 Hvis2 Hmod_tab Hglob] [HΦ HA]") => //.
    { apply factorial_module_typing. }
    { unfold module_restrictions. cbn. repeat split;exists [];auto. }
    { cbn. instantiate (5:=[_;_]).
      instantiate (1:={[N.of_nat gidx := {| g_mut := MUT_mut; g_val := VAL_int32 n |} ]}).
      instantiate (1:=∅).
      instantiate (1:=∅).
      instantiate (1:= {[N.of_nat hidx := _ ]}).
      iSplitL "Hvis1 Hvis2";[|iSplit;[|auto]].
      simpl. iFrame. done.
      rewrite /instantiation_resources_pre_wasm /=.
      iSplitL;[|iPureIntro;split;apply Forall_nil;auto].
      iSplitL "Hmod_tab";[|iSplitR;[|iSplitR]].
      { rewrite /import_func_wasm_check /func_typecheck ! Forall2_cons /=.
        iSplit. iApply big_sepM_singleton. iFrame. iPureIntro.
        repeat split; auto. eexists _. rewrite lookup_singleton. eauto. set_solver. set_solver. }
      { iSplit. by iApply big_sepM_empty. iPureIntro.
        rewrite /tab_typecheck /tab_domcheck /factorial_impts ! Forall2_cons /=.
        repeat split; auto. }
      { iSplit. by iApply big_sepM_empty. iPureIntro.
        rewrite /mem_typecheck /mem_domcheck /factorial_impts ! Forall2_cons /=.
        repeat split; auto. }
      { rewrite /import_glob_wasm_check /glob_typecheck ! Forall2_cons /=.
        iSplit. iApply big_sepM_singleton. iFrame. iPureIntro.
        repeat split; auto. eexists _. rewrite lookup_singleton. eauto. set_solver. set_solver. }
    }

    iIntros (idnstart) "Hf [Hmod [[Hvis1 [Hvis2 _]] Hi]]".
    iDestruct "Hi" as (i) "[Hi _]".
    unfold instantiation_resources_post_wasm.
    iDestruct "Hi" as (g_inits tab_allocs mem_allocs glob_allocs wts' wms')
                        "(Hres & %Hpre & %Htaballocs & %Hwts' & %Hcheck1
                          & %Hmemalloc & %Hwms' & %Hcheck2 & %Hinit & %Hgloballocs & [Hfuncs [Htab [_ _]]])".
    simplify_eq. destruct i. cbn in *.
    destruct Hpre as [Htypes [Hprefuncs [_ [_ [Hpreglobs Hstart]]]]].
    repeat (destruct inst_funcs;[done|]).
    destruct inst_globs;[by inversion Hpreglobs|].
    apply b2p in Hstart.
    apply prefix_cons_inv_1 in Hprefuncs.
    apply prefix_cons_inv_1 in Hpreglobs.
    simplify_eq.
    iDestruct "Hfuncs" as "[Hmyrec [HF [Hfact [Hmain _]]]] /=".

    set (i:={| inst_types := [Tf [T_i32] [T_i32]; Tf [T_i32] []; Tf [T_i32; T_i32] []; Tf [] []];
               inst_funcs := [:: f, f0, f1, f2, idnstart & inst_funcs];
               inst_tab := inst_tab;
               inst_memory := inst_memory;
               inst_globs := g :: inst_globs
            |}).
    rewrite -/i.

    rewrite drop_0. iDestruct (big_sepL2_length with "Htab") as %Htablen. destruct inst_tab;[done|].
    iDestruct "Htab" as "[[[Ht _] _] _]".

    iDestruct "Hres" as "[[Hmodtab _] [_ [_ [Hglob _]]]]".
    rewrite /import_func_resources /import_glob_resources !big_sepM_singleton.

    iApply (main_host_spec with "[$] [$] [$] [$] [$] [$] [$] [$] [$]");eauto;unfold i;simpl;auto.
  Qed.
    
    
End FactorialHost.

