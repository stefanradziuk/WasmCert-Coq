(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "theories" "Wasm" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-top" "Wasm.type_checker_reflects_typing" "-native-compiler" "ondemand" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 2047 lines to 693 lines, then from 735 lines to 233 lines, then from 246 lines to 1505 lines, then from 1504 lines to 243 lines, then from 256 lines to 747 lines, then from 748 lines to 322 lines, then from 335 lines to 984 lines, then from 983 lines to 464 lines, then from 477 lines to 1371 lines, then from 1369 lines to 486 lines, then from 499 lines to 929 lines, then from 932 lines to 889 lines *)
(* coqc version 8.13.2 (March 2023) compiled on Mar 2 2023 16:53:07 with OCaml 4.14.0
   coqtop version 8.13.2 (March 2023)
   Expected coqc runtime on this file: 8.453 sec *)
Require Coq.Arith.Le.
Require Coq.NArith.BinNat.
Require Coq.Program.Equality.
Require Coq.ZArith.BinInt.
Require Coq.ZArith.Int.
Require Coq.micromega.Lia.
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
Require Wasm.pickability.
Require Wasm.common.
Require Wasm.bytes.
Require Wasm.numerics.
Require Wasm.memory.
Require Wasm.memory_list.
Require Wasm.datatypes.

Declare ML Module "ltac_plugin".
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False : Prop := .
End LocalFalse.
Axiom proof_admitted : False.
Global Set Default Proof Mode "Classic".
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.

Module Export Wasm_DOT_datatypes_properties_WRAPPED.
Module Export datatypes_properties.
Import Wasm.bytes.
Import Wasm.common.
Export Wasm.datatypes.
Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.ssrfun.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Canonical Structure immediate_eqType :=
  Eval hnf in EqType immediate nat_eqMixin.
Canonical Structure funcaddr_eqType :=
  Eval hnf in EqType funcaddr nat_eqMixin.
Canonical Structure tableaddr_eqType :=
  Eval hnf in EqType tableaddr nat_eqMixin.
Canonical Structure memaddr_eqType :=
  Eval hnf in EqType memaddr nat_eqMixin.
Canonical Structure globaladdr_eqType :=
  Eval hnf in EqType globaladdr nat_eqMixin.

Definition ascii_eq_dec : forall tf1 tf2 : Ascii.ascii,
  {tf1 = tf2} + {tf1 <> tf2}.
Admitted.

Definition ascii_eqb v1 v2 : bool := ascii_eq_dec v1 v2.
Definition eqasciiP : Equality.axiom ascii_eqb :=
  eq_dec_Equality_axiom ascii_eq_dec.

Canonical Structure ascii_eqMixin := EqMixin eqasciiP.
Canonical Structure ascii_eqType :=
  Eval hnf in EqType Ascii.ascii ascii_eqMixin.

Definition byte_eqb v1 v2 : bool := Byte.byte_eq_dec v1 v2.
Definition eqbyteP : Equality.axiom byte_eqb :=
  eq_dec_Equality_axiom Byte.byte_eq_dec.

Canonical Structure byte_eqMixin := EqMixin eqbyteP.
Canonical Structure byte_eqType :=
  Eval hnf in EqType Byte.byte byte_eqMixin.

Scheme Equality for value_type.
Definition value_type_eqb v1 v2 : bool := value_type_eq_dec v1 v2.
Definition eqvalue_typeP : Equality.axiom value_type_eqb :=
  eq_dec_Equality_axiom value_type_eq_dec.

Canonical Structure value_type_eqMixin := EqMixin eqvalue_typeP.
Canonical Structure value_type_eqType := Eval hnf in EqType value_type value_type_eqMixin.

Scheme Equality for packed_type.
Definition packed_type_eqb v1 v2 : bool := packed_type_eq_dec v1 v2.
Definition eqpacked_typeP : Equality.axiom packed_type_eqb :=
  eq_dec_Equality_axiom packed_type_eq_dec.

Canonical Structure packed_type_eqMixin := EqMixin eqpacked_typeP.
Canonical Structure packed_type_eqType := Eval hnf in EqType packed_type packed_type_eqMixin.

Scheme Equality for mutability.
Definition mutability_eqb v1 v2 : bool := mutability_eq_dec v1 v2.
Definition eqmutabilityP : Equality.axiom mutability_eqb :=
  eq_dec_Equality_axiom mutability_eq_dec.

Canonical Structure mutability_eqMixin := EqMixin eqmutabilityP.
Canonical Structure mutability_eqType := Eval hnf in EqType mutability mutability_eqMixin.

Scheme Equality for global_type.
Definition global_type_eqb v1 v2 : bool := global_type_eq_dec v1 v2.
Definition eqglobal_typeP : Equality.axiom global_type_eqb :=
  eq_dec_Equality_axiom global_type_eq_dec.

Canonical Structure global_type_eqMixin := EqMixin eqglobal_typeP.
Canonical Structure global_type_eqType := Eval hnf in EqType global_type global_type_eqMixin.

Definition function_type_eq_dec : forall tf1 tf2 : function_type,
  {tf1 = tf2} + {tf1 <> tf2}.
Admitted.

Definition function_type_eqb v1 v2 : bool := function_type_eq_dec v1 v2.
Definition eqfunction_typeP : Equality.axiom function_type_eqb :=
  eq_dec_Equality_axiom function_type_eq_dec.

Canonical Structure function_type_eqMixin := EqMixin eqfunction_typeP.
Canonical Structure function_type_eqType :=
  Eval hnf in EqType function_type function_type_eqMixin.

Definition t_context_eq_dec : forall x y : t_context, {x = y} + {x <> y}.
Admitted.

Definition t_context_eqb v1 v2 : bool := t_context_eq_dec v1 v2.
Definition eqt_contextP : Equality.axiom t_context_eqb :=
  eq_dec_Equality_axiom t_context_eq_dec.

Canonical Structure t_context_eqMixin := EqMixin eqt_contextP.
Canonical Structure t_context_eqType := Eval hnf in EqType t_context t_context_eqMixin.

Scheme Equality for sx.
Definition sx_eqb v1 v2 : bool := sx_eq_dec v1 v2.
Definition eqsxP : Equality.axiom sx_eqb :=
  eq_dec_Equality_axiom sx_eq_dec.

Canonical Structure sx_eqMixin := EqMixin eqsxP.
Canonical Structure sx_eqType := Eval hnf in EqType sx sx_eqMixin.

Scheme Equality for unop_i.
Definition unop_i_eqb v1 v2 : bool := unop_i_eq_dec v1 v2.
Definition equnop_iP : Equality.axiom unop_i_eqb :=
  eq_dec_Equality_axiom unop_i_eq_dec.

Canonical Structure unop_i_eqMixin := EqMixin equnop_iP.
Canonical Structure unop_i_eqType := Eval hnf in EqType unop_i unop_i_eqMixin.

Scheme Equality for unop_f.
Definition unop_f_eqb v1 v2 : bool := unop_f_eq_dec v1 v2.
Definition equnop_fP : Equality.axiom unop_f_eqb :=
  eq_dec_Equality_axiom unop_f_eq_dec.

Canonical Structure unop_f_eqMixin := EqMixin equnop_fP.
Canonical Structure unop_f_eqType := Eval hnf in EqType unop_f unop_f_eqMixin.

Scheme Equality for binop_i.
Definition binop_i_eqb v1 v2 : bool := binop_i_eq_dec v1 v2.
Definition eqbinop_iP : Equality.axiom binop_i_eqb :=
  eq_dec_Equality_axiom binop_i_eq_dec.

Canonical Structure binop_i_eqMixin := EqMixin eqbinop_iP.
Canonical Structure binop_i_eqType := Eval hnf in EqType binop_i binop_i_eqMixin.

Scheme Equality for binop_f.
Definition binop_f_eqb v1 v2 : bool := binop_f_eq_dec v1 v2.
Definition eqbinop_fP : Equality.axiom binop_f_eqb :=
  eq_dec_Equality_axiom binop_f_eq_dec.

Canonical Structure binop_f_eqMixin := EqMixin eqbinop_fP.
Canonical Structure binop_f_eqType := Eval hnf in EqType binop_f binop_f_eqMixin.

Scheme Equality for testop.
Definition testop_eqb v1 v2 : bool := testop_eq_dec v1 v2.
Definition eqtestopP : Equality.axiom testop_eqb :=
  eq_dec_Equality_axiom testop_eq_dec.

Canonical Structure testop_eqMixin := EqMixin eqtestopP.
Canonical Structure testop_eqType := Eval hnf in EqType testop testop_eqMixin.

Scheme Equality for relop_i.
Definition relop_i_eqb v1 v2 : bool := relop_i_eq_dec v1 v2.
Definition eqrelop_iP : Equality.axiom relop_i_eqb :=
  eq_dec_Equality_axiom relop_i_eq_dec.

Canonical Structure relop_i_eqMixin := EqMixin eqrelop_iP.
Canonical Structure relop_i_eqType := Eval hnf in EqType relop_i relop_i_eqMixin.

Scheme Equality for relop_f.
Definition relop_f_eqb v1 v2 : bool := relop_f_eq_dec v1 v2.
Definition eqrelop_fP : Equality.axiom relop_f_eqb :=
  eq_dec_Equality_axiom relop_f_eq_dec.

Canonical Structure relop_f_eqMixin := EqMixin eqrelop_fP.
Canonical Structure relop_f_eqType := Eval hnf in EqType relop_f relop_f_eqMixin.

Scheme Equality for cvtop.
Definition cvtop_eqb v1 v2 : bool := cvtop_eq_dec v1 v2.
Definition eqcvtopP : Equality.axiom cvtop_eqb :=
  eq_dec_Equality_axiom cvtop_eq_dec.

Canonical Structure cvtop_eqMixin := EqMixin eqcvtopP.
Canonical Structure cvtop_eqType := Eval hnf in EqType cvtop cvtop_eqMixin.

Definition value_eq_dec : forall v1 v2 : value, {v1 = v2} + {v1 <> v2}.
Admitted.

Definition value_eqb v1 v2 : bool := value_eq_dec v1 v2.
Definition eqvalueP : Equality.axiom value_eqb :=
  eq_dec_Equality_axiom value_eq_dec.

Canonical Structure value_eqMixin := EqMixin eqvalueP.
Canonical Structure value_eqType := Eval hnf in EqType value value_eqMixin.

 
Definition basic_instruction_rect' :=
  ltac:(rect'_build basic_instruction_rect).

Definition basic_instruction_eq_dec : forall e1 e2 : basic_instruction,
  {e1 = e2} + {e1 <> e2}.
Admitted.

Definition basic_instruction_eqb cl1 cl2 : bool :=
  basic_instruction_eq_dec cl1 cl2.
Definition eqbasic_instructionP : Equality.axiom basic_instruction_eqb :=
  eq_dec_Equality_axiom basic_instruction_eq_dec.

Canonical Structure basic_instruction_eqMixin := EqMixin eqbasic_instructionP.
Canonical Structure basic_instruction_eqType :=
  Eval hnf in EqType basic_instruction basic_instruction_eqMixin.

Definition instance_eq_dec : forall (i1 i2 : instance), {i1 = i2} + {i1 <> i2}.
Admitted.

Definition instance_eqb i1 i2 : bool := instance_eq_dec i1 i2.

Definition eqinstanceP : Equality.axiom instance_eqb :=
  eq_dec_Equality_axiom instance_eq_dec.

Canonical Structure instance_eqMixin := EqMixin eqinstanceP.
Canonical Structure instance_eqType := Eval hnf in EqType instance instance_eqMixin.

Section Host.

Variable host_function : eqType.

Let function_closure := function_closure host_function.
Let store_record := store_record host_function.
 

Let administrative_instruction_rect :=
  @administrative_instruction_rect  
  : forall (P : administrative_instruction -> Type), _.

Definition function_closure_eq_dec : forall (cl1 cl2 : function_closure),
  {cl1 = cl2} + {cl1 <> cl2}.
Admitted.

Definition function_closure_eqb cl1 cl2 : bool := function_closure_eq_dec cl1 cl2.
Definition eqfunction_closureP : Equality.axiom function_closure_eqb :=
  eq_dec_Equality_axiom function_closure_eq_dec.

Canonical Structure function_closure_eqMixin := EqMixin eqfunction_closureP.
Canonical Structure function_closure_eqType :=
  Eval hnf in EqType function_closure function_closure_eqMixin.

Definition tableinst_eq_dec : forall v1 v2 : tableinst, {v1 = v2} + {v1 <> v2}.
Admitted.

Definition tableinst_eqb v1 v2 : bool := tableinst_eq_dec v1 v2.
Definition eqtableinstP : Equality.axiom tableinst_eqb. exact (eq_dec_Equality_axiom tableinst_eq_dec). Defined.

Canonical Structure tableinst_eqMixin := EqMixin eqtableinstP.
Canonical Structure tableinst_eqType := Eval hnf in EqType tableinst tableinst_eqMixin.

Definition global_eq_dec : forall v1 v2 : global, {v1 = v2} + {v1 <> v2}.
Admitted.

Definition global_eqb v1 v2 : bool := global_eq_dec v1 v2.
Definition eqglobalP : Equality.axiom global_eqb. exact (eq_dec_Equality_axiom global_eq_dec). Defined.

Canonical Structure global_eqMixin := EqMixin eqglobalP.
Canonical Structure global_eqType := Eval hnf in EqType global global_eqMixin.

Definition store_record_eq_dec : forall v1 v2 : store_record, {v1 = v2} + {v1 <> v2}.
Admitted.

Definition store_record_eqb v1 v2 : bool := store_record_eq_dec v1 v2.
Definition eqstore_recordP : Equality.axiom store_record_eqb. exact (eq_dec_Equality_axiom store_record_eq_dec). Defined.

Canonical Structure store_record_eqMixin := EqMixin eqstore_recordP.
Canonical Structure store_record_eqType := Eval hnf in EqType store_record store_record_eqMixin.

Definition frame_eq_dec : forall v1 v2 : frame, {v1 = v2} + {v1 <> v2}.
Admitted.

Definition frame_eqb v1 v2 : bool := frame_eq_dec v1 v2.
Definition eqframeP : Equality.axiom frame_eqb. exact (eq_dec_Equality_axiom frame_eq_dec). Defined.

Canonical Structure frame_eqMixin := EqMixin eqframeP.
Canonical Structure frame_eqType := Eval hnf in EqType frame frame_eqMixin.

Definition module_export_desc_eq_dec : forall v1 v2 : module_export_desc, {v1 = v2} + {v1 <> v2}.
Admitted.

Definition module_export_desc_eqb v1 v2 : bool := module_export_desc_eq_dec v1 v2.
Definition eqmodule_export_descP : Equality.axiom module_export_desc_eqb. exact (eq_dec_Equality_axiom module_export_desc_eq_dec). Defined.

Canonical Structure module_export_desc_eqMixin := EqMixin eqmodule_export_descP.
Canonical Structure module_export_desc_eqType :=
  Eval hnf in EqType module_export_desc module_export_desc_eqMixin.

Definition module_export_eq_dec : forall v1 v2 : module_export, {v1 = v2} + {v1 <> v2}.
Admitted.

Definition module_export_eqb v1 v2 : bool := module_export_eq_dec v1 v2.
Definition eqmodule_exportP : Equality.axiom module_export_eqb. exact (eq_dec_Equality_axiom module_export_eq_dec). Defined.

Canonical Structure module_export_eqMixin := EqMixin eqmodule_exportP.
Canonical Structure module_export_eqType := Eval hnf in EqType module_export module_export_eqMixin.

 
Definition administrative_instruction_rect' :=
  ltac:(rect'_build administrative_instruction_rect).

Definition administrative_instruction_eq_dec : forall e1 e2 : administrative_instruction,
  {e1 = e2} + {e1 <> e2}.
Admitted.

Definition administrative_instruction_eqb cl1 cl2 : bool :=
  administrative_instruction_eq_dec cl1 cl2.
Definition eqadministrative_instructionP : Equality.axiom administrative_instruction_eqb. exact (eq_dec_Equality_axiom administrative_instruction_eq_dec). Defined.

Canonical Structure administrative_instruction_eqMixin := EqMixin eqadministrative_instructionP.
Canonical Structure administrative_instruction_eqType :=
  Eval hnf in EqType administrative_instruction administrative_instruction_eqMixin.

Definition lholed_eq_dec : forall v1 v2 : lholed, {v1 = v2} + {v1 <> v2}.
Admitted.

Definition lholed_eqb v1 v2 : bool := lholed_eq_dec v1 v2.
Definition eqlholedP : Equality.axiom lholed_eqb. exact (eq_dec_Equality_axiom lholed_eq_dec). Defined.

Canonical Structure lholed_eqMixin := EqMixin eqlholedP.
Canonical Structure lholed_eqType := Eval hnf in EqType lholed lholed_eqMixin.

Definition limits_eq_dec : forall v1 v2 : limits, {v1 = v2} + {v1 <> v2}.
Admitted.
Definition limits_eqb v1 v2 : bool := limits_eq_dec v1 v2.
Definition eqlimitsP : Equality.axiom limits_eqb. exact (eq_dec_Equality_axiom limits_eq_dec). Defined.

Canonical Structure limits_eqMixin := EqMixin eqlimitsP.
Canonical Structure limits_eqType := Eval hnf in EqType limits limits_eqMixin.

Definition table_type_eq_dec : forall v1 v2 : table_type, {v1 = v2} + {v1 <> v2}.
Admitted.
Definition table_type_eqb v1 v2 : bool := table_type_eq_dec v1 v2.
Definition eqtable_typeP : Equality.axiom table_type_eqb. exact (eq_dec_Equality_axiom table_type_eq_dec). Defined.

Canonical Structure table_type_eqMixin := EqMixin eqtable_typeP.
Canonical Structure table_type_eqType := Eval hnf in EqType table_type table_type_eqMixin.

Definition memory_type_eq_dec : forall v1 v2 : memory_type, {v1 = v2} + {v1 <> v2}.
Admitted.
Definition memory_type_eqb v1 v2 : bool := memory_type_eq_dec v1 v2.
Definition eqmemory_typeP : Equality.axiom memory_type_eqb. exact (eq_dec_Equality_axiom memory_type_eq_dec). Defined.

Canonical Structure memory_type_eqMixin := EqMixin eqmemory_typeP.
Canonical Structure memory_type_eqType := Eval hnf in EqType memory_type memory_type_eqMixin.

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb. exact (eq_dec_Equality_axiom res_crash_eq_dec). Defined.

Canonical Structure res_crash_eqMixin := EqMixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in EqType res_crash res_crash_eqMixin.

Definition res_step_eq_dec : forall r1 r2 : res_step, {r1 = r2} + {r1 <> r2}.
Admitted.
Definition res_step_eqb (r1 r2 : res_step) : bool. exact (res_step_eq_dec r1 r2). Defined.
Definition eqres_stepP : Equality.axiom res_step_eqb. exact (eq_dec_Equality_axiom res_step_eq_dec). Defined.

Canonical Structure res_step_eqMixin := EqMixin eqres_stepP.
Canonical Structure res_step_eqType := Eval hnf in EqType res_step res_step_eqMixin.

End Host.

End datatypes_properties.

End Wasm_DOT_datatypes_properties_WRAPPED.
Module Export Wasm_DOT_datatypes_properties.
Module Export Wasm.
Module Export datatypes_properties.
Include Wasm_DOT_datatypes_properties_WRAPPED.datatypes_properties.
End datatypes_properties.

End Wasm.

End Wasm_DOT_datatypes_properties.
Import mathcomp.ssreflect.ssrnat.
Import mathcomp.ssreflect.ssrbool.
Import mathcomp.ssreflect.eqtype.
Import mathcomp.ssreflect.seq.
Export Wasm.datatypes_properties.

Set Implicit Arguments.

Section Host.
Definition typeof (v : value) : value_type.
Admitted.
Definition option_projl (A B : Type) (x : option (A * B)) : option A.
Admitted.
Definition t_length (t : value_type) : nat.
Admitted.
Definition is_int_t (t : value_type) : bool.
Admitted.
Definition is_float_t (t : value_type) : bool.
Admitted.
Definition is_mut (tg : global_type) : bool.
Admitted.
Definition es_is_trap (es : seq administrative_instruction) : bool.
Admitted.
Definition load_store_t_bounds (a : alignment_exponent) (tp : option packed_type) (t : value_type) : bool.
Admitted.

End Host.

Section Host.

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

End Host.

Import Wasm.common.

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

