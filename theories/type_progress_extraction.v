From mathcomp Require Import ssreflect eqtype seq.
From Coq Require Import Program.Equality ZArith_base Extraction.
From Wasm Require Export type_progress type_preservation type_checker type_checker_reflects_typing.


Module ProgressExtract.

Variable host_function : eqType.
Let host := host host_function.
Variable host_instance : host.
Let host_state := host_state host_instance.

Definition t_progress := t_progress.
Definition interpret_one_step := interpret_one_step.
Definition interpret_multi_step := interpret_multi_step.

Definition t_preservation := t_preservation.

Definition i32_of_Z (z: Z) := VAL_int32 (Wasm_int.int_of_Z i32m z).

Definition add_236_bis : seq basic_instruction := [::
  BI_const (i32_of_Z (2)%Z);
  BI_const (i32_of_Z (3)%Z);
  BI_const (i32_of_Z (6)%Z);
  BI_binop T_i32 (Binop_i BOI_add);
  BI_binop T_i32 (Binop_i BOI_add)
  ].

Definition add_236 : seq administrative_instruction := map AI_basic add_236_bis.

Let store_record := store_record host_function.

Let emp_store_record : store_record := {|
  s_funcs   := [::];
  s_tables  := [::];
  s_mems    := [::];
  s_globals := [::];
|}.

Let emp_instance : instance := {|
  inst_types  := [::];
  inst_funcs  := [::];
  inst_tab    := [::];
  inst_memory := [::];
  inst_globs  := [::];
|}.

Let emp_frame : frame := {|
  f_locs := [::];
  f_inst := emp_instance;
|}.

Let emp_context : t_context := {|
  tc_types_t := [::];
  tc_func_t  := [::];
  tc_global  := [::];
  tc_table   := [::];
  tc_memory  := [::];
  tc_local   := [::];
  tc_label   := [::];
  tc_return  := None;
|}.

Theorem H_be_typing_add_236 : be_typing emp_context add_236_bis (Tf [::] [:: T_i32]).
Proof. apply typing_if_type_checker => /=. reflexivity. Qed.

Theorem H_config_typing_add_236 : config_typing emp_store_record emp_frame add_236 [:: T_i32].
Proof.
  apply mk_config_typing.
  - repeat split; auto. apply TProp.Forall_nil.
  - apply mk_s_typing with (C := emp_context) (C0 := emp_context); auto.
    apply mk_frame_typing with (i := emp_instance) (C := emp_context); auto.
  - apply ety_a with (bes := add_236_bis).
    apply H_be_typing_add_236.
Defined.

Definition ts_add_236 := [:: T_i32].

Definition fuel_100 : nat := 100.

End ProgressExtract.

Extraction Language OCaml.
Recursive Extraction ProgressExtract DummyHost.

(*
 * Depending on the GHC version, the extracted code may have to be patched.
 * The Coq-extracted code tries to find unsafeCoerce# in GHC.Base, this has to
 * be changed to GHC.Exts (and `import qualified GHC.Exts` added).
 *
 * This is how to single-step reduce add_2_7 in haskell:
 * λ :f add_2_7
 * add_2_7 = Cons
 *             (AI_basic (BI_const (VAL_int32 (Zpos (XO XH)))))
 *             (Cons
 *                (AI_basic (BI_const (VAL_int32 (Zpos (XI (XI XH))))))
 *                (Cons (AI_basic (BI_binop T_i32 (Binop_i0 BOI_add))) Nil))
 * λ add_2_7' = interpret_one_step host_function host_instance emp_store_record emp_frame add_2_7 ts_add_2_7 (unsafeCoerce Tt) h_config_typing_add_2_7
 * λ :f add_2_7'
 * add_2_7' = Cons
 *              (AI_basic (BI_const (VAL_int32 (Zpos (XI (XO (XO XH))))))) Nil
 *
 * NOTE the use of (unsafeCoerce Tt) for hs.
 * It's probably fine as it's expecting a singleton there (is it?) but might
 * break if progress tries to inspect hs.
 * `undefined` also works but you have to be careful not to attempt printing it
 * when examining intermediate steps.
 *)

