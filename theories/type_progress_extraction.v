From mathcomp Require Import eqtype seq.
From Coq Require Import Program.Equality ZArith_base Extraction.
From Wasm Require Export type_progress type_preservation
  type_checker type_checker_reflects_typing.


Module ProgressExtract.

Let host_eqType := unit_eqType.

Definition host : Type := host unit_eqType.

Definition host_instance : host.
Proof.
  refine {|
    host_state := unit_eqType ;
    host_application _ _ _ _ _ _ _ := False
  |}; intros; exfalso; auto.
Defined.

Let store_record := store_record host_eqType.
Let config_typing := @config_typing host_eqType.

Definition t_progress := @t_progress host_eqType host_instance.
Definition interpret_one_step := @interpret_one_step host_eqType host_instance.
Definition interpret_multi_step := @interpret_multi_step host_eqType host_instance.

Definition t_preservation := t_preservation.

Definition i32_of_Z (z: Z) := VAL_int32 (Wasm_int.int_of_Z i32m z).

(*  (func $fibi (param $n i32) (result i32)
 *    (local $i i32)
 *    (local $x i32)
 *    (local $y i32)
 *    (local $tmp i32)
 *    (local.set $i (i32.const 0))
 *    (local.set $x (i32.const 0))
 *    (local.set $y (i32.const 1))
 *    (; i is a loop counter ;)
 *    (; x is 0th, y is 1st fib num ;)
 *
 *    (if (i32.eq (local.get $n) (i32.const 0))
 *     (then (return (i32.const 0)))
 *    )
 *
 *    (loop $loop
 *      (local.set $i (i32.add (local.get $i) (i32.const 1)))
 *      (local.set $tmp (i32.add (local.get $x) (local.get $y)))
 *      (local.set $x (local.get $y))
 *      (local.set $y (local.get $tmp))
 *
 *      (; if $i is less than $n loop again ;)
 *      (br_if $loop (i32.lt_s (local.get $i) (local.get $n)))
 *    )
 *
 *    (local.get $x)
 *  )
 * locals:
 *   $n: 0
 *   $i: 1
 *   $x: 2
 *   $y: 3
 * $tmp: 4
 *)

Definition loop_body : seq basic_instruction := [::
  (* i += 1 *)
  BI_get_local 1;
  BI_const (i32_of_Z 1);
  BI_binop T_i32 (Binop_i BOI_add);
  BI_set_local 1;

  (* tmp = x + y *)
  BI_get_local 2;
  BI_get_local 3;
  BI_binop T_i32 (Binop_i BOI_add);
  BI_set_local 4;

  (* x = y *)
  BI_get_local 3;
  BI_set_local 2;

  (* y = tmp *)
  BI_get_local 4;
  BI_set_local 3;

  (* i < n *)
  BI_get_local 1;
  BI_get_local 0;
  BI_relop T_i32 (Relop_i (ROI_lt SX_S));
  BI_br_if 0
].

Definition fib_bis : seq basic_instruction := [::
  (* n = 10 *)
  BI_const (i32_of_Z 10);
  BI_set_local 0;

  (* i = 0 *)
  BI_const (i32_of_Z 0);
  BI_set_local 1;

  (* x = 0 *)
  BI_const (i32_of_Z 0);
  BI_set_local 2;

  (* y = 1 *)
  BI_const (i32_of_Z 1);
  BI_set_local 3;

  (* n == 0 *)
  BI_get_local 0;
  BI_testop T_i32 TO_eqz;
  (* (if (i32.eq (local.get $n) (i32.const 0)) *)
  BI_if
    (Tf [::] [::T_i32])
    (* then *)
    [:: BI_const (i32_of_Z 0)]
    (* else *)
    [:: BI_loop (Tf [::] [::]) loop_body; BI_get_local 2]
].

Definition fib : seq administrative_instruction := map AI_basic fib_bis.

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

Let loc_frame : frame := {|
  f_locs := [::i32_of_Z 0; i32_of_Z 0; i32_of_Z 0; i32_of_Z 0; i32_of_Z 0];
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

Let loc_ts := [::T_i32; T_i32; T_i32; T_i32; T_i32].

Let loc_context : t_context := upd_local emp_context loc_ts.

Compute (b_e_type_checker loc_context fib_bis (Tf [::] [::T_i32])).

Theorem H_be_typing_fib : be_typing loc_context fib_bis (Tf [::] [:: T_i32]).
Proof.
  remember (b_e_type_checker_reflects_typing
    loc_context fib_bis (Tf [::] [:: T_i32])) as H.
  compute in H.
  inversion H.
  assumption.
Qed.

Theorem H_config_typing_fib : config_typing emp_store_record loc_frame fib [:: T_i32].
Proof.
  apply mk_config_typing.
  - repeat split; auto. apply TProp.Forall_nil.
  - apply mk_s_typing with (C := loc_context) (C0 := loc_context); auto.
    apply mk_frame_typing with (i := emp_instance) (C := emp_context); auto.
  - apply ety_a with (bes := fib_bis).
    apply H_be_typing_fib.
Defined.

Definition ts_fib := [:: T_i32].

Definition fuel_100 : nat := 100.

End ProgressExtract.

Extraction Language OCaml.

Extraction "progress_extracted" ProgressExtract DummyHost.

(*
   # ProgressExtract.interpret_multi_step ProgressExtract.fuel_100 ProgressExtract.emp_store_record ProgressExtract.emp_frame ProgressExtract.add_236 ProgressExtract.ts_add_236 (Obj.magic ProgressExtract.host_eqType) ProgressExtract.coq_H_config_typing_add_236;;
 *)

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

