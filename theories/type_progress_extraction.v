From mathcomp Require Import eqtype seq.
From Coq Require Import Program.Equality ZArith_base Extraction.
From Wasm Require Export type_progress type_preservation
  type_checker type_checker_reflects_typing pp.


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
Definition interpret_multi_step_pf := @interpret_multi_step_pf host_eqType host_instance.

Definition t_preservation := t_preservation.

Definition pp_head_val (es : list administrative_instruction) :=
  match es with
  | [:: AI_basic (BI_const v)] => pp_value v
  | _ => String.EmptyString
  end.

Definition i64_of_Z (z: Z) := VAL_int64 (Wasm_int.int_of_Z i64m z).

(*  (func $fibi (param $n i64) (result i64)
 *    (local $i i64)
 *    (local $x i64)
 *    (local $y i64)
 *    (local $tmp i64)
 *    (local.set $i (i64.const 0))
 *    (local.set $x (i64.const 0))
 *    (local.set $y (i64.const 1))
 *    (; i is a loop counter ;)
 *    (; x is 0th, y is 1st fib num ;)
 *
 *    (if (i64.eq (local.get $n) (i64.const 0))
 *     (then (return (i64.const 0)))
 *    )
 *
 *    (loop $loop
 *      (local.set $i (i64.add (local.get $i) (i64.const 1)))
 *      (local.set $tmp (i64.add (local.get $x) (local.get $y)))
 *      (local.set $x (local.get $y))
 *      (local.set $y (local.get $tmp))
 *
 *      (; if $i is less than $n loop again ;)
 *      (br_if $loop (i64.lt_s (local.get $i) (local.get $n)))
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

Let n : Z := 60.

Definition loop_body : seq basic_instruction := [::
  (* i += 1 *)
  BI_get_local 1;
  BI_const (i64_of_Z 1);
  BI_binop T_i64 (Binop_i BOI_add);
  BI_set_local 1;

  (* tmp = x + y *)
  BI_get_local 2;
  BI_get_local 3;
  BI_binop T_i64 (Binop_i BOI_add);
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
  BI_relop T_i64 (Relop_i (ROI_lt SX_S));
  BI_br_if 0
].

Definition fib_bis : seq basic_instruction := [::
  (* n = 10 *)
  BI_const (i64_of_Z n);
  BI_set_local 0;

  (* i = 0 *)
  BI_const (i64_of_Z 0);
  BI_set_local 1;

  (* x = 0 *)
  BI_const (i64_of_Z 0);
  BI_set_local 2;

  (* y = 1 *)
  BI_const (i64_of_Z 1);
  BI_set_local 3;

  (* n == 0 *)
  BI_get_local 0;
  BI_testop T_i64 TO_eqz;
  (* (if (i64.eq (local.get $n) (i64.const 0)) *)
  BI_if
    (Tf [::] [::T_i64])
    (* then *)
    [:: BI_const (i64_of_Z 0)]
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
  f_locs := [::i64_of_Z 0; i64_of_Z 0; i64_of_Z 0; i64_of_Z 0; i64_of_Z 0];
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

Let loc_ts := [::T_i64; T_i64; T_i64; T_i64; T_i64].

Let loc_context : t_context := upd_local emp_context loc_ts.

Compute (b_e_type_checker loc_context fib_bis (Tf [::] [::T_i64])).

Theorem H_be_typing_fib : be_typing loc_context fib_bis (Tf [::] [:: T_i64]).
Proof.
  remember (b_e_type_checker_reflects_typing
    loc_context fib_bis (Tf [::] [:: T_i64])) as H.
  compute in H.
  inversion H.
  assumption.
Qed.

Theorem H_config_typing_fib : config_typing emp_store_record loc_frame fib [:: T_i64].
Proof.
  apply mk_config_typing.
  - repeat split; auto. apply TProp.Forall_nil.
  - apply mk_s_typing with (C := loc_context) (C0 := loc_context); auto.
    apply mk_frame_typing with (i := emp_instance) (C := emp_context); auto.
  - apply ety_a with (bes := fib_bis).
    apply H_be_typing_fib.
Defined.

Definition ts_fib := [:: T_i64].

(* TODO use Z for fuel *)
Definition fuel_fib : nat := Z.to_nat (Z.mul (Z.add n 1) 20).

End ProgressExtract.

From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString.

Extraction Language OCaml.

Extraction "progress_extracted" ProgressExtract DummyHost.

(*
   # let e' = ProgressExtract.interpret_multi_step ProgressExtract.fuel_fib ProgressExtract.emp_store_record ProgressExtract.loc_frame ProgressExtract.fib ProgressExtract.ts_fib (Obj.magic ProgressExtract.host_eqType) ProgressExtract.coq_H_config_typing_fib;;
#   let cl2s cl = String.concat "" (List.map (String.make 1) cl);;
#   let ppstr = ProgressExtract.pp_head_val e' in " " ^ (cl2s ppstr);;
- : string = " i32.const -298632863\n"

   let itp_partially_applied = ProgressExtract.interpret_multi_step ProgressExtract.fuel_fib ProgressExtract.emp_store_record ProgressExtract.loc_frame ProgressExtract.fib ProgressExtract.ts_fib (Obj.magic ProgressExtract.host_eqType);;
val itp_partially_applied : config_typing -> administrative_instruction list =
  <fun>
#   let e' = time itp_partially_applied ProgressExtract.coq_H_config_typing_fib;;
execution time: 21.410549s
 *)

