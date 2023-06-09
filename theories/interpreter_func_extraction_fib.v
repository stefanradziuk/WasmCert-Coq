From mathcomp Require Import eqtype seq.
From Coq Require Import Program.Equality ZArith_base Extraction.
From Wasm Require Export interpreter_func pp.

Module Extr.

Let host_eqType := unit_eqType.

Definition host : Type := host unit_eqType.

Definition host_instance : host.
Proof.
  refine {|
    host_state := unit_eqType ;
    host_application _ _ _ _ _ _ _ := False
  |}; intros; exfalso; auto.
Defined.

Let store_record := store_record EmptyHost.host_function_eqType.
Let host_state := host_state EmptyHost.host_instance.
Let res_tuple := res_tuple EmptyHost.host_instance.

Definition run_step_with_measure := @run_step_with_measure _ _ _ Interpreter_func.host_application_impl_correct tt.
Definition run_v := @run_v _ _ _ Interpreter_func.host_application_impl_correct tt.
Check run_v.

Definition pp_res_val (r : host_state * store_record * res) :=
  match r with
  | (_, _, R_value [:: v]) => pp_value v
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

Let n : Z := 20000.

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

Let loc_frame : frame := {|
  f_locs := [::i64_of_Z 0; i64_of_Z 0; i64_of_Z 0; i64_of_Z 0; i64_of_Z 0];
  f_inst := emp_instance;
|}.

(* TODO use Z for fuel *)
Definition fuel_fib : nat := Z.to_nat (Z.mul (Z.add n 1) 20).

End Extr.

(* Check (Extr.run_v Extr.emp_store_record Extr.loc_frame Extr.fib Extr.fuel_fib). *)

From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString.

Extraction Language OCaml.

Extraction "cert_extr" Extr DummyHost.

