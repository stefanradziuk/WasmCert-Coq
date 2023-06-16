From mathcomp Require Import eqtype seq ssrfun.
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
Let config_tuple := config_tuple EmptyHost.host_instance.

Definition run_step := @run_step _ _ Interpreter_func.host_application_impl.
Definition run_v := @run_v _ _ Interpreter_func.host_application_impl.

Definition run_v_wrap fuel depth s f es :=
  let cfg := (tt, s, f, es) in
  run_v fuel depth cfg.

Check run_v_wrap.

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

Definition loop_body (n : Z) : seq basic_instruction := [::
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

Definition fib_bis (n : Z) : seq basic_instruction := [::
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
    [:: BI_loop (Tf [::] [::]) (loop_body n); BI_get_local 2]
].

Definition fib (n : Z) : seq administrative_instruction := map AI_basic (fib_bis n).

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
Definition fuel_fib (n : Z) : nat := Z.to_nat (Z.mul (Z.add n 1) 20).

Definition depth : nat := 10.

Definition n_0 : Z := 0.
Definition n_10 : Z := 10.
Definition n_20 : Z := 20.
Definition n_30 : Z := 30.
Definition n_40 : Z := 40.
Definition n_50 : Z := 50.
Definition n_60 : Z := 60.
Definition n_100 : Z := 100.
Definition n_1000 : Z := 1000.
Definition n_2000 : Z := 2000.
Definition n_5000 : Z := 5000.
Definition n_10000 : Z := 10000.
Definition n_15000 : Z := 15000.
Definition n_20000 : Z := 20000.

End Extr.

(* Check (Extr.run_v Extr.emp_store_record Extr.loc_frame Extr.fib Extr.fuel_fib). *)

From Coq Require Import
  extraction.ExtrOcamlBasic
  extraction.ExtrOcamlString.

Extraction Language OCaml.

Extraction "itp_extr" Extr DummyHost.

