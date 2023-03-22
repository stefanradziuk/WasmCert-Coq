(* -*- mode: coq; coq-prog-args: ("-emacs" "-R" "theories" "Wasm" "-w" "-deprecated-native-compiler-option,-native-compiler-disabled" "-top" "Wasm.type_progress_extraction" "-native-compiler" "ondemand") -*- *)
(* File reduced by coq-bug-minimizer from original input, then from 125 lines to 36 lines, then from 41 lines to 37 lines *)
(* coqc version 8.13.2 (March 2023) compiled on Mar 2 2023 16:53:07 with OCaml 4.14.0
   coqtop version 8.13.2 (March 2023)
   Expected coqc runtime on this file: 10.577 sec *)
Require Wasm.type_progress.
Require Wasm.type_checker_reflects_typing.

Import mathcomp.ssreflect.ssreflect.
Import mathcomp.ssreflect.seq.
Import Coq.ZArith.ZArith_base.
Export Wasm.type_progress.
Export Wasm.type_checker_reflects_typing.

Module Export ProgressExtract.

Definition i32_of_Z (z: Z) := VAL_int32 (Wasm_int.int_of_Z i32m z).
Definition add_236_bis : seq basic_instruction.
exact ([::
  BI_const (i32_of_Z (2)%Z);
  BI_const (i32_of_Z (3)%Z);
  BI_const (i32_of_Z (6)%Z);
  BI_binop T_i32 (Binop_i BOI_add);
  BI_binop T_i32 (Binop_i BOI_add)
  ]).
Defined.
Let emp_context : t_context.
Admitted.

Theorem H_be_typing_add_236 : be_typing emp_context add_236_bis (Tf [::] [:: T_i32]).
Proof.
apply typing_if_type_checker => /=.
reflexivity.
Qed.

End ProgressExtract.

Extraction Language Haskell.

Timeout 10 Extraction "progress_extracted" ProgressExtract DummyHost.

