(* Wasm base definitions *)
(* (C) J. Pichon - see LICENSE.txt *)
(* in serious need of cleaning up
 * - proofs have not been ported
 * - lots of axioms
 * - no validation
 * - variable order in inductive definitions is pretty much random
 *)


From mathcomp
Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module Wasm_int.

Record mixin_of (int_t : Type) := Mixin {
  int_zero : int_t;
  int_clz : int_t -> int_t;
  int_ctz : int_t -> int_t;
  int_popcnt : int_t -> int_t;
  (**)
  int_add : int_t -> int_t -> int_t;
  int_sub : int_t -> int_t -> int_t;
  int_mul : int_t -> int_t -> int_t;
  int_div_u : int_t -> int_t -> option int_t;
  int_div_s : int_t -> int_t -> option int_t;
  int_rem_u : int_t -> int_t -> option int_t;
  int_rem_s : int_t -> int_t -> option int_t;
  int_and : int_t -> int_t -> int_t;
  int_or : int_t -> int_t -> int_t;
  int_xor : int_t -> int_t -> int_t;
  int_shl : int_t -> int_t -> int_t;
  int_shr_u : int_t -> int_t -> int_t;
  int_shr_s : int_t -> int_t -> int_t;
  int_rotl : int_t -> int_t -> int_t;
  int_rotr : int_t -> int_t -> int_t;
  (**)
  int_eqz : int_t -> bool;
  (**)
  int_eq : int_t -> int_t -> bool;
  int_lt_u : int_t -> int_t -> bool;
  int_lt_s : int_t -> int_t -> bool;
  int_gt_u : int_t -> int_t -> bool;
  int_gt_s : int_t -> int_t -> bool;
  int_le_u : int_t -> int_t -> bool;
  int_le_s : int_t -> int_t -> bool;
  int_ge_u : int_t -> int_t -> bool;
  int_ge_s : int_t -> int_t -> bool;
  (**)
  int_of_nat : nat -> int_t; (* TODO: ??? *)
  nat_of_int : int_t -> nat;
}.

Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >-> Equality.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.

Definition int_ne (e : type) : sort e -> sort e -> bool :=
  let 'Pack _ (Class _ (Mixin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ int_eq _ _ _ _ _ _ _ _ _ _)) := e in
    fun x => fun y => negb (int_eq x y).

End Wasm_int.




Module Wasm_float.

Record mixin_of (float_t : Type) := Mixin {
  float_zero : float_t;
  float_neg : float_t -> float_t;
  float_abs : float_t -> float_t;
  float_ceil : float_t -> float_t;
  float_floor : float_t -> float_t;
  float_trunc : float_t -> float_t;
  float_nearest : float_t -> float_t;
  float_sqrt : float_t -> float_t;
  float_add : float_t -> float_t -> float_t;
  float_sub : float_t -> float_t -> float_t;
  float_mul : float_t -> float_t -> float_t;
  float_div : float_t -> float_t -> float_t;
  float_min : float_t -> float_t -> float_t;
  float_max : float_t -> float_t -> float_t;
  float_copysign : float_t -> float_t -> float_t;
  float_eq : float_t -> float_t -> bool;
  float_lt : float_t -> float_t -> bool;
  float_gt : float_t -> float_t -> bool;
  float_le : float_t -> float_t -> bool;
  float_ge : float_t -> float_t -> bool;
                                      }.


Record class_of T := Class {base : Equality.class_of T; mixin : mixin_of T}.
Local Coercion base : class_of >->  Equality.class_of.

Structure type := Pack {sort; _ : class_of sort}.
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).
Definition class := let: Pack _ c as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c.
Let xT := let: Pack T _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack m :=
  fun b bT & phant_id (Equality.class bT) b => Pack (@Class T b m).

Definition eqType := @Equality.Pack cT xclass.

Definition float_ne (e : type) : sort e -> sort e -> bool :=
  let 'Pack _ (Class _ (Mixin _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ float_eq _ _ _ _)) := e in
    fun x => fun y => negb (float_eq x y).

End Wasm_float.


Variable host : eqType.
Variable host_state : eqType.

Definition immediate := nat. (* i *)

Definition static_offset := nat. (* off *)

Definition alignment_exponent := nat. (* a *)

Definition uint8 := nat. (* TODO *)

Definition byte := uint8.
Variable byte_eqb : byte -> byte -> bool.

(* TODO: lots of stuff *)

Definition bytes := list byte.

Fixpoint bytes_takefill (a : byte) (n : nat) (aas : bytes) : bytes :=
  match n with
  | O => nil
  | S n' =>
    match aas with
    | nil => cons a (bytes_takefill a n' aas)
    | cons a' aas' => cons a' (bytes_takefill a n' aas')
    end
  end.

Fixpoint bytes_replicate (n : nat) (b : byte) : bytes :=
  match n with
  | 0 => [::]
  | n'.+1 => b :: bytes_replicate n' b
  end.

Fixpoint last {A} (l : list A) : option A :=
  match l with
  | [::] => None
  | [::x] => Some x
  | _ :: l' => last l'
  end.

Definition msbyte (bs : bytes) : option byte :=
  last bs.

Definition mem := list byte.

Definition read_bytes (m : mem) (n : nat) (l : nat) : bytes :=
  List.firstn l (List.skipn n m).

Definition write_bytes (m : mem) (n : nat) (bs : bytes) : mem :=
  app (List.firstn n m) (app bs (List.skipn (n + length bs) m)).

Definition mem_append (m : mem) (bs : bytes) := app m bs.

Inductive value_type : Type := (* t *)
| T_i32
| T_i64
| T_f32
| T_f64.

Definition value_type_eqb (v1 v2 : value_type) :=
  match (v1, v2) with
  | (T_i32, T_i32) => true
  | (T_i64, T_i64) => true
  | (T_f32, T_f32) => true
  | (T_f64, T_f64) => true
  | _ => false
  end.

Lemma eqvalue_typeP : Equality.axiom value_type_eqb.
Proof.
move => v1 v2.
case: v1; case: v2;
try (apply ReflectT; done);
try (apply ReflectF; done).
Qed.

Canonical value_type_eqMixin := EqMixin eqvalue_typeP.
Canonical value_type_eqType := Eval hnf in EqType value_type value_type_eqMixin.

Inductive packed_type : Type := (* tp *)
| Tp_i8
| Tp_i16
| Tp_i32.

Inductive mutability : Type := (* mut *)
| T_immut
| T_mut.

Definition mutability_eqb (m1 m2 : mutability) : bool :=
  match (m1, m2) with
  | (T_immut, T_immut) => true
  | (T_mut, T_mut) => true
  | _ => false
  end.

Lemma eqmutabilityP : Equality.axiom mutability_eqb.
Proof.
  move => m1 m2.
  case: m1; case: m2; try (by apply ReflectT); try (by apply ReflectF; move => H; discriminate H).
Qed.
Canonical mutability_eqMixin := EqMixin eqmutabilityP.
Canonical mutability_eqType := Eval hnf in EqType mutability mutability_eqMixin.


Record global_type := (* tg *)
  { tg_mut : mutability; tg_t : value_type}.

Definition global_type_eqb (tg1 tg2 : global_type) : bool :=
  (tg_mut tg1 == tg_mut tg2)
    && (tg_t tg1 == tg_t tg2).

Lemma eqglobal_typeP : Equality.axiom global_type_eqb.
Proof.
  move => g1 g2.
  case: g1 => m1 t1; case g2 => m2 t2.
  case_eq (m1 == m2) => [Hm|Hm].
  {
    case_eq (t1 == t2) => [Ht|Ht].
    {
      rewrite /global_type_eqb /=.
      rewrite Hm Ht.
      apply ReflectT.
      move/eqP: Hm => Hm.
      move/eqP: Ht => Ht.
      rewrite Hm Ht.
      reflexivity.
    }
    {
      rewrite /global_type_eqb /=.
      rewrite Hm Ht.
      apply ReflectF.
      move => H.
      injection H => Ht2 Hm2.
      rewrite Ht2 in Ht.
      rewrite eq_refl in Ht.
      move/eqP: Ht => Ht.
      discriminate Ht.
    }
  }
  {
    rewrite /global_type_eqb /=.
    rewrite Hm.
    apply ReflectF.
    move => H.
    injection H => _ Hm2.
    rewrite Hm2 in Hm.
    rewrite eq_refl in Hm.
    move/eqP: Hm => Hm.
    discriminate Hm.
  }
Qed.

(* Todo *)
Canonical global_type_eqMixin := EqMixin eqglobal_typeP.
Canonical global_type_eqType := Eval hnf in EqType global_type global_type_eqMixin.


Inductive function_type := (* tf *)
| Tf : list value_type -> list value_type -> function_type.

Definition function_type_eqb (tf1 tf2 : function_type) : bool :=
  match (tf1, tf2) with
  | (Tf vt11 vt12, Tf vt21 vt22) => (vt11 == vt21) && (vt12 == vt22)
  end.

Lemma eqfunction_typeP : Equality.axiom function_type_eqb.
Proof.
  case => tf11 tf12.
  case => tf21 tf22.
  rewrite /function_type_eqb.
  case_eq (tf11 == tf21) => /= [/eqP-Hm|/eqP-Hm].
  {
    case_eq (tf12 == tf22) => /= [/eqP-Ht|/eqP-Ht].
    {
      apply ReflectT.
      rewrite Hm Ht.
      reflexivity.
    }
    {
      apply ReflectF.
      move => H.
      injection H => {H} Ht2 Hm2.
      rewrite Ht2 in Ht.
      apply: Ht.
      reflexivity.
    }
  }
  {
    apply ReflectF.
    move => H.
    injection H => {H} _ Hm2.
    rewrite Hm2 in Hm.
    apply: Hm.
    reflexivity.
  }
Qed.
Canonical function_type_eqMixin := EqMixin eqfunction_typeP.
Canonical function_type_eqType := Eval hnf in EqType function_type function_type_eqMixin.

Record t_context := {
  tc_types_t : list function_type;
  tc_func_t : list function_type;
  tc_global : list global_type;
  tc_table : option nat;
  tc_memory : option nat;
  tc_local : list value_type;
  tc_label : list (list value_type);
  tc_return : option (list value_type);
}.

Variable t_context_eqb : t_context -> t_context -> bool.
(* TODO *)

Record s_context := {
  sc_inst : list t_context;
  sc_funcs : list function_type;
  sc_tab : list nat;
  sc_mem : list nat;
  sc_globs : list global_type;
}.

Inductive sx : Type :=
| sx_S
| sx_U.

Definition sx_eqb (s1 s2 : sx) : bool :=
  match (s1, s2) with
  | (sx_S, sx_S) => true
  | (sx_U, sx_U) => true
  | _ => false
  end.

Lemma eqsxP : Equality.axiom sx_eqb.
Proof.
  move => v1 v2.
case: v1; case: v2;
try (apply ReflectT; done);
try (apply ReflectF; done).
Qed.
Canonical sx_eqMixin := EqMixin eqsxP.
Canonical sx_eqType := Eval hnf in EqType sx sx_eqMixin.

Inductive unop_i : Type :=
| Clz
| Ctz
| Popcnt.

Inductive unop_f : Type :=
| Neg
| Abs
| Ceil
| Floor
| Trunc
| Nearest
| Sqrt.

Inductive binop_i : Type :=
| Add
| Sub
| Mul
| Div : sx -> binop_i
| Rem : sx -> binop_i
| And
| Or
| Xor
| Shl
| Shr : sx -> binop_i
| Rotl
| Rotr.

Inductive binop_f : Type :=
| Addf
| Subf
| Mulf
| Divf
| Min
| Max
| Copysign.

Inductive testop : Type :=
| Eqz.

Inductive relop_i : Type :=
| Eq
| Ne
| Lt : sx -> relop_i
| Gt : sx -> relop_i
| Le : sx -> relop_i
| Ge : sx -> relop_i.

Inductive relop_f : Type :=
| Eqf
| Nef
| Ltf
| Gtf
| Lef
| Gef.

Inductive cvtop : Type :=
| Convert
| Reinterpret.

Variable i32 : eqType.
Variable i64 : eqType.
Variable f32 : eqType.
Variable f64 : eqType.

Inductive value : Type := (* v *)
| ConstInt32 : i32 -> value
| ConstInt64 : i64 -> value
| ConstFloat32 : f32 -> value
| ConstFloat64 : f64 -> value.

Definition value_eqb (v1 v2 : value) : bool :=
  match (v1, v2) with
  | (ConstInt32 i1, ConstInt32 i2) => i1 == i2
  | (ConstInt64 i1, ConstInt64 i2) => i1 == i2
  | (ConstFloat32 f1, ConstFloat32 f2) => f1 == f2
  | (ConstFloat64 f1, ConstFloat64 f2) => f1 == f2
  | _ => false
  end.

Axiom eqvalueP : Equality.axiom value_eqb.
(* TODO *)
Canonical value_eqMixin := EqMixin eqvalueP.
Canonical value_eqType := Eval hnf in EqType value value_eqMixin.

Inductive basic_instruction : Type := (* be *)
| Unreachable
| Nop
| Drop
| Select
| Block : function_type -> list basic_instruction -> basic_instruction
| Loop : function_type -> list basic_instruction -> basic_instruction
| If : function_type -> list basic_instruction -> list basic_instruction -> basic_instruction
| Br : immediate -> basic_instruction
| Br_if : immediate -> basic_instruction
| Br_table : list immediate -> immediate -> basic_instruction
| Return
| Call : immediate -> basic_instruction
| Call_indirect : immediate -> basic_instruction
| Get_local : immediate -> basic_instruction
| Set_local : immediate -> basic_instruction
| Tee_local : immediate -> basic_instruction
| Get_global : immediate -> basic_instruction
| Set_global : immediate -> basic_instruction
| Load : value_type -> option (packed_type * sx) -> alignment_exponent -> static_offset -> basic_instruction
| Store : value_type -> option packed_type -> alignment_exponent -> static_offset -> basic_instruction
| Current_memory
| Grow_memory
| EConst : value -> basic_instruction
| Unop_i : value_type -> unop_i -> basic_instruction
| Unop_f : value_type -> unop_f -> basic_instruction
| Binop_i : value_type -> binop_i -> basic_instruction
| Binop_f : value_type -> binop_f -> basic_instruction
| Testop : value_type -> testop -> basic_instruction
| Relop_i : value_type -> relop_i -> basic_instruction
| Relop_f : value_type -> relop_f -> basic_instruction
| Cvtop : value_type -> cvtop -> value_type -> option sx -> basic_instruction.

Variable basic_instruction_eqb : basic_instruction -> basic_instruction -> bool.
(* TODO: write this... *)

Axiom eqbasic_instructionP : Equality.axiom basic_instruction_eqb.
Canonical basic_instruction_eqMixin := EqMixin eqbasic_instructionP.
Canonical basic_instruction_eqType := Eval hnf in EqType basic_instruction basic_instruction_eqMixin.

Inductive function_closure : Type := (* cl *)
| Func_native : immediate -> function_type -> list value_type -> list basic_instruction -> function_closure
| Func_host : function_type -> host -> function_closure.

Definition function_closure_eqb (cl1 cl2 : function_closure) : bool :=
  match (cl1, cl2) with
  | (Func_native i1 tf1 vs1 eis1, Func_native i2 tf2 vs2 eis2) =>
    (i1 == i2) && (tf1 == tf2) && (vs1 == vs2) && (eis1 == eis2)
  | (Func_host tf1 h1, Func_host tf2 h2) =>
    (tf1 == tf2) && (h1 == h2)
  | _ => false
  end.

Axiom eqfunction_closureP : Equality.axiom function_closure_eqb.
(* TODO *)
Canonical function_closure_eqMixin := EqMixin eqfunction_closureP.
Canonical function_closure_eqType := Eval hnf in EqType function_closure function_closure_eqMixin.

Record instance : Type := (* inst *) {
  i_types : list function_type;
  i_funcs : list immediate;
  i_tab : option immediate;
  i_mem : option immediate;
  i_globs : list immediate;
}.

Definition instance_eqb (i1 i2 : instance) : bool :=
  (i_types i1 == i_types i2)
    &&
    (i_funcs i1 == i_funcs i2)
    &&
    (i_tab i1 == i_tab i2)
    &&
    (i_mem i1 == i_mem i2)
    &&
    (i_globs i1 == i_globs i2)
.

Axiom eqinstanceP : Equality.axiom instance_eqb.
(* TODO *)
Canonical instance_eqMixin := EqMixin eqinstanceP.
Canonical instance_eqType := Eval hnf in EqType instance instance_eqMixin.

Definition tabinst := list (option function_closure).

Record global : Type := {
  g_mut : mutability;
  g_val : value;
}.

Definition global_eqb (g1 g2 : global) : bool :=
  (g_mut g1 == g_mut g2) && (g_val g1 == g_val g2).

Lemma eqglobalP : Equality.axiom global_eqb.
Proof.
  move => g1 g2.
  case: g1 => m1 t1; case g2 => m2 t2.
  case_eq (m1 == m2) => [Hm|Hm].
  {
    case_eq (t1 == t2) => [Ht|Ht].
    {
      rewrite /global_eqb /=.
      rewrite Hm Ht.
      apply ReflectT.
      move/eqP: Hm => Hm.
      move/eqP: Ht => Ht.
      rewrite Hm Ht.
      reflexivity.
    }
    {
      rewrite /global_eqb /=.
      rewrite Hm Ht.
      apply ReflectF.
      move => H.
      injection H => Ht2 Hm2.
      rewrite Ht2 in Ht.
      rewrite eq_refl in Ht.
      move/eqP: Ht => Ht.
      discriminate Ht.
    }
  }
  {
    rewrite /global_eqb /=.
    rewrite Hm.
    apply ReflectF.
    move => H.
    injection H => _ Hm2.
    rewrite Hm2 in Hm.
    rewrite eq_refl in Hm.
    move/eqP: Hm => Hm.
    discriminate Hm.
  }
Qed.
(* TODO *)
Canonical global_eqMixin := EqMixin eqglobalP.
Canonical global_eqType := Eval hnf in EqType global global_eqMixin.


Record store_record : Type := (* s *) {
  s_inst : list instance;
  s_funcs : list function_closure;
  s_tab : list tabinst;
  s_mem : list mem;
  s_globs : list global;
}.

Definition store_record_eqb (s1 s2 : store_record) : bool :=
  (s_inst s1 == s_inst s2) && (s_funcs s1 == s_funcs s2) && (s_tab s1 == s_tab s2) && (s_mem s1 == s_mem s2) && (s_globs s1 == s_globs s2).

Axiom eqstore_recordP : Equality.axiom store_record_eqb.
(* TODO *)
Canonical store_record_eqMixin := EqMixin eqstore_recordP.
Canonical store_record_eqType := Eval hnf in EqType store_record store_record_eqMixin.

Definition upd_s_mem (s : store_record) (m : list mem) : store_record :=
  Build_store_record
    (s_inst s)
    (s_funcs s)
    (s_tab s)
    m
    (s_globs s).

Inductive administrative_instruction : Type := (* e *)
| Basic : basic_instruction -> administrative_instruction
| Trap
| Callcl : function_closure -> administrative_instruction
| Label : nat -> list administrative_instruction -> list administrative_instruction -> administrative_instruction
| Local : nat -> immediate -> list value -> list administrative_instruction -> administrative_instruction.

Fixpoint administrative_instruction_eqb (e1 e2 : administrative_instruction) : bool :=
  let fff :=
      (fix f (l1 l2 : list administrative_instruction) :=
         match (l1, l2) with
         | (nil, nil) => true
         | (cons _ _, nil) => false
         | (nil, cons _ _) => false
         | (cons x xs, cons y ys) => (administrative_instruction_eqb x y) && (f xs ys)
         end
      ) in
  match (e1, e2) with
  | (Basic be1, Basic be2) => be1 == be2
  | (Trap, Trap) => true
  | (Callcl cl1, Callcl cl2) => cl1 == cl2
  | (Label n1 es11 es12, Label n2 es21 es22) =>
    (Nat.eqb n1 n2) &&
    (fff es11 es21) &&
    (fff es12 es22)
  | (Local n1 i1 vs1 es1, Local n2 i2 vs2 es2) =>
    (Nat.eqb n1 n2) &&
    (Nat.eqb i1 i2) &&
    (vs1 == vs2) &&
    (fff es1 es2)
  | _ => (* TODO *) false
  end.

Axiom eqadministrative_instructionP : Equality.axiom administrative_instruction_eqb.
(* TODO *)
Canonical administrative_instruction_eqMixin := EqMixin eqadministrative_instructionP.
Canonical administrative_instruction_eqType := Eval hnf in EqType administrative_instruction administrative_instruction_eqMixin.


Inductive lholed : Type :=
| LBase : list administrative_instruction -> list administrative_instruction -> lholed
| LRec : list administrative_instruction -> nat -> list administrative_instruction -> lholed -> list administrative_instruction -> lholed.

Variable i32_r : Wasm_int.class_of i32.
Definition i32_t : Wasm_int.type := Wasm_int.Pack i32_r.
Variable i64_r : Wasm_int.class_of i64.
Definition i64_t : Wasm_int.type := Wasm_int.Pack i64_r.
Variable f32_r : Wasm_float.class_of f32.
Definition f32_t : Wasm_float.type := Wasm_float.Pack f32_r.
Variable f64_r : Wasm_float.class_of f64.
Definition f64_t : Wasm_float.type := Wasm_float.Pack f64_r.

Variable ui32_trunc_f32 : f32 -> option i32.
Variable si32_trunc_f32 : f32 -> option i32.
Variable ui32_trunc_f64 : f64 -> option i32.
Variable si32_trunc_f64 : f64 -> option i32.

Variable ui64_trunc_f32 : f32 -> option i64.
Variable si64_trunc_f32 : f32 -> option i64.
Variable ui64_trunc_f64 : f64 -> option i64.
Variable si64_trunc_f64 : f64 -> option i64.

Variable f32_convert_ui32 : i32 -> f32.
Variable f32_convert_si32 : i32 -> f32.
Variable f32_convert_ui64 : i64 -> f32.
Variable f32_convert_si64 : i64 -> f32.

Variable f64_convert_ui32 : i32 -> f64.
Variable f64_convert_si32 : i32 -> f64.
Variable f64_convert_ui64 : i64 -> f64.
Variable f64_convert_si64 : i64 -> f64.

Variable wasm_wrap : i64 -> i32.
Variable wasm_extend_u : i32 -> i64.
Variable wasm_extend_s : i32 -> i64.
Variable wasm_demote : f64 -> f32.
Variable wasm_promote : f32 -> f64.

Variable serialise_i32 : i32 -> bytes.
Variable serialise_i64 : i64 -> bytes.
Variable serialise_f32 : f32 -> bytes.
Variable serialise_f64 : f64 -> bytes.
Variable wasm_bool : bool -> i32.
Variable int32_minus_one : i32.

Definition mem_size (m : mem) :=
  length m.

Definition mem_grow (m : mem) (n : nat) :=
 m ++ bytes_replicate (n * 64000) 0.

Definition load (m : mem) (n : nat) (off : static_offset) (l : nat) : option bytes :=
  if mem_size m >= (n + off + l)
  then Some (read_bytes m (n + off) l)
  else None.

Definition sign_extend (s : sx) (l : nat) (bs : bytes) : bytes :=
  (* TODO *) bs.
(* TODO
  let msb := msb (msbyte bytes) in
  let byte := (match sx with sx_U => O | sx_S => if msb then -1 else 0) in
  bytes_takefill byte l bytes
*)

Definition load_packed (s : sx) (m : mem) (n : nat) (off : static_offset) (lp : nat) (l : nat) : option bytes :=
  option_map (sign_extend s l) (load m n off lp).

Definition store (m : mem) (n : nat) (off : static_offset) (bs : bytes) (l : nat) : option mem :=
  if (mem_size m) >= (n + off + l)
  then Some (write_bytes m (n + off) (bytes_takefill O l bs))
  else None.

Definition store_packed := store.

Variable wasm_deserialise : bytes -> value_type -> value.

Variable host_apply : store_record -> function_type -> host -> list value -> host_state -> option (store_record * list value).

Definition typeof (v : value) : value_type :=
  match v with
  | ConstInt32 _ => T_i32
  | ConstInt64 _ => T_i64
  | ConstFloat32 _ => T_f32
  | ConstFloat64 _ => T_f64
  end.

Definition option_projl (A B : Type) (x : option (A * B)) : option A :=
  option_map fst x.

Definition option_projr (A B : Type) (x : option (A * B)) : option B :=
  option_map snd x.

Definition t_length (t : value_type) : nat :=
  match t with
  | T_i32 => 4
  | T_i64 => 8
  | T_f32 => 4
  | T_f64 => 8
  end.

Definition tp_length (tp : packed_type) : nat :=
  match tp with
  | Tp_i8 => 1
  | Tp_i16 => 2
  | Tp_i32 => 4
  end.

Definition is_int_t (t : value_type) : bool :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  end.

Definition is_float_t (t : value_type) : bool :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  end.

Definition is_mut (tg : global_type) : bool :=
  tg_mut tg == T_mut.

Check Wasm_int.int_ctz.
Check Wasm_int.class.

Definition app_unop_i (e : Wasm_int.type) (iop : unop_i) (c : Wasm_int.sort e) : Wasm_int.sort e :=
  (let: Wasm_int.Pack u (Wasm_int.Class eqmx intmx) as e' := e return Wasm_int.sort e' -> Wasm_int.sort e' in
  match iop with
  | Ctz => Wasm_int.int_ctz intmx
  | Clz => Wasm_int.int_clz intmx
  | Popcnt => Wasm_int.int_popcnt intmx
  end) c.

Definition app_unop_f (e : Wasm_float.type) (fop : unop_f) (c : Wasm_float.sort e) : Wasm_float.sort e :=
  (let: Wasm_float.Pack u (Wasm_float.Class eqmx mx) as e' := e return Wasm_float.sort e' -> Wasm_float.sort e' in
  match fop with
  | Neg => Wasm_float.float_neg mx
  | Abs => Wasm_float.float_abs mx
  | Ceil => Wasm_float.float_ceil mx
  | Floor => Wasm_float.float_floor mx
  | Trunc => Wasm_float.float_trunc mx
  | Nearest => Wasm_float.float_nearest mx
  | Sqrt => Wasm_float.float_sqrt mx
  end) c.

(* TODO: can't be bothered to make this nicer *)
Definition app_binop_i (e : Wasm_int.type) (iop : binop_i) (c1 c2 : Wasm_int.sort e) : option (Wasm_int.sort e) :=
  (let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> Wasm_int.sort e' -> option (Wasm_int.sort e') in
  match iop with
  | Add => fun c1 c2 => Some (Wasm_int.int_add mx c1 c2)
  | Sub => fun c1 c2 => Some (Wasm_int.int_sub mx c1 c2)
  | Mul => fun c1 c2 => Some (Wasm_int.int_mul mx c1 c2)
  | Div sx_U => Wasm_int.int_div_u mx
  | Div sx_S => Wasm_int.int_div_s mx
  | Rem sx_U => Wasm_int.int_rem_u mx
  | Rem sx_S => Wasm_int.int_rem_s mx
  | And => fun c1 c2 => Some (Wasm_int.int_and mx c1 c2)
  | Or => fun c1 c2 => Some (Wasm_int.int_or mx c1 c2)
  | Xor => fun c1 c2 => Some (Wasm_int.int_xor mx c1 c2)
  | Shl => fun c1 c2 => Some (Wasm_int.int_shl mx c1 c2)
  | Shr sx_U => fun c1 c2 => Some (Wasm_int.int_shr_u mx c1 c2)
  | Shr sx_S => fun c1 c2 => Some (Wasm_int.int_shr_s mx c1 c2)
  | Rotl => fun c1 c2 => Some (Wasm_int.int_rotl mx c1 c2)
  | Rotr => fun c1 c2 => Some (Wasm_int.int_rotr mx c1 c2)
  end) c1 c2.

(* TODO: can't be bothered to make this nicer *)
Definition app_binop_f (e : Wasm_float.type) (fop : binop_f) (c1 c2 : Wasm_float.sort e) : option (Wasm_float.sort e) :=
    (let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e return Wasm_float.sort e' -> Wasm_float.sort e' -> option (Wasm_float.sort e') in
  match fop with
  | Addf => fun c1 c2 => Some (Wasm_float.float_add mx c1 c2)
  | Subf => fun c1 c2 => Some (Wasm_float.float_sub mx c1 c2)
  | Mulf => fun c1 c2 => Some (Wasm_float.float_mul mx c1 c2)
  | Divf => fun c1 c2 => Some (Wasm_float.float_div mx c1 c2)
  | Min => fun c1 c2 => Some (Wasm_float.float_min mx c1 c2)
  | Max => fun c1 c2 => Some (Wasm_float.float_max mx c1 c2)
  | Copysign => fun c1 c2 => Some (Wasm_float.float_copysign mx c1 c2)
  end) c1 c2.

Definition app_testop_i (e : Wasm_int.type) (o : testop) (c : Wasm_int.sort e) : bool :=
  (let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> bool in
  match o with
  | Eqz => fun c => Wasm_int.int_eqz mx c
  end) c.

Definition app_relop_i (e : Wasm_int.type) (rop : relop_i) (c1 c2 : Wasm_int.sort e) : bool :=
  (let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> Wasm_int.sort e' -> bool in
  match rop with
  | Eq => fun c1 c2 => Wasm_int.int_eq mx c1 c2
  | Ne => fun c1 c2 => Wasm_int.int_ne c1 c2
  | Lt sx_U => fun c1 c2 => Wasm_int.int_lt_u mx c1 c2
  | Lt sx_S => fun c1 c2 => Wasm_int.int_lt_s mx c1 c2
  | Gt sx_U => fun c1 c2 => Wasm_int.int_gt_u mx c1 c2
  | Gt sx_S => fun c1 c2 => Wasm_int.int_gt_s mx c1 c2
  | Le sx_U => fun c1 c2 => Wasm_int.int_le_u mx c1 c2
  | Le sx_S => fun c1 c2 => Wasm_int.int_le_s mx c1 c2
  | Ge sx_U => fun c1 c2 => Wasm_int.int_ge_u mx c1 c2
  | Ge sx_S => fun c1 c2 => Wasm_int.int_ge_s mx c1 c2
  end) c1 c2.

Definition app_relop_f (e : Wasm_float.type) (rop : relop_f) (c1 c2 : Wasm_float.sort e) : bool :=
  (let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e return Wasm_float.sort e' -> Wasm_float.sort e' -> bool in
  match rop with
  | Eqf => fun c1 c2 => Wasm_float.float_eq mx c1 c2
  | Nef => fun c1 c2 => Wasm_float.float_ne c1 c2
  | Ltf => fun c1 c2 => Wasm_float.float_lt mx c1 c2
  | Gtf => fun c1 c2 => Wasm_float.float_gt mx c1 c2
  | Lef => fun c1 c2 => Wasm_float.float_le mx c1 c2
  | Gef => fun c1 c2 => Wasm_float.float_ge mx c1 c2
  end) c1 c2.

Definition types_agree (t : value_type) (v : value) : bool :=
  (typeof v) == t.

Definition cl_type (cl : function_closure) : function_type :=
  match cl with
  | Func_native _ tf _ _ => tf
  | Func_host tf _ => tf
  end.

Definition rglob_is_mut (g : global) : bool :=
  g_mut g == T_mut.

Definition option_bind (A B : Type) (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some y => f y
  end.

Definition stypes (s : store_record) (i j : nat) : option function_type :=
  option_bind (fun l => List.nth_error l j)
   (option_map (i_types) (List.nth_error (s_inst s) i)).
(* TODO: optioned *)

Definition sfunc_ind (s : store_record) (i j : nat) : option nat :=
  option_bind (fun l => List.nth_error l j) (option_map i_funcs (List.nth_error (s_inst s) i)).

Definition sfunc (s : store_record) (i j : nat) : option function_closure :=
  option_bind (List.nth_error (s_funcs s)) (sfunc_ind s i j).

Definition sglob_ind (s : store_record) (i j : nat) : option nat :=
  option_bind (fun l => List.nth_error l j)
   (option_map i_globs (List.nth_error (s_inst s) i)).

Definition sglob (s : store_record) (i j : nat) : option global :=
  option_bind (List.nth_error (s_globs s))
    (sglob_ind s i j).

Definition sglob_val (s : store_record) (i j : nat) : option value :=
  option_map g_val (sglob s i j).

Definition smem_ind (s : store_record) (i : nat) : option nat :=
  option_bind i_mem (List.nth_error (s_inst s) i).

Definition stab_s (s : store_record) (i j : nat) : option function_closure :=
  let stabinst := List.nth_error (s_tab s) i in
  option_bind (fun x => x) (
  option_bind
    (fun stabinst => if length stabinst > j then List.nth_error stabinst j else None)
    stabinst).

Definition stab (s : store_record) (i j : nat) : option function_closure :=
  match option_bind i_tab (List.nth_error (s_inst s) i) with
  | Some k => stab_s s k j
  | None => None
  end.

Definition update_list_at {A : Type} (l : list A) (k : nat) (a : A) :=
  List.firstn k l ++ [::a] ++ List.skipn (k + 1) l.

Definition supdate_glob_s (s : store_record) (k : nat) (v : value) : option store_record :=
  option_map
  (fun g =>
   let g' := Build_global (g_mut g) v in 
   let gs' := update_list_at (s_globs s) k g' in 
  Build_store_record
  (s_inst s)
  (s_funcs s)
  (s_tab s)
  (s_mem s)
  gs')
  (List.nth_error (s_globs s) k).

Definition supdate_glob (s : store_record) (i j : nat) (v : value) : option store_record :=
  option_bind
    (fun k => supdate_glob_s s k v)
    (sglob_ind s i j).

Definition is_const (e : administrative_instruction) : bool :=
  match e with
  | Basic _ => true
  | _ => false
  end.

Definition const_list (es : list administrative_instruction) : bool :=
  List.forallb is_const es.

Definition store_extension (s s' : store_record) : bool :=
  ((s_inst s) == (s_inst s')) &&
  ((s_funcs s) == (s_funcs s')) &&
  ((s_tab s) == (s_tab s')) &&
  (all2 (fun bs bs' => mem_size bs <= mem_size bs') (s_mem s) (s_mem s')) &&
  ((s_globs s) == (s_globs s')).

Definition to_e_list (bes : list basic_instruction) : list administrative_instruction :=
  map Basic bes.

Definition v_to_e_list (ves : list value) : list administrative_instruction :=
  map (fun v => Basic (EConst v)) ves.

Fixpoint lfill (k : nat) (lh : lholed) (es : list administrative_instruction) : option (list administrative_instruction) :=
  match k with
  | O =>
   match lh with
    | LBase vs es' => if const_list vs then Some (app vs (app es es')) else None
    | LRec _ _ _ _ _ => None
   end
  | S k' =>
   match lh with
   | LBase _ _ => None
   | LRec vs n es' lh' es'' =>
     if const_list vs then
       match lfill k' lh' es with
       | Some lfilledk => Some (app vs (cons (Label n es' lfilledk) es''))
       | None => None
       end
     else None
   end
  end.

Definition lfilled (k : nat) (lh : lholed) (es : list administrative_instruction) (es' : list administrative_instruction) : bool :=
  match lfill k lh es with
  | None => false
  | Some es'' => es' == es''
  end.

(* TODO: also inductive definition? *)

Fixpoint lfill_exact (k : nat) (lh : lholed) (es : list administrative_instruction) : option (list administrative_instruction) :=
  match k with
  | O =>
   match lh with
    | LBase nil nil => Some es
    | LBase _ _ => None
    | LRec _ _ _ _ _ => None
   end
  | S k' =>
   match lh with
   | LBase _ _ => None
   | LRec vs n es' lh' es'' =>
     if const_list vs then
       match lfill_exact k' lh' es with
       | Some lfilledk => Some (app vs (cons (Label n es' lfilledk) es''))
       | None => None
       end
     else None
   end
  end.

Definition lfilled_exact (k : nat) (lh : lholed) (es : list administrative_instruction) (es' : list administrative_instruction) : bool :=
  match lfill_exact k lh es with
  | None => false
  | Some es'' => es' == es''
  end.

Definition load_store_t_bounds (a : alignment_exponent) (tp : option packed_type) (t : value_type) : bool :=
  match tp with
  | None => Nat.pow 2 a <= t_length t
  | Some tp' => (Nat.pow 2 a <= tp_length tp') && (tp_length tp' < t_length t) && (is_int_t t)
  end.

Definition cvt_i32 (s : option sx) (v : value) : option i32 :=
  match v with
  | ConstInt32 _ => None
  | ConstInt64 c => Some (wasm_wrap c)
  | ConstFloat32 c =>
    match s with
    | Some sx_U => ui32_trunc_f32 c
    | Some sx_S => si32_trunc_f32 c
    | None => None
    end
  | ConstFloat64 c =>
    match s with
    | Some sx_U => ui32_trunc_f64 c
    | Some sx_S => si32_trunc_f64 c
    | None => None
    end
  end.

Definition cvt_i64 (s : option sx) (v : value) : option i64 :=
  match v with
  | ConstInt32 c =>
    match s with
    | Some sx_U => Some (wasm_extend_u c)
    | Some sx_S => Some (wasm_extend_s c)
    | None => None
    end
  | ConstInt64 c => None
  | ConstFloat32 c =>
    match s with
    | Some sx_U => ui64_trunc_f32 c
    | Some sx_S => si64_trunc_f32 c
    | None => None
    end
  | ConstFloat64 c =>
    match s with
    | Some sx_U => ui64_trunc_f64 c
    | Some sx_S => si64_trunc_f64 c
    | None => None
    end
  end.

Definition cvt_f32 (s : option sx) (v : value) : option f32 :=
  match v with
  | ConstInt32 c =>
    match s with
    | Some sx_U => Some (f32_convert_ui32 c)
    | Some sx_S => Some (f32_convert_si32 c)
    | None => None
    end
  | ConstInt64 c =>
    match s with
    | Some sx_U => Some (f32_convert_ui64 c)
    | Some sx_S => Some (f32_convert_si64 c)
    | None => None
    end
  | ConstFloat32 c => None
  | ConstFloat64 c => Some (wasm_demote c)
  end.

Definition cvt_f64 (s : option sx) (v : value) : option f64 :=
  match v with
  | ConstInt32 c =>
    match s with
    | Some sx_U => Some (f64_convert_ui32 c)
    | Some sx_S => Some (f64_convert_si32 c)
    | None => None
    end
  | ConstInt64 c =>
    match s with
    | Some sx_U => Some (f64_convert_ui64 c)
    | Some sx_S => Some (f64_convert_si64 c)
    | None => None
    end
  | ConstFloat32 c => Some (wasm_promote c)
  | ConstFloat64 c => None
  end.

Definition cvt (t : value_type) (s : option sx) (v : value) : option value :=
  match t with
  | T_i32 => option_map ConstInt32 (cvt_i32 s v)
  | T_i64 => option_map ConstInt64 (cvt_i64 s v)
  | T_f32 => option_map ConstFloat32 (cvt_f32 s v)
  | T_f64 => option_map ConstFloat64 (cvt_f64 s v)
  end.

Definition bits (v : value) : bytes :=
  match v with
  | ConstInt32 c => serialise_i32 c
  | ConstInt64 c => serialise_i64 c
  | ConstFloat32 c => serialise_f32 c
  | ConstFloat64 c => serialise_f64 c
  end.

Definition bitzero (t : value_type) : value :=
  match t with
  | T_i32 => ConstInt32 (Wasm_int.int_zero (Wasm_int.mixin i32_r))
  | T_i64 => ConstInt64 (Wasm_int.int_zero (Wasm_int.mixin i64_r))
  | T_f32 => ConstFloat32 (Wasm_float.float_zero (Wasm_float.mixin f32_r))
  | T_f64 => ConstFloat64 (Wasm_float.float_zero (Wasm_float.mixin f64_r))
  end.

Definition n_zeros (ts : list value_type) : list value :=
  map bitzero ts.

(* TODO: lots of lemmas *)
