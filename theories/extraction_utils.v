From mathcomp Require Import ssreflect ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* TODO file naming -- type-logic / type-prop utils? *)

(* XXX do the extra spaces here make a difference? *)
Notation " P ** Q " := (prod P Q) (at level 5, right associativity).

(* Basic logic ops for Type *)
(* XXX is there something similar in stdlib? Search didn't return anything *)
(* TODO n-ary sigtype notation? *)
Definition notT (T : Type) : Type := T -> Empty_set.
Definition decidableT (T : Type) : Type := T + notT T.
Definition iffT (A B : Type) : Type := prod (A -> B) (B -> A).
Notation "P <--> Q" := (iffT P Q) (at level 95, right associativity).
(* XXX resolve deprecation warning
 * used this to get not-like behaviour for auto tactics but *)
Hint Unfold notT : core.
Hint Unfold iffT : core.

(* TODO reuse equiv_Empty_set_False *)
Definition Empty_set_imp_False : Empty_set -> False.
Proof. intro H. inversion H. Qed.


(* TODO move to a Type utils common file *)
Lemma equiv_Empty_set_False : iffT False Empty_set.
Proof. split; (intros H; inversion H). Qed.


Lemma not_notT : forall (P : Prop), ~ P -> notT P.
Proof.
  intros P HNP. intros HP. destruct (HNP HP).
Qed.

Lemma decidable_decidableT : forall (P : Prop), decidable P -> decidableT P.
Proof.
  intros P [HP|HNP]; unfold decidableT.
  - left. by apply HP.
  - right. by apply (not_notT HNP).
Qed.


