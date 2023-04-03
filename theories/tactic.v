From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import operations opsem properties.

(** A common pattern in the proof: using an hypothesis on the form [rev l = l'] to rewrite [l]. **)
Ltac subst_rev_const_list :=
 repeat lazymatch goal with
 | HRevConst: rev ?lconst = ?h :: ?t |- _ =>
   apply rev_move in HRevConst; rewrite HRevConst; rewrite -cat1s; rewrite rev_cat;
   rewrite -v_to_e_cat; rewrite -catA
 end.

(** Simplify the lists in the goal. **)
Ltac simplify_lists :=
  (** Common rewriting rules. **)
  repeat first [
      rewrite drop_rev
    | rewrite take_rev
    | rewrite revK
    | rewrite length_is_size
    | rewrite size_take
    | rewrite size_drop
    | rewrite size_rev
    | rewrite v_to_e_size
    | rewrite rev_cat
    | rewrite rev_cons -cats1
    | rewrite -v_to_e_cat
    | rewrite -v_to_e_rev
    | rewrite -v_to_e_take
    | rewrite -v_to_e_drop];
  (** Putting all the lists into a normal form, as concatenations of as many things.
    Because [cat1s] conflicts with [cats0], replacing any occurence of [[X]] to
    [[X] ++ [::]], it has to be done separately.
    Rewrite with the associated [math goal with] is avoid to deal with existential
    vairables. **)
  repeat match goal with
  |- context C [?x :: ?l] =>
     lazymatch l with [::] => fail | _ => rewrite -(cat1s x l) end
  end;
  repeat lazymatch goal with
  | |- context C [[::] ++ _] => rewrite cat0s
  | |- context C [_ ++ [::]] => rewrite cats0
  | |- context C [rcons _ _] => rewrite -cats1
  | |- context C [(_ ++ _) ++ _] => rewrite -catA
  | |- context C [rev [::]] => rewrite rev0
  | |- context C [v_to_e_list [::]] => rewrite v_to_e_list0
  | |- context C [v_to_e_list [:: _]] => rewrite v_to_e_list1
  end;
  try subst_rev_const_list.

