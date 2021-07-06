(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

Require Import FSets.FMapList FSets.FMapFacts Arith ZArith
        LibHyps.LibHyps List.
Require Import Structures.OrderedTypeEx FSets.FSetList.
 
Inductive binop := Plus | Minus | Mult.

Inductive exp : Type :=
| Val : Z -> exp
| BinOp: binop -> exp -> exp -> exp.

Definition eval_op op :=
  match op with
     Plus => Z.add| Minus => Z.sub| Mult => Z.mul
  end.


Inductive Eval_exp: exp -> Z -> Prop:=
  EE_val: forall v, Eval_exp (Val v) v
| EE_binop: forall e1 e2 v1 v2 op f,
    Eval_exp e1 v1
    -> Eval_exp e2 v2
    -> eval_op op = f
    -> Eval_exp (BinOp op e1 e2) (f v1 v2).


(* optional customization *)
Ltac rename_depth ::= constr:(3).
Local Open Scope autonaming_scope.
Import ListNotations.
Ltac rename_hyp_eval n th :=
  match th with
    Eval_exp ?e ?v => name(`_EE` ++ e#n ++ v#n)
  | Val ?v => name(v#(S n))
  | BinOp ?o ?e1 ?e2 => name(o#(S 0) ++ e1#n ++ e2#n)
  | eval_op ?o ?v1 ?v2 => name(o#(S 0) ++ v1#n ++ v2#n)
  end.
Close Scope autonaming_scope.
Ltac rename_hyp ::= rename_hyp_eval.




Lemma determ_nolibhyp: forall e v v',
    Eval_exp e v -> 
    Eval_exp e v' -> 
    v = v'.
Proof.
  intros * h_EE_e_v. 
  revert v'.
  induction h_EE_e_v as
      [v | e1 e2 v1 v2 op f h_e_v1 IH_v1 h_e_v2 IH_v2 hop];
    intros v' h_EE_e_v'.
  - inversion h_EE_e_v'.
    auto.
  - inversion h_EE_e_v'. (* "as" very hard to guess + useless here. *)
    subst.
    erewrite IH_v1;eauto.
    erewrite IH_v2;eauto.
Qed.

(* Same proof as above, no naming effort. *)
Lemma determ: forall e v v',
    Eval_exp e v -> 
    Eval_exp e v' -> 
    v = v'.
Proof.
  intros until 1 /ng.
  revert v'.
  induction h_EE_e_v_; intros  /sng.
  - inversion h_EE_v_v'_.
    auto.
  - inversion h_EE_op_e1_e2_v'_ /sng.
    erewrite h_all_eq_v1_v'_;eauto.
    erewrite h_all_eq_v2_v'_;eauto.
Qed.

(*** Local Variables: ***)
(*** eval: (company-coq-mode 1) ***)
(*** End: ***)
