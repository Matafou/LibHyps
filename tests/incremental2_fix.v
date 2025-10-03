(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)
(* Adding variables, thus an environment. *)

Require Import FSets.FMapList FSets.FMapFacts Arith ZArith
        LibHyps.LibHyps List.
Require Import Structures.OrderedTypeEx FSets.FSetList.

(* Env is a map from nat to values (Z) *)
Module Env := FMapList.Make(Nat_as_OT).
Module EnvFact := FMapFacts.Facts(Env).

Inductive binop := Plus | Minus | Mult.

(* We add variabes *)
Inductive exp : Type :=
| Val : Z -> exp
| Var : nat -> exp
| BinOp: binop -> exp -> exp -> exp.

Definition eval_op op :=
  match op with
     Plus => Z.add| Minus => Z.sub| Mult => Z.mul
  end.

(* We add an environment Γ in the rules. *)
Inductive Eval_exp Γ : exp -> Z -> Prop:=
  EE_val: forall v, Eval_exp Γ (Val v) v
| EE_var: forall x v, Env.MapsTo x v Γ -> Eval_exp Γ (Var x) v
| EE_binop: forall e1 e2 v1 v2 op f,
    Eval_exp Γ e1 v1
    -> Eval_exp Γ e2 v2
    -> eval_op op = f
    -> Eval_exp Γ (BinOp op e1 e2) (f v1 v2).


(* optional customization *)
Ltac rename_depth ::= constr:(3).
Local Open Scope autonaming_scope.
Import ListNotations.
Ltac rename_hyp_eval n th :=
  match th with
    Eval_exp _ ?e ?v => name(`_EE` ++ e#n ++ v#n) (* no gamma in name *)
  | Val ?v => name(v#(S n)) (* v instead of Val v *)
  | Var ?x => name(x#(S n)) (* x instead of Var x *)
  | BinOp ?o ?e1 ?e2 => name(o#(S 0) ++ e1#n ++ e2#n) (* hide BinOp *)
  | eval_op ?o ?v1 ?v2 => name(o#(S 0) ++ v1#n ++ v2#n) (* hide eval_op *)
  end.
Close Scope autonaming_scope.
Ltac rename_hyp ::= rename_hyp_eval.


Lemma determ_nolibhyp: forall Γ e v v',
    Eval_exp Γ e v -> 
    Eval_exp Γ e v' -> 
    v = v'.
Proof.
  intros * h_EE_e_v. 
  revert v'.
  induction h_EE_e_v as
      [v | x v h_MapsTo | e1 e2 v1 v2 op f h_e_v1 IH_v1 h_e_v2 IH_v2 hop];
    intros v' h_EE_e_v'.
  - inversion h_EE_e_v'.
    auto.
  - inversion h_EE_e_v'; auto; subst.
    eapply EnvFact.MapsTo_fun;eauto.
  - inversion h_EE_e_v'.
    subst.
    erewrite IH_v1;eauto.
    erewrite IH_v2;eauto.
Qed.

(* No intros to update. Some hyps have a new type hence a new name. *)
Lemma determ: forall Γ e v v',
    Eval_exp Γ e v -> 
    Eval_exp Γ e v' -> 
    v = v'.
Proof.
  intros until 1 /ng.
  revert v'.
  induction h_EE_e_v_; intros /sng.
  - inversion h_EE_v_v'_.
    auto.
  - inversion h_EE_x_v'_ ; auto/sng.
    eapply EnvFact.MapsTo_fun;eauto.
  - inversion h_EE_op_e1_e2_v'_ /sng.
    erewrite h_all_eq_v1_v'_;eauto.
    erewrite h_all_eq_v2_v'_;eauto.
Qed.

(*** Local Variables: ***)
(*** eval: (company-coq-mode 1) ***)
(*** End: ***)
