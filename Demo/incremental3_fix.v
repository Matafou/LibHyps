(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)
(* Lemma on determinism needs generalization. *)

Require Import FSets.FMapList FSets.FMapFacts Arith ZArith
        LibHyps.LibHyps List.
Require Import Structures.OrderedTypeEx FSets.FSetList.

Module Env := FMapList.Make(Nat_as_OT).
Module EnvFact := FMapFacts.Facts(Env).

Inductive binop := Plus | Minus | Mult.

Inductive exp : Type :=
| Val : Z -> exp
| Var : nat -> exp
| BinOp: binop -> exp -> exp -> exp.

Definition eval_op op :=
  match op with
     Plus => Z.add| Minus => Z.sub| Mult => Z.mul
  end.

Inductive Eval_exp Γ: exp -> Z -> Prop:=
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
    Eval_exp _ ?e ?v => name(`_EE` ++ e#n ++ v#n)
  | Val ?v => name(v#(S n))
  | Var ?x => name(x#(S n))
  | BinOp ?o ?e1 ?e2 => name(o#(S 0) ++ e1#n ++ e2#n)
  | eval_op ?o ?v1 ?v2 => name(o#(S 0) ++ v1#n ++ v2#n)
  | Env.Equal ?X ?Y => name(`_EQ` ++ X#n ++ Y#n) (* shorten Equal *)
  end.
Close Scope autonaming_scope.
Ltac rename_hyp ::= rename_hyp_eval.


(* We actually need to prove modulo equivalence of environments *)
Lemma determ_nolibhyp: forall Γ Γ' e v v',
    Eval_exp Γ e v -> 
    Eval_exp Γ' e v' -> 
    Env.Equal Γ Γ' -> 
    v = v'.
Proof.
  intros * h_EE_e_v. 
  revert v'.
  induction h_EE_e_v as
      [v | x v h_MapsTo | e1 e2 v1 v2 op f h_e_v1 IH_v1 h_e_v2 IH_v2 hop];
    intros v' h_EE_e_v' heq_Γ.
  - inversion h_EE_e_v'.
    auto.
  - inversion h_EE_e_v'; auto; subst.
    rewrite heq_Γ in h_MapsTo.
    eapply EnvFact.MapsTo_fun;eauto.
  - inversion h_EE_e_v'.
    subst.
    erewrite IH_v1;eauto.
    erewrite IH_v2;eauto.
Qed.

Lemma determ: forall Γ Γ' e v v',
    Eval_exp Γ e v -> 
    Eval_exp Γ' e v' -> 
    Env.Equal Γ Γ' -> 
    v = v'.
Proof.
  intros until 1 /ng.
  revert v'.
  induction h_EE_e_v_; intros /sng.
  - inversion h_EE_v_v'_.
    auto.
  - inversion h_EE_x_v'_; auto /sng.
    rewrite h_EQ_Γ_Γ'_ in h_MapsTo_x_v_Γ_.
    eapply EnvFact.MapsTo_fun;eauto.
  - inversion h_EE_op_e1_e2_v'_ /sng.
    erewrite h_all_eq_v1_v'_;eauto.
    erewrite h_all_eq_v2_v'_;eauto.
Qed.


(*** Local Variables: ***)
(*** eval: (company-coq-mode 1) ***)
(*** End: ***)
