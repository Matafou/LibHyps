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
| BinOp: binop -> exp -> exp -> exp
| Assign: nat -> exp -> exp.

Inductive Com : Type :=
| Skip: Com
| Seq: Com -> Com -> Com.

Record Ret := { val: Z; env: Env.t Z }.

Definition EqRet ret1 ret2 :=
  ret1.(val) = ret2.(val)
  /\ Env.Equal ret1.(env) ret2.(env).

Definition eval_op op :=
  match op with
     Plus => Z.add| Minus => Z.sub| Mult => Z.mul
  end.

Inductive Eval_exp Γ: exp -> Ret -> Prop :=
  EE_val: forall v, Eval_exp Γ (Val v) {| val := v; env := Γ |}
| EE_var: forall x v, Env.MapsTo x v Γ -> Eval_exp Γ (Var x) {| val := v; env := Γ |}
| EE_binop: forall e1 e2 v1 v2 op f,
    Eval_exp Γ e1 v1 -> Eval_exp Γ e2 v2 -> eval_op op = f
    -> Eval_exp Γ (BinOp op e1 e2) {| val :=(f v1.(val) v2.(val)); env := Γ |}
| EX_Assign: forall (x:nat) (e:exp) v, 
    Eval_exp Γ e v ->
    Eval_exp Γ (Assign x e) {| val := v.(val);
                               env := (Env.add x v.(val) v.(env)) |}
.

Inductive Exec Γ: Com -> Env.t Z -> Prop :=
| EX_Skip: Exec Γ Skip Γ
| EX_Seq: forall Γ1 Γ2 (c1 c2:Com),
    Exec Γ c1 Γ1 -> Exec Γ1 c2 Γ2 -> Exec Γ (Seq c1 c2) Γ2.

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
  | Exec ?G ?c ?G' => name(`_EX` ++ G#n ++ c#n ++ G'#n)
  | Env.Equal ?X ?Y => name(`_EQ` ++ X#n ++ Y#n) (* shorten Equal *)
  | EqRet ?X ?Y => name(`_EQ` ++ X#n ++ Y#n) (* shorten Equal *)
  end.
Close Scope autonaming_scope.
Ltac rename_hyp ::= rename_hyp_eval.


(* We actually need to prove modulo equivalence of environments *)
Lemma determ: forall Γ Γ' e v v',
    Eval_exp Γ e v -> 
    Eval_exp Γ' e v' -> 
    Env.Equal Γ Γ' -> 
    EqRet v v'.
Proof.
  intros until 1 /ng.
  revert v'.
  induction h_EE_e_v_; intros /sng.
  - inversion h_EE_v_v'_.
    red;auto.
  - inversion h_EE_x_v'_ /sng.
    rewrite h_EQ_Γ_Γ'_ in h_MapsTo_x_v_Γ_.
    red.
    assert (v=v0)/sng.
    { eapply EnvFact.MapsTo_fun;eauto. }
    auto.
  - inversion h_EE_op_e1_e2_v'_ /sng.
    specialize h_all_EQ_v1_v'_ with (1:=h_EE_e1_v0_) (2:=h_EQ_Γ_Γ'_).
    specialize h_all_EQ_v2_v'_ with (1:=h_EE_e2_v3_) (2:=h_EQ_Γ_Γ'_).
    unfold EqRet in h_all_EQ_v1_v'_, h_all_EQ_v2_v'_.
    destruct h_all_EQ_v1_v'_, h_all_EQ_v2_v'_/sng.
    rewrite h_eq_val_v1_val_v0_, h_eq_val_v2_val_v3_.
    red;auto.
  - inversion h_EE_Assign_x_e_v'_ /sng.
    subst.
    specialize h_all_EQ_v_v'_ with (1:=h_EE_e_v0_) (2:=h_EQ_Γ_Γ'_).
    unfold EqRet in h_all_EQ_v_v'_.
    destruct h_all_EQ_v_v'_ /sng.
    repeat rewrite h_eq_val_v_val_v0_.
    red;split;auto.
    cbn.
    rewrite h_EQ_env_v_env_v0_.
    reflexivity.
Qed.


(*** Local Variables: ***)
(*** eval: (company-coq-mode 1) ***)
(*** End: ***)
