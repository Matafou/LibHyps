(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

Require Import Arith ZArith LibHyps.LibHyps (*LibHyps.LibSpecialize*) List.

Lemma foo: forall x y z:nat,
    x = y -> forall  a b t : nat, a+1 = t+2 -> b + 5 = t - 7 ->  (forall u v, v+1 = 1 -> u+1 = 1 -> a+1 = z+2)  -> z = b + x-> True.
Proof.
  intros.
  (* ugly names *)
  Undo.
  (* Example of using the iterator on new hyps: this prints each new hyp name. *)
  intros; {fun h => idtac h}.
  Undo.
  (* This gives sensible names to each new hyp. *)
  intros ; { autorename }.
  Undo.
  (* short syntax: *)
  intros /n.
  Undo.
  (* same thing but use subst if possible, and group non prop hyps to the top. *)
  intros ; { substHyp }; { autorename}; {move_up_types}.
  Undo.
  (* short syntax: *)  
  intros /s/n/g.
  Undo.
  (* Even shorter: *)  
  intros /s/n/g.

  (* Let us instantiate the 2nd premis of h_all_eq_add_add without copying its type: *)
  (* BROKEN IN COQ 8.18*)
  especialize h_all_eq_add_add_ with u at 2.
  { apply Nat.add_0_l. }
  (* now h_all_eq_add_add is specialized *)
  Undo 6.

  intros until 1.
  (** The taticals apply after any tactic. Notice how H:x=y is not new
    and hence not substituted, whereas z = b + x is. *)
  destruct x eqn:heq;intros /sng.
  - apply I.
  - apply I.
Qed.


Import TacNewHyps.Notations.
Import LibHyps.LegacyNotations.

(* This settings should reproduce the naming scheme of libhypps-1.0.0
   and libhypps-1.0.1. *)
Ltac add_suffix ::= constr:(false).
Ltac numerical_names ::= numerical_names_sufx.

Local Open Scope autonaming_scope.
Import ListNotations.

(* From there this is LibHypTest from 1f7a1ed2289e439c291fcbd06c51705547feef1e *)
Ltac rename_hyp_2 n th :=
  match th with
  | true <> false => name(`_tNEQf`)
  | true = false => name(`_tEQf`)
  end.

Ltac rename_hyp ::= rename_hyp_2.

(* Suppose I want to add later another naming rule: *)
Ltac rename_hyp_3 n th :=
  match th with
  | Nat.eqb ?x ?y = true => name(`_Neqb` ++ x#n ++ y#n)
  | true = Nat.eqb ?x ?y => name(`_Neqb` ++ x#n ++ y#n)
  | _ => rename_hyp_2 n th (* call the previously defined tactic *)
  end.

Ltac rename_hyp ::= rename_hyp_3.
Ltac rename_depth ::= constr:(3).

Close Scope Z_scope.
Open Scope nat_scope.
Lemma dummy: forall x y,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
    0 = 1 ->
    (0 = 1)%Z ->
    ~x = y ->
    true = Nat.eqb 3 4  ->
    Nat.eqb 3 4 = true  ->
    true = Nat.leb 3 4  ->
    1 = 0 ->
    ~x = y ->
    ~1 < 0 ->
     (forall w w':nat , w = w' -> ~true=false) ->
     (forall w w':nat , w = w' -> true=false /\ True) ->
     (forall w w':nat , w = w' -> False /\ True) ->
     (exists w:nat , w = w -> ~(true=(andb false true)) /\ False) ->
     (exists w:nat , w = w -> True /\ False) ->
     (forall w w':nat , w = w' -> true=false) ->
     (forall w w':nat , w = w' -> Nat.eqb 3 4=Nat.eqb 4 3) ->
    List.length (cons 3 nil) = (fun x => 0)1 ->
    List.length (cons 3 nil) = 0 ->
    plus 0 y = y ->
    (true=false) ->
    (False -> (true=false)) ->
    forall (x : nat) (env : list nat),
      ~ List.In x nil ->
      cons x (cons 3 env) = cons 2 env ->
    forall z t:nat, IDProp ->
      (0 < 1 -> 0 < 0 -> true = false -> ~(true=false)) ->
      (~(true=false)) ->
      (forall w w',w < w' -> ~(true=false)) ->
      (0 < 1 -> ~(1<0)) ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
  (* auto naming at intro: *)
  !intros.

  match type of x with nat => idtac | _ => fail "test failed!" end.
  match type of y with nat => idtac | _ => fail "test failed!" end.
  match type of h_le_0n_1n with 0 <= 1 => idtac | _ => fail "test failed!" end.
  match type of h_le_0z_1z with (0 <= 1)%Z => idtac | _ => fail "test failed!" end.
  match type of h_le_x_y with x <= y => idtac | _ => fail "test failed!" end.
  match type of h_eq_x_y with x = y => idtac | _ => fail "test failed!" end.
  match type of h_eq_0n_1n with 0 = 1 => idtac | _ => fail "test failed!" end.
  match type of h_eq_0z_1z with 0%Z = 1%Z => idtac | _ => fail "test failed!" end.
  match type of h_neq_x_y with x <> y => idtac | _ => fail "test failed!" end.
  match type of h_Neqb_3n_4n with true = (3 =? 4) => idtac | _ => fail "test failed!" end.
  match type of h_Neqb_3n_4n0 with (3 =? 4) = true => idtac | _ => fail "test failed!" end.
  match type of h_eq_true_leb_3n_4n with true = (3 <=? 4) => idtac | _ => fail "test failed!" end.
  match type of h_eq_1n_0n with 1 = 0 => idtac | _ => fail "test failed!" end.
  match type of h_neq_x_y0 with x <> y => idtac | _ => fail "test failed!" end.
  match type of h_not_lt_1n_0n with ~ 1 < 0 => idtac | _ => fail "test failed!" end.
  match type of h_all_tNEQf with forall w w' : nat, w = w' -> true <> false => idtac | _ => fail "test failed!" end.
  match type of h_all_and_tEQf_True with forall w w' : nat, w = w' -> true = false /\ True => idtac | _ => fail "test failed!" end.
  match type of h_all_and_False_True with forall w w' : nat, w = w' -> False /\ True => idtac | _ => fail "test failed!" end.
  match type of h_ex_and_neq_False with exists w : nat, w = w -> true <> (false && true)%bool /\ False => idtac | _ => fail "test failed!" end.
  match type of h_ex_and_True_False with exists w : nat, w = w -> True /\ False => idtac | _ => fail "test failed!" end.
  match type of h_all_tEQf with forall w w' : nat, w = w' -> true = false => idtac | _ => fail "test failed!" end.
  match type of h_all_eq_eqb_eqb with forall w w' : nat, w = w' -> (3 =? 4) = (4 =? 3) => idtac | _ => fail "test failed!" end.
  match type of h_eq_length_cons with length [3] = (fun _ : nat => 0) 1 => idtac | _ => fail "test failed!" end.
  match type of h_eq_length_cons_0n with length [3] = 0 => idtac | _ => fail "test failed!" end.
  match type of h_eq_add_0n_y_y with 0 + y = y => idtac | _ => fail "test failed!" end.
  match type of h_tEQf with true = false => idtac | _ => fail "test failed!" end.
  match type of h_impl_tEQf with False -> true = false => idtac | _ => fail "test failed!" end.
  match type of x0 with nat => idtac | _ => fail "test failed!" end.
  match type of env with list nat => idtac | _ => fail "test failed!" end.
  match type of h_not_In_x0_nil with ~ In x0 [] => idtac | _ => fail "test failed!" end.
  match type of h_eq_cons_x0_3n_cons_2n with x0 :: 3 :: env = 2 :: env => idtac | _ => fail "test failed!" end.
  match type of h_IDProp with IDProp => idtac | _ => fail "test failed!" end.
  match type of h_impl_tNEQf with 0 < 1 -> 0 < 0 -> true = false -> true <> false => idtac | _ => fail "test failed!" end.
  match type of h_tNEQf with true <> false => idtac | _ => fail "test failed!" end.
  match type of h_all_tNEQf0 with forall w w' : nat, w < w' -> true <> false => idtac | _ => fail "test failed!" end.
  match type of h_impl_not_lt with 0 < 1 -> ~ 1 < 0 => idtac | _ => fail "test failed!" end.
  match type of h_impl_lt_1n_0n with 0 < 1 -> 1 < 0 => idtac | _ => fail "test failed!" end.
  match type of h_lt_0n_z with 0 < z => idtac | _ => fail "test failed!" end.
  exact I.
Qed. 


Definition eq_one (i:nat) := i = 1.
Module AS.


  Lemma foo: (forall x:nat, x = 1 -> (x>0) -> x < 0) -> False.
  Proof.
    intros h.
    especialize h with x at 2.
    + assumption.
    + match type of h_eqone with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.


  Lemma test_espec: forall x:nat, x = 1 -> (x = 1 -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1 .
    + assumption.
    + match type of h_eqone with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.

  Lemma test_espec2: forall x:nat, x = 1 -> (x = 1 -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1 as h.
    + assumption.
    + match type of h with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.

  Lemma test_espec3: forall x:nat, x = 1 -> (x = 1 -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1 as ?.
    + assumption.
    + match type of H with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.

  Lemma test_espec4: forall x:nat, x = 1 -> (x = 1 -> x = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1,2 as ?.
    + assumption.
    + reflexivity.
    + match type of H with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.

  Lemma test_espec5: forall x:nat, x = 1 -> (x = 1 -> x = x -> x = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone at 1,2,3 as ?.
    + assumption.
    + reflexivity.
    + reflexivity.
    + match type of H with
        False => idtac
      | _ => fail "test failed!"
      end.
      contradiction.
  Qed.

  
  Lemma test_espec_h: forall x:nat, x = 1 -> (forall a y z:nat, x = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y at 2,1 as h.
    + reflexivity.
    + assumption.
    + exfalso.
      apply h with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.


  
  Lemma test_espec_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y at 2,1 as ?.
    + reflexivity.
    + reflexivity.
    + exfalso.
      apply H with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  
End AS.


Module Using.

  Lemma test_espec: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y at 2,1 .
    + reflexivity.
    + reflexivity.
    + exfalso.
      apply h_eqone with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  
  Lemma test_espec_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y at 2,1 as h.
    + reflexivity.
    + reflexivity.
    + exfalso.
      apply h with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  
  Lemma test_espec_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y at 2,1 as ?.
    + reflexivity.
    + reflexivity.
    + exfalso.
      apply H with 0.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  

  Lemma test_espec2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y at 2 .
    + reflexivity.
    + exfalso.
      apply h_eqone with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec2_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y at 2 as h.
    + reflexivity.
    + exfalso.
      apply h with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec2_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y at 2 as ?.
    + reflexivity.
    + exfalso.
      apply H with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  

  Lemma test_espec3: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y , z at 2 .
    + reflexivity.
    + exfalso.
      apply h_eqone with 1.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec3_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y , z at 2 as h.
    + reflexivity.
    + exfalso.
      apply h with 1.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec3_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with y , z at 2 as ?.
    + reflexivity.
    + exfalso.
      apply H with 1.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  

  Lemma test_espec4: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a, y, z at 1 .
    + reflexivity.
    + exfalso.
      apply h_eqone.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec4_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a, y, z at 1 as h.
    + reflexivity.
    + exfalso.
      apply h.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec4_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a, y, z at 1 as ?.
    + reflexivity.
    + exfalso.
      apply H.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  
  Lemma test_espec5: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y,z at 1 .
    + reflexivity.
    + exfalso.
      apply h_eqone.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec5_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y,z at 1 as h.
    + reflexivity.
    + exfalso.
      apply h.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec5_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,y,z at 1 as ?.
    + reflexivity.
    + exfalso.
      apply H.
      * reflexivity.
      * instantiate (z:=0). reflexivity.
      * symmetry.
        assumption.
  Qed.
  
  Lemma test_espec6: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a at 1 .
    + reflexivity.
    + exfalso.
      apply h_eqone with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec6_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a at 1 as h.
    + reflexivity.
    + exfalso.
      apply h with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.
  Lemma test_espec6_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a at 1 as ?.
    + reflexivity.
    + exfalso.
      apply H with 1 0.
      * reflexivity.
      * reflexivity.
      * symmetry.
        assumption.
  Qed.

  Lemma test_espec7: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,z at 1,4 .
    + reflexivity.
    + rewrite hx.
      instantiate (z:=0).
      reflexivity.
    + exfalso.
      apply h_eqone with 1.
      * reflexivity.
      * reflexivity.
  Qed.

  Lemma test_espec7_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,z at 1,4 as h.
    + reflexivity.
    + rewrite hx.
      instantiate (z:=0).
      reflexivity.
    + exfalso.
      apply h with 1.
      * reflexivity.
      * reflexivity.
  Qed.
  Lemma test_espec7_h2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    especialize h_eqone with a,z at 1,4 as ?.
    + reflexivity.
    + rewrite hx.
      instantiate (z:=0).
      reflexivity.
    + exfalso.
      apply H with 1.
      * reflexivity.
      * reflexivity.
  Qed.

(* This tests only hold for coq >= 8.18 *)
(*
  Lemma test_espec8: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone with a at 1,4 .
  Abort.

  Lemma test_espec8_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone with a at 1,4 as h.
  Abort.

  Lemma test_espec8_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone with a at 1,4 as ?.
  Abort.

  Lemma test_espec9: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone at 1,4.
  Abort.

  Lemma test_espec9_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone at 1,4 as h.
  Abort.

  Lemma test_espec9_h: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
  Proof.
    intros x hx h_eqone.
    Fail especialize h_eqone at 1,4 as ?.
  Abort.
*)
End Using.


Lemma test_esepec_6_7: (eq_one 2 -> eq_one 3 ->eq_one 4 ->eq_one 5 ->eq_one 6 ->eq_one 7 ->eq_one 8 -> eq_one 9 -> eq_one 1 -> False) -> True.
Proof.
  intros H.
  especialize H at 3,1,4,5,2,7 as h; [ admit | admit | admit  | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> eq_one 1 ->False=> idtac "OK" end].
  Undo.
  especialize H at 3,1,4,5,2,7; [ admit | admit | admit  | admit | admit | admit | match type of H with eq_one 7 -> eq_one 9 -> eq_one 1 ->False=> idtac "OK" end].
  Undo.
  especialize H at 3,1,4,5,2,7,9 as h; [ admit | admit | admit  | admit | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H at 3,1,4,5,2,7,9; [ admit | admit | admit  | admit | admit | admit | admit | match type of H with eq_one 7 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  exact I.
Qed.


Axiom ex_hyp : (forall (b:bool), forall x: nat, eq_one 1 -> forall y:nat, eq_one 2 ->eq_one 3 ->eq_one 4 ->eq_one x ->eq_one 6 ->eq_one y -> eq_one 8 -> eq_one 9 -> False).

Lemma test_esepec: True.
Proof.

  especialize (ex_hyp true) at 2 as h;[ .. | match type of h with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) at 2,3 as h;[  .. | match type of h with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  Fail especialize H at 2,3,5 as h. 
  Undo.
  especialize (ex_hyp true) with x at 2,3,5 as h ;[ ..  | match type of h with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) with x at 2,3,5,6 as h ;[ ..  | match type of h with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  Fail especialize H with x at 2,3,5,7 as h.
  especialize (ex_hyp true) with x,y at 2,3,5,7 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) with x,y at 2,3,5,7,9 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) with x,y at 2,3,1,5,7,9 as h ;[ ..  | match type of h with eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) with x,y at 8,2,3,5,7,9 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac "OK" end].
  Undo.

  especialize (ex_hyp true) at 2 as ?;[ .. | match type of H with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) at 2,3 as ?;[  .. | match type of H with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  Fail especialize H at 2,3,5 as ?. 
  Undo.
  especialize (ex_hyp true) with x at 2,3,5 as ? ;[ ..  | match type of H with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) with x at 2,3,5,6 as ? ;[ ..  | match type of H with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  Fail especialize H with x at 2,3,5,7 as ?.
  especialize (ex_hyp true) with x,y at 2,3,5,7 as ? ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) with x,y at 2,3,5,7,9 as ? ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) with x,y at 2,3,1,5,7,9 as ? ;[ ..  | match type of H with eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize (ex_hyp true) with x,y at 8,2,3,5,7,9 as ? ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac "OK" end].
  Undo.

  Fail especialize (ex_hyp true) at 2.

  Undo.
  generalize (ex_hyp true) as H.
  intro.
  especialize H at 2 as h;[ .. | match type of h with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H at 2,3 as h;[  .. | match type of h with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H at 2,3,5 as h.  *)
  especialize H with x at 2,3,5 as h ;[ ..  | match type of h with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H with x at 2,3,5,6 as h ;[ ..  | match type of h with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H with x at 2,3,5,7 as h. *)
  especialize H with x,y at 2,3,5,7 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H with x,y at 2,3,5,7,9 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize H with x,y at 2,3,1,5,7,9 as h ;[ ..  | match type of h with eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize H with x,y at 8,2,3,5,7,9 as h ;[ ..  | match type of h with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac "OK" end].
  Undo.

  especialize H at 2 as ?;[ .. | match type of H0 with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H at 2,3 as ?;[  .. | match type of H0 with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H at 2,3,5 as ?.  *)
  especialize H with x at 2,3,5 as ? ;[ ..  | match type of H0 with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H with x at 2,3,5,6 as ? ;[ ..  | match type of H0 with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H with x at 2,3,5,7 as ?. *)
  especialize H with x,y at 2,3,5,7 as ? ;[ ..  | match type of H0 with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H with x,y at 2,3,5,7,9 as ? ;[ ..  | match type of H0 with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize H with x,y at 2,3,1,5,7,9 as ? ;[ ..  | match type of H0 with eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize H with x,y at 8,2,3,5,7,9 as ? ;[ ..  | match type of H0 with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac "OK" end].
  Undo.

  especialize H at 2;[ .. | match type of H with forall x: nat, eq_one 1 -> forall y:nat, eq_one 3 -> eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H at 2,3;[  .. | match type of H with forall x: nat, eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H at 2,3,5.  *)
  especialize H with x at 2,3,5 ;[ ..  | match type of H with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one 6 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H with x at 2,3,5,6 ;[ ..  | match type of H with eq_one 1 -> forall y:nat, eq_one 4 -> eq_one _ -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  (* Only for coq >= 8.18 *)
  (* Fail especialize H with x at 2,3,5,7. *)
  especialize H with x,y at 2,3,5,7 ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H with x,y at 2,3,5,7,9 ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize H with x,y at 2,3,1,5,7,9 ;[ ..  | match type of H with eq_one 4 -> eq_one 6 -> eq_one 8 -> False => idtac "OK" end].
  Undo.
  especialize H with x,y at 8,2,3,5,7,9 ;[ ..  | match type of H with eq_one 1 -> eq_one 4 -> eq_one 6 -> False => idtac "OK" end].
  Undo.

  exact I.
Qed.



Lemma test_espec_namings: forall n:nat, (eq_one n -> eq_one 1 -> False) -> True.
Proof.
  intros n h_eqone.
  especialize Nat.quadmul_le_squareadd with a at 1 as hh : h.
  { apply le_n. }
  especialize min_l with n,m at 1 as ?.
  { apply (le_n O). }
  especialize h_eqone at 2 as h1 : h2.
  { reflexivity. }
  unfold eq_one in h2.
  match type of h2 with 1 = 1 => idtac | _ => fail end.
  match type of h1 with eq_one n -> False => idtac | _ => fail end.
  exact I.
Qed.


(* "until i" and "at *" *)

Lemma test_esepec_until_star: (eq_one 2 -> eq_one 3 ->eq_one 4 ->eq_one 5 ->eq_one 6 ->eq_one 7 ->eq_one 8 -> eq_one 9 -> eq_one 1 -> False) -> True.
Proof.
  
  intros h_eqone.
  (* specialize on term ==> create a new hyp *)

  Fail especialize (let x:=not_eq_S in x) with n,m at *.
  especialize (let x:=not_eq_S in x) with n,m at * as h;
    [ .. | match type of h with (S _)<>(S _) => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:=not_eq_S in x) with n,m at * as ?;
    [ .. | match type of H with (S _)<>(S _) => idtac | _ => fail "Test failed!" end].
  Undo.
  Fail especialize (let x:=not_eq_S in x) with n,m until 1.
  especialize (let x:=not_eq_S in x) with n,m at * as h;
    [ .. | match type of h with (S _)<>(S _) => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:=Nat.add_sub_eq_nz in x) with n,m,p until 2 as h;
    [ .. | match type of h with ?m + ?p = ?n => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:= Nat.add_sub_eq_nz in x) with p until 1 as h;
    [ .. | match type of h with forall n m : nat, n - m = ?p -> m + ?p = n => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:=h_eqone in x) at *;
    [ ..  | match type of H_spec with False => idtac | _ => fail "Test failed!" end].
  Undo.
  (* proveprem_until h_eqone 4. *)
  especialize (let x:= h_eqone in x) until 4;
    [ admit |admit |admit |admit | match type of H_spec with eq_one 6 -> eq_one 7 -> eq_one 8 -> eq_one 9 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end ].
  Undo.
  (* behavior when acting on a hypothesis: replace the hyp by its specialize version *)
  especialize h_eqone until 4 ;
    [ admit |admit |admit |admit | match type of h_eqone with eq_one 6 -> eq_one 7 -> eq_one 8 -> eq_one 9 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone at * ;
    [ .. | match type of h_eqone with False => idtac | _ => fail "Test failed!" end].
  Undo.
  (* unless we give the "as" option *)
  especialize h_eqone at * as h ;
    [ admit |admit |admit |admit |admit |admit |admit |admit |admit | match type of h with False => idtac | _ => fail "Test failed!" end;
                                                                      match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 4 -> eq_one 5 -> eq_one 6 -> eq_one 7 -> eq_one 8 -> eq_one 9 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone until 4 as h;
    [ admit |admit |admit |admit | match type of h with eq_one 6 -> eq_one 7 -> eq_one 8 -> eq_one 9 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  exact I.
Qed.

Require Import LibHyps.LibDecomp.

Goal forall l1 l2 l3:list nat, List.length l1 = List.length l2 /\ List.length l1 = List.length l3 -> True.
Proof.

  intros l1 l2 l3 h.
  (* then_allnh_gen ltac:(fun x => all_hyps) ltac:(fun _ => decomp_logicals h)  ltac:(fun lh => idtac lh) . *)

  (* Set Ltac Debug. *)
  decomp_logicals h /sng.
  match goal with
    |- _ => 
    match type of h_eq_length_l1_length_l2 with
      length l1 = length l2 =>  idtac
    | _  => fail "Test failed (wrong type)!"
    end
  | _ => fail "Test failed (wrong name)!"
  end.
  exact I.
Qed.
