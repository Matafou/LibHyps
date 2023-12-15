(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

Require Import Arith ZArith LibHyps.LibHyps LibHyps.LibSpecialize List.


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


(* BROKEN IN 8.18 *)
(*
Definition eq_one (i:nat) := i = 1.
(* eq_one is delta_reducible but I don't want it to be reduced. *)
Lemma test_espec: (eq_one 2 -> eq_one 3 -> eq_one 1 -> False) -> True.
Proof.
  intros h_eqone.
  (* let nme := fresh_robust H "hh" "def" in idtac nme.Definition *)

  especialize h_eqone as newH at 2;
    [ admit | match type of newH with eq_one 2 -> eq_one 1 -> False => idtac end;
              match type of h_eqone with  eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac end].
  Undo.
  especialize h_eqone at 2 as newH;
    [ admit | match type of newH with eq_one 2 -> eq_one 1 -> False => idtac end;
              match type of h_eqone with  eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2 as hhh;
    [ admit | match type of hhh with _ <= _ -> _ = _ => idtac | _ => fail "Test failed!" end ].
  Undo.

  especialize (let x:=Nat.le_antisymm in x)as hhh at 2;
    [ admit | match type of hhh with _ <= _ -> _ = _ => idtac | _ => fail "Test failed!" end ].
  Undo.

  especialize h_eqone at 2;
    [ admit | match type of h_eqone with eq_one 2 -> eq_one 1 -> False => idtac end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2;
    [ admit | match goal with |- (_ <= _ -> _ = _) -> True => idtac | _ => fail "Test failed!" end ].
  Undo.

  especialize h_eqone as ? at 2;
    [ admit | match type of h_eqone_spec with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone at 2 as ? ;
    [ admit | match type of h_eqone_spec with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  
  especialize (let x:=Nat.le_antisymm in x) as ? at 2;
    [ admit | match type of H_spec with _ <= _ -> _ = _ => idtac | _ => fail "Test failed!" end;
              match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2 as ? ;
    [ admit | match type of H_spec with _ <= _ -> _ = _ => idtac | _ => fail "Test failed!" end;
              match type of h_eqone with eq_one 2 -> eq_one 3 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone at 2 : h;
    [ admit | match type of h_eqone with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h with 3=1 => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2 : h;
    [ admit | match goal with |- (_ <= _ -> _ = _) -> True => idtac | _ => fail "Test failed!" end;
              match type of h with _ <= _ => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone at 2 : ? ;
    [ admit | match type of h_eqone with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h_eqone_prem with 3=1 => idtac | _ => fail "Test failed!" end].
  Undo. 

  especialize (let x:=Nat.le_antisymm in x) at 2 : ? ;
    [ admit | match goal with |- (_ <= _ -> _ = _) -> True => idtac | _ => fail "Test failed!" end;
              match type of H_prem with _ <= _ => idtac | _ => fail "Test failed!" end].
  Undo.


  especialize h_eqone at 2 as newH : h;
    [ admit | match type of newH with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h with 3=1 => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2 as newH : h;
    [ admit | match type of newH with (_ <= _ -> _ = _) => idtac | _ => fail "Test failed!" end;
              match type of h with _ <= _ => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone as newH at 2 : h;
    [ admit | match type of newH with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h with 3=1 => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) as newH at 2 : h;
    [ admit |
      match type of newH with (_ <= _ -> _ = _) => idtac | _ => fail "Test failed!" end;
      match type of h with _ <= _ => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone at 2 as ? : h;
    [ admit | match type of h_eqone_spec with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h with 3=1 => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2 as ? : h;
    [ admit |
      match type of H_spec with (_ <= _ -> _ = _) => idtac | _ => fail "Test failed!" end;
      match type of h with _ <= _ => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone as ? at 2 : h;
    [ admit | match type of h_eqone_spec with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h with 3=1 => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) as ? at 2 : h;
    [ admit |
      match type of H_spec with (_ <= _ -> _ = _) => idtac | _ => fail "Test failed!" end;
      match type of h with _ <= _ => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone at 2 as ? : ? ;
    [ admit | match type of h_eqone_spec with eq_one 2 -> eq_one 1 -> False => idtac | _ => fail "Test failed!" end;
              match type of h_eqone_prem with 3=1 => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2 as ? : ? ;
    [ admit |
      match type of H_spec with (_ <= _ -> _ = _) => idtac | _ => fail "Test failed!" end;
      match type of H_prem with _ <= _ => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone as ? at 2 : ? ;
    [ admit | match goal with h_eqone_spec:eq_one 2 -> eq_one 1 -> False,
                              h_eqone_prem : 3 = 1 |- _ => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) as ? at 2 : ? ;
    [ admit |
      match type of H_spec with (_ <= _ -> _ = _) => idtac | _ => fail "Test failed!" end;
      match type of H_prem with _ <= _ => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone at 2,3;
    [ admit | admit| match type of h_eqone with eq_one 2 -> False=> idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 1,2;
    [ admit | admit | match goal with |- (_ = _) -> True => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone at 3,2;
    [ admit | admit| match type of h_eqone with eq_one 2 -> False=> idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2,1;
    [ admit | admit | match goal with |- (_ = _) -> True => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone as h at 2,3;
    [ admit | admit| match type of h with eq_one 2 -> False=> idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) at 2,1 as h;
    [ admit | admit | 
      match type of h with (_ = _) => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone at 2,3 as h;
    [ admit | admit| match type of h with eq_one 2 -> False=> idtac | _ => fail "Test failed!" end].
  Undo.

  especialize (let x:=Nat.le_antisymm in x) as h at 2,1;
    [ admit | admit | 
      match type of h with (_ = _) => idtac | _ => fail "Test failed!" end].
  Undo.

  especialize h_eqone at 3,2,1;
    [ admit | admit | admit |  match type of h_eqone with False=> idtac | _ => fail "Test failed!" end ].
  Undo.

  especialize h_eqone as h at 3,2,1;
    [ admit | admit | admit |  match type of h with False=> idtac | _ => fail "Test failed!" end ].
  Undo.

  especialize h_eqone at 3,2,1 as h;
    [ admit | admit | admit |  match type of h with False=> idtac | _ => fail "Test failed!" end ].
  Undo.
  exact I.
Qed.

Lemma foo2: (eq_one 2 -> eq_one 3 ->eq_one 4 ->eq_one 5 ->eq_one 6 -> eq_one 1 -> False) -> True.
Proof.
  intros h_eqone.
  especialize h_eqone at 3,1,4,5 as h;
    [ admit | admit | admit  | admit | match type of h with eq_one 3 -> eq_one 1 ->False=> idtac | _ => fail "Test failed!" end  ]. 
  Undo.
  especialize h_eqone as h at 3,1,4,5;
    [ admit | admit | admit  | admit | match type of h with eq_one 3 -> eq_one 1 ->False=> idtac | _ => fail "Test failed!" end  ]. 
  Undo.
  especialize h_eqone at 3,1,4,5;
    [ admit | admit | admit  | admit | match type of h_eqone with eq_one 3 -> eq_one 1 ->False=> idtac | _ => fail "Test failed!" end  ]. 
  Undo.
  especialize h_eqone at 3,1,4,5,2;
    [ admit | admit | admit | admit  | admit | match type of h_eqone with eq_one 1 ->False=> idtac | _ => fail "Test failed!" end  ]. 
  Undo.
  especialize h_eqone at 3,1,4,5,2  as h;
    [ admit | admit | admit | admit  | admit | match type of h with eq_one 1 ->False=> idtac | _ => fail "Test failed!" end  ]. 
  Undo.
  especialize h_eqone as h at 3,1,4,5,2;
    [ admit | admit | admit | admit  | admit | match type of h with eq_one 1 ->False=> idtac | _ => fail "Test failed!" end  ]. 
  Undo.
  exact I.
Qed.


Lemma test_espec_namings: forall n:nat, (eq_one n -> eq_one 1 -> False) -> True.
Proof.
  intros n h_eqone.
  especialize Nat.quadmul_le_squareadd at 1 as hh : h.
  { apply le_n. }
  especialize min_l at 1 as ? : ?.
  { apply (le_n O). }
  especialize h_eqone at 2 as h1 : h2.
  { reflexivity. }
  match type of h2 with 1 = 1 => idtac | _ => fail end.
  match type of h1 with eq_one n -> False => idtac | _ => fail end.
  exact I.
Qed.

Lemma test_esepec_6_7: (eq_one 2 -> eq_one 3 ->eq_one 4 ->eq_one 5 ->eq_one 6 ->eq_one 7 ->eq_one 8 -> eq_one 9 -> eq_one 1 -> False) -> True.
Proof.
  intros h_eqone.
  especialize h_eqone at 3,1,4,5,2,7 as h;
    [ admit | admit | admit  | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> eq_one 1 ->False=> idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone as h at 3,1,4,5,2,7;
    [ admit | admit | admit  | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> eq_one 1 ->False=> idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone at 3,1,4,5,2,7;
    [ admit | admit | admit  | admit | admit | admit | match type of h_eqone with eq_one 7 -> eq_one 9 -> eq_one 1 ->False=> idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone at 3,1,4,5,2,7,9 as h;
    [ admit | admit | admit  | admit | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone as h at 3,1,4,5,2,7,9;
    [ admit | admit | admit  | admit | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize h_eqone at 3,1,4,5,2,7,9;
    [ admit | admit | admit  | admit | admit | admit | admit | match type of h_eqone with eq_one 7 -> eq_one 9 -> False => idtac | _ => fail "Test failed!" end].
  Undo.
  exact I.
Qed.

(* "until i" and "at *" *)

Lemma test_esepec_until_star: (eq_one 2 -> eq_one 3 ->eq_one 4 ->eq_one 5 ->eq_one 6 ->eq_one 7 ->eq_one 8 -> eq_one 9 -> eq_one 1 -> False) -> True.
Proof.
  
  intros h_eqone.
  (* specialize on term ==> create a new hyp *)
  especialize (let x:=not_eq_S in x) at *;
    [ intro ; admit | match type of H_spec with (S _)<>(S _) => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:=not_eq_S in x) at * as h;
    [ intro ; admit | match type of h with (S _)<>(S _) => idtac | _ => fail "Test failed!" end].
  Undo.
  especialize (let x:=h_eqone in x) at *;
    [ admit |admit |admit |admit |admit |admit |admit |admit |admit | match type of H_spec with False => idtac | _ => fail "Test failed!" end].
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
    [ admit |admit |admit |admit |admit |admit |admit |admit |admit | match type of h_eqone with False => idtac | _ => fail "Test failed!" end].
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
*)

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
