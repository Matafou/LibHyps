(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)


Require Export LibHyps.TacNewHyps.
Require Export LibHyps.LibHypsNaming.
Require Export LibHyps.LibHyps.
Export TacNewHyps.Notations.
Require Import Arith ZArith List.
Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr Printf.
Local Set Default Proof Mode "Classic".
Import ListNotations.

Import LibHyps.LegacyNotations.

(* This settings should reproduce the naming scheme of libhypps-1.0.0
   and libhypps-1.0.1. *)
Ltac2 Set numerical_sufx := true.
Ltac2 Set add_suffix := false.

Ltac2 rename_hyp_1 n th :=
    if Int.lt n 0 then []
    else
      lazy_match! th with
      | @cons _ ?x (cons ?y ?l) => [String "cons"; Rename x; Rename y; RenameN (decr (decr n)) l]
      | @cons _ ?x ?l => if Int.ge n 1 then [String "cons"; Rename x; RenameN (decr n) l] else [String "cons"]
      end.

Ltac2 rename_hyp_2 n th :=
  match! th with
  | true <> false => [ String "tNEQf" ]
  | true = false => [ String "tEQf"]
  | _ => rename_hyp_1 n th (* call the previously defined tactic *)
  end.

Ltac2 Set rename_hyp := rename_hyp_2.

Ltac2 rename_hyp_3 n th :=
  match! th with
  | Nat.eqb ?x ?y = true => [ String "Neqb" ; Rename x ; Rename y ]
  | true = Nat.eqb ?x ?y => [ String "Neqb" ; Rename x ; Rename y ]
  | _ => rename_hyp_2 n th (* call the previously defined tactic *)
  end.

Ltac2 Set rename_hyp := rename_hyp_3.

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
    Nat.eqb (x + 1) 0 <> Nat.eqb 1 y ->
    true = Nat.eqb 3 4  ->
    Nat.eqb (x + 3) 4 = true  ->
    Nat.eqb (2 * (x + 3)) 4 = true  ->
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
  match type of h_Neqb_mul_2n_add_4n with (2 * (x + 3) =? 4) = true => idtac | _ => fail "test failed!" end.
  match type of h_eq_true_leb_3n_4n with true = (3 <=? 4) => idtac | _ => fail "test failed!" end.
  match type of h_eq_1n_0n with 1 = 0 => idtac | _ => fail "test failed!" end.
  match type of h_neq_x_y0 with x <> y => idtac | _ => fail "test failed!" end.
  match type of h_neq_eqb_add_0n_eqb_1n_y with  (x + 1 =? 0) <> (1 =? y) => idtac | _ => fail "test failed!" end.
  match type of h_not_lt_1n_0n with ~ 1 < 0 => idtac | _ => fail "test failed!" end.
  match type of h_all_tNEQf with forall w w' : nat, w = w' -> true <> false => idtac | _ => fail "test failed!" end.
  match type of h_all_and_tEQf_True with forall w w' : nat, w = w' -> true = false /\ True => idtac | _ => fail "test failed!" end.
  match type of h_all_and_False_True with forall w w' : nat, w = w' -> False /\ True => idtac | _ => fail "test failed!" end.
  match type of h_ex_and_neq_False with exists w : nat, w = w -> true <> (false && true)%bool /\ False => idtac | _ => fail "test failed!" end.
  match type of h_ex_and_True_False with exists w : nat, w = w -> True /\ False => idtac | _ => fail "test failed!" end.
  match type of h_all_tEQf with forall w w' : nat, w = w' -> true = false => idtac | _ => fail "test failed!" end.
  match type of h_all_eq_eqb_eqb with forall w w' : nat, w = w' -> (3 =? 4) = (4 =? 3) => idtac | _ => fail "test failed!" end.
  match type of h_eq_length_cons with (length [3] = (fun _ : nat => 0) 1) => idtac | _ => fail "test failed!" end.
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

  Restart.
  intros /ng.
  lazymatch reverse goal with
  | Ht:_,Hz:_, Hx0:_,Hy:_ , Hx:_ |- True =>
    let _ := constr:((ltac:(reflexivity)): Hx=x) in
    let _ := constr:((ltac:(reflexivity)): Hy=y) in
    let _ := constr:((ltac:(reflexivity)): Hx0=x0) in
    let _ := constr:((ltac:(reflexivity)): Ht=t) in
    idtac
  | _ => fail "test failed (wrong order of hypothesis)!"
  end.

  Restart.
  intros /sng.
  lazymatch reverse goal with
  | Ht:_,Hz:_, Hx0:_,Hy:_ |- True =>
    let _ := constr:((ltac:(reflexivity)): Hy=y) in
    let _ := constr:((ltac:(reflexivity)): Hx0=x0) in
    let _ := constr:((ltac:(reflexivity)): Ht=t) in
    idtac
  | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  
  exact I.
Qed. 



Definition eq_one (i:nat) := i = 1.
Lemma test_espec_namings: forall n:nat, (forall m, eq_one n -> eq_one 1 -> eq_one m -> m = n) -> True.
Proof.
  intros n h_eqone.
  especialize Nat.quadmul_le_squareadd with a at 1 as hh (*: h*).
  { apply le_n. }
  especialize min_l with n,m at 1 as ?.
  { apply (le_n O). }
  especialize h_eqone at 3 as h1 (*: h2 *).
  { admit. }
  (* unfold eq_one in h2. *)
  (* match type of h2 with 1 = 1 => idtac | _ => fail end. *)
  match type of h1 with forall m : nat, eq_one n -> eq_one 1 -> m = n => idtac | _ => fail end.
  exact I.
Abort.


Ltac2 rename_hyp_4 n th :=
  match! th with
  | length ?l => [ String "lgth" ; Rename l ]
  | _ => rename_hyp_3 n th (* call the previously defined tactic *)
  end.

Ltac2 Set rename_hyp := rename_hyp_4.

Ltac2 Set rename_depth := 3.

Goal forall l1 l2 l3:list nat, List.length l1 = List.length l2 /\ List.length l1 = List.length l3 -> True.
Proof.

  intros l1 l2 l3 ?/n.
  (* then_allnh_gen ltac:(fun x => all_hyps) ltac:(fun _ => decomp_logicals h)  ltac:(fun lh => idtac lh) . *)

  (* Set Ltac Debug. *)
  decomp_logicals h_and_eq_lgth_lgth_eq_lgth_lgth /sn.
  match goal with
    |- _ => 
    match type of h_eq_lgth_l1_lgth_l2 with
      length l1 = length l2 =>  idtac
    | _  => fail "Test failed (wrong type)!"
    end
  | _ => fail "Test failed (wrong name)!"
  end.
  exact I.
Qed.

(* example of new tactical from the documentation. *)
Tactic Notation "!!!" tactic3(Tac) := Tac ;{ substHyp } ;{< rename_or_revert }; { autorename}.

Lemma foo: forall x y z:nat,
    x = y -> forall  a b t : nat, a+1 = t+2 -> b + 5 = t - 7 ->  (forall u v, v+1 = 1 -> u+1 = 1 -> a+1 = z+2) -> (fun x => x <= 0) 0 -> z = b + x-> True.
Proof.
  !!!intros.
  match goal with
  | |- (0 <= 0) -> True => idtac
  end.
  match type of h_eq_add_a_1n_add_t_2n with
  | a + 1 = t + 2 =>  idtac
  end.

Abort.
