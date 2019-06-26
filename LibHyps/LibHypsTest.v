(* Copyright 2017-2019 Pierre Courtieu *)
(* This file is part of LibHyps.

    Foobar is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    Foobar is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with Foobar.  If not, see <https://www.gnu.org/licenses/>.
*)

Require Import Arith ZArith LibHyps.LibHyps LibHyps.LibSpecialize List.



Local Open Scope autonaming_scope.
Import ListNotations.

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
