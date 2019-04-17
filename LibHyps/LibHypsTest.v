
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
  | Nat.eqb ?x ?y = _ => name(`_Neqb` ++ x#n ++ x#n)
  | _ = Nat.eqb ?x ?y => name(`_Neqb` ++ x#n ++ x#n)
  | _ => rename_hyp_2 n th (* call the previously defined tactic *)
  end.

Ltac rename_hyp ::= rename_hyp_3.

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
  Check x : nat.
  Check y : nat.
  Check   h_le_0N_1N : 0 <= 1.
  Check   h_le_0Z_1Z : (0 <= 1)%Z.
  Check h_le_x_y : x <= y.
  Check h_eq_x_y : x = y.
  Check   h_eq_0N_1N : 0 = 1.
  Check h_eq_0Z_1Z : 0%Z = 1%Z.
  Check h_n_eq_x_y : x <> y.
  Check h_Neqb_3N_3N : true = (3 =? 4).
  Check h_Neqb_3N_3N0 : (3 =? 4) = true.
  Check h_eq_true_leb : true = (3 <=? 4).
  Check h_eq_1N_0N : 1 = 0.
  Check h_n_eq_x_y0 : x <> y.
  Check h_n_lt_1N_0N : ~ 1 < 0.
  Check h_all_tNEQf : forall w w' : nat, w = w' -> true <> false.
  Check h_all_and_tEQf_True : forall w w' : nat, w = w' -> true = false /\ True.
  Check h_all_and_False_True : forall w w' : nat, w = w' -> False /\ True.
  Check h_ex_and_n_eq_False : exists w : nat, w = w -> true <> (false && true)%bool /\ False.
  Check   h_ex_and_True_False : exists w : nat, w = w -> True /\ False.
  Check h_all_tEQf : forall w w' : nat, w = w' -> true = false.
  Check h_all_Neqb_3N_3N : forall w w' : nat, w = w' -> (3 =? 4) = (4 =? 3).
  Check h_eq_length : length [3] = (fun _ : nat => 0) 1.
  Check h_eq_length0_0N : length [3] = 0.
  Check h_eq_add_y : 0 + y = y.
  Check h_tEQf : true = false.
  Check h_impl_tEQf : False -> true = false.
  Check x0 : nat.
  Check env : list nat.
  Check h_n_In_nat_x0_nil : ~ In x0 [].
  Check h_eq_cons_x0_3N_cons_2N : x0 :: 3 :: env = 2 :: env.
  Check z.
  Check t : nat.
  Check h_IDProp : IDProp.
  Check h_impl_tNEQf : 0 < 1 -> 0 < 0 -> true = false -> true <> false.
  Check h_tNEQf : true <> false.
  Check h_all_tNEQf0 : forall w w' : nat, w < w' -> true <> false.
  Check h_impl_n_lt : 0 < 1 -> ~ 1 < 0.
  Check h_impl_lt_1N_0N : 0 < 1 -> 1 < 0.
  Check h_lt_0N_z : 0 < z.
  exact I.
Qed.
