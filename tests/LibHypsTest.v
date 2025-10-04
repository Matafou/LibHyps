(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

From Coq Require Import Arith ZArith List.
Require Import  LibHyps.LibHyps (*LibHyps.LibSpecialize*).
From Coq Require Import List.

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

Close Scope autonaming_scope.
Close Scope Z_scope.
Open Scope nat_scope.

Ltac test h th :=
  match type of h with
  | th => idtac
  | ?actual => fail "test failed: expected " h ": " th "but got: " h ": " actual
  end.

Ltac testg tg :=
  match goal with
  | |- tg => idtac
  | |- ?actual => fail "test failed: expected goal" tg "but got: " actual
  end.

Lemma test_autorename: forall x y,
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
  intros /n.
  test x nat.
  test y nat.
  test h_le_0_1_ (0 <= 1).
  test h_le_0_1_0 ((0 <= 1)%Z).
  test h_le_x_y_ (x <= y).
  test h_eq_x_y_ (x = y).
  test h_eq_0_1_ (0 = 1).
  test h_eq_0_1_0 (0%Z = 1%Z).
  test h_neq_x_y_ (x <> y).
  test h_Neqb_3_4_ (true = (3 =? 4)).
  test h_Neqb_3_4_0 ((3 =? 4) = true).
  test h_eq_true_leb_3_4_ (true = (3 <=? 4)).
  test h_eq_1_0_ (1 = 0).
  test h_neq_x_y_ (x <> y).
  test h_not_lt_1_0_ (~ 1 < 0).
  test h_all_tNEQf_ (forall w w' : nat, w = w' -> true <> false).
  test h_all_and_tEQf_True_ (forall w w' : nat, w = w' -> true = false /\ True).
  test h_all_and_False_True_ (forall w w' : nat, w = w' -> False /\ True).
  test h_ex_and_neq_False_ (exists w : nat, w = w -> true <> (false && true)%bool /\ False).
  test h_ex_and_True_False_ (exists w : nat, w = w -> True /\ False).
  test h_all_tEQf_ (forall w w' : nat, w = w' -> true = false).
  test h_all_eq_eqb_eqb_ (forall w w' : nat, w = w' -> (3 =? 4) = (4 =? 3)).
  test h_eq_length_cons_ (length [3] = (fun _ : nat => 0) 1).
  test h_eq_length_cons_0_ (length [3] = 0).
  test h_eq_add_0_y_y_ (0 + y = y).
  test h_tEQf_ (true = false).
  test h_impl_tEQf_ (False -> true = false).
  test x0 (nat).
  test env (list nat).
  test h_not_In_x0_nil_ (~ In x0 []).
  test h_eq_cons_x0_3_cons_2_ (x0 :: 3 :: env = 2 :: env).
  test h_IDProp_ (IDProp).
  test h_impl_tNEQf_ (0 < 1 -> 0 < 0 -> true = false -> true <> false).
  test h_tNEQf_ (true <> false).
  test h_all_tNEQf_0 ((forall w w' : nat, w < w' -> true <> false)).
  test h_impl_not_lt_ (0 < 1 -> ~ 1 < 0).
  test h_impl_lt_1_0_ (0 < 1 -> 1 < 0).
  test h_lt_0_z_ (0 < z).
  exact I.
Qed.

Import TacNewHyps.Notations.

Lemma test_autorename_failing: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  (* Fails beause the ((fun f => x = y) true) is not renamable. *)
  Fail intros /n!.
  intros ; { autorename }. (* autorename does not fail if no renaming found *)
  test H ((fun _ : bool => x = y) true).
  auto.
Qed.

Lemma test_autorename_failing2: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros /n. (* /n does not fail, even if a hyp is not renamed *)  
  test x (nat).
  test y (nat).
  test H (((fun _ : bool => x = y) true)).  
  test h_le_0_1_ (0 <= 1).
  test h_le_0_1_0 ((0 <= 1)%Z).
  test h_le_x_y_ (x <= y).
  test h_eq_x_y_ (x = y).
  test h_impl_lt_1_0_ (0 < 1 -> 1 < 0).
  test h_lt_0_z_ (0 < z).
  exact I.
Qed.

Lemma test_rename_or_revert: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros ; { rename_or_revert }.
  testg ((fun _ : bool => x = y) true -> True).
  auto.
Qed.

Lemma test_rename_or_revert2: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros /n?.
  testg ((fun _ : bool => x = y) true -> True).
  test x (nat).
  test y (nat).
  (* Checking that hyps after the failed rename are introduced. *)
  test h_le_0_1_ (0 <= 1).
  test h_le_0_1_0 ((0 <= 1)%Z).
  test h_le_x_y_ (x <= y).
  test h_eq_x_y_ (x = y).
  test h_impl_lt_1_0_ (0 < 1 -> 1 < 0).
  test h_lt_0_z_ (0 < z).
  intro.
  exact I.
Qed.

Lemma test_revertHyp: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  (* Wrong order for revert. *)
  Fail intros ; { revertHyp }.
  intros ; {< revertHyp }.
  testg (forall x y : nat,
            (fun _ : bool => x = y) true ->
            bool ->
            bool ->
            forall z : nat,
              0 <= 1 -> (0 <= 1)%Z -> x <= y -> x = y -> (0 < 1 -> 1 < 0) -> 0 < z -> True).
  intros.
  exact I.
Qed.


(* group_up_list is faster (called on the whole list of new hyps) and should be prefered. *)
Lemma test_group_up_list2: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros ; {! group_up_list }. 
  lazymatch reverse goal with
    | Hb:_, Ha:_,Hz : _ , Hy:_ , Hx:_ |- True =>
      let t := constr:((ltac:(reflexivity)): Hb=b) in
      let t := constr:((ltac:(reflexivity)): Ha=a) in
      let t := constr:((ltac:(reflexivity)): Hz=z) in
      let t := constr:((ltac:(reflexivity)): Hy=y) in
      let t := constr:((ltac:(reflexivity)): Hx=x) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  lazymatch goal with
    | hH1:_, hH2:_,hH3 : _ , hH4:_ , hH5:_ |- True =>
      let t := constr:((ltac:(reflexivity)):H1=hH1) in
      let t := constr:((ltac:(reflexivity)): H2=hH2) in
      let t := constr:((ltac:(reflexivity)): H3=hH3) in
      let t := constr:((ltac:(reflexivity)): H4=hH4) in
      let t := constr:((ltac:(reflexivity)): H5=hH5) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  exact I.
Qed.


Lemma test_group_up_list21: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros /g.
  lazymatch reverse goal with
    | Hb:_, Ha:_,Hz : _ , Hy:_ , Hx:_ |- True =>
      let t := constr:((ltac:(reflexivity)): Hb=b) in
      let t := constr:((ltac:(reflexivity)): Ha=a) in
      let t := constr:((ltac:(reflexivity)): Hz=z) in
      let t := constr:((ltac:(reflexivity)): Hy=y) in
      let t := constr:((ltac:(reflexivity)): Hx=x) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  lazymatch goal with
    | hH1:_, hH2:_,hH3 : _ , hH4:_ , hH5:_ |- True =>
      let t := constr:((ltac:(reflexivity)):H1=hH1) in
      let t := constr:((ltac:(reflexivity)): H2=hH2) in
      let t := constr:((ltac:(reflexivity)): H3=hH3) in
      let t := constr:((ltac:(reflexivity)): H4=hH4) in
      let t := constr:((ltac:(reflexivity)): H5=hH5) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  exact I.
Qed.

(* group_up_list is insensitive to order of hypothesis. It respects
   the respective order of variables in each segment. This has changed
   in version 2.0.5 together with a bug fix.
   Note that the deprecated move_up_types is sensitive to order. *)
Lemma test_group_up_list1_rev: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros ; {!< group_up_list }.
  lazymatch reverse goal with
    | Hb:_, Ha:_,Hz : _ , Hy:_ , Hx:_ |- True =>
      let t := constr:((ltac:(reflexivity)): Hb=b) in
      let t := constr:((ltac:(reflexivity)): Ha=a) in
      let t := constr:((ltac:(reflexivity)): Hz=z) in
      let t := constr:((ltac:(reflexivity)): Hy=y) in
      let t := constr:((ltac:(reflexivity)): Hx=x) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  lazymatch goal with
    | hH1:_, hH2:_,hH3 : _ , hH4:_ , hH5:_ |- True =>
      let t := constr:((ltac:(reflexivity)):H1=hH1) in
      let t := constr:((ltac:(reflexivity)): H2=hH2) in
      let t := constr:((ltac:(reflexivity)): H3=hH3) in
      let t := constr:((ltac:(reflexivity)): H4=hH4) in
      let t := constr:((ltac:(reflexivity)): H5=hH5) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  exact I.
 Qed.

(* Two more tests for the case where the top hyp is Prop-sorted. *)

Lemma test_group_up_list3:
  ((fun f => 0 = 1) true)
  ->
  forall x y:nat,
  forall a b: bool, forall z:nat,
      0 <= 1 ->
      (0%Z <= 1%Z)%Z ->
      x <= y ->
      x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros ; { move_up_types }.
  lazymatch reverse goal with
  | Hb:_, Ha:_,Hz : _ , Hy:_ , Hx:_ |- True =>
    let t := constr:((ltac:(reflexivity)): Hb=b) in
    let t := constr:((ltac:(reflexivity)): Ha=a) in
    let t := constr:((ltac:(reflexivity)): Hz=z) in
    let t := constr:((ltac:(reflexivity)): Hy=y) in
    let t := constr:((ltac:(reflexivity)): Hx=x) in
    idtac
  | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  lazymatch goal with
    | hH1:_, hH2:_,hH3 : _ , hH4:_ , hH5:_ |- True =>
      let t := constr:((ltac:(reflexivity)):H1=hH1) in
      let t := constr:((ltac:(reflexivity)): H2=hH2) in
      let t := constr:((ltac:(reflexivity)): H3=hH3) in
      let t := constr:((ltac:(reflexivity)): H4=hH4) in
      let t := constr:((ltac:(reflexivity)): H5=hH5) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  exact I.
Qed.



Lemma test_group_up_list2_rev: 
  ((fun f => 0 = 1) true)
  ->
  forall x y:nat,
  forall a b: bool, forall z:nat,
      0 <= 1 ->
      (0%Z <= 1%Z)%Z ->
      x <= y ->
      x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros ; {< move_up_types }.
  lazymatch reverse goal with
  | Ha:_, Hb:_,Hx : _ , Hy:_ , Hz:_ |- True =>
    let t := constr:((ltac:(reflexivity)): Hb=b) in
    let t := constr:((ltac:(reflexivity)): Ha=a) in
    let t := constr:((ltac:(reflexivity)): Hz=z) in
    let t := constr:((ltac:(reflexivity)): Hy=y) in
    let t := constr:((ltac:(reflexivity)): Hx=x) in
    idtac
  | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  lazymatch goal with
    | hH1:_, hH2:_,hH3 : _ , hH4:_ , hH5:_ |- True =>
      let t := constr:((ltac:(reflexivity)):H1=hH1) in
      let t := constr:((ltac:(reflexivity)): H2=hH2) in
      let t := constr:((ltac:(reflexivity)): H3=hH3) in
      let t := constr:((ltac:(reflexivity)): H4=hH4) in
      let t := constr:((ltac:(reflexivity)): H5=hH5) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  exact I.
Qed.

(* Test for substHyp, the order in which subst are done *)

Lemma test_subst: 
  ((fun f => 0 = 1) true)
  ->
  forall x y:nat,
  forall a b: bool, forall z:nat,
      0 <= 1 ->
      x = z ->
      (0%Z <= 1%Z)%Z ->
      x <= y ->
      x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros ; { substHyp }.
  (* x = z is subst first, and y = y remains *)
  lazymatch reverse goal with
  | H: y <= y |- True => idtac
  | _ => fail "test failed!"
  end.
  exact I.
Qed.

(* Checking the chaining of operators. *)
Lemma test_group_up_after_subst: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  intros ; { subst_or_idtac } ; {! group_up_list }.
  lazymatch reverse goal with
  | Hb:_, Ha:_,Hz:_ , Hy:_ |- True =>
    let t := constr:((ltac:(reflexivity)): Hb=b) in
    let t := constr:((ltac:(reflexivity)): Ha=a) in
    let t := constr:((ltac:(reflexivity)): Hz=z) in
    let t := constr:((ltac:(reflexivity)): Hy=y) in
    idtac
  | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  lazymatch goal with
    | hH0:_,hH1:_, hH2:_, hH4:_ , hH5:_ |- True =>
      let t := constr:((ltac:(reflexivity)): H0=hH0) in
      let t := constr:((ltac:(reflexivity)):H1=hH1) in
      let t := constr:((ltac:(reflexivity)): H2=hH2) in
      let t := constr:((ltac:(reflexivity)): H4=hH4) in
      let t := constr:((ltac:(reflexivity)): H5=hH5) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  exact I.
Qed.


Ltac substHyp H ::=
  match type of H with
  | Depl => fail 1 (* fail immediately, we are applying on a list of hyps. *)
  | ?x = ?y =>
    (* subst would maybe subst using another hyp, so use replace to be sure *)
    once ((is_var(x); replace x with y in *; [try clear x ; try clear H] )
          + (is_var(y);replace y with x in * ; [ try clear H]))
  | _ => idtac
  end.


(* Legacy Notations tac ;!; tac2. *)
Lemma test_tactical_semi: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  (* move_up_types is there for backward compatibility. It moves Type-Sorted hyps up. *)
  intros ;; move_up_types.
  lazymatch reverse goal with
    | Hb:_, Ha:_,Hz : _ , Hy:_ , Hx:_ |- True =>
      let t := constr:((ltac:(reflexivity)): Hb=b) in
      let t := constr:((ltac:(reflexivity)): Ha=a) in
      let t := constr:((ltac:(reflexivity)): Hz=z) in
      let t := constr:((ltac:(reflexivity)): Hy=y) in
      let t := constr:((ltac:(reflexivity)): Hx=x) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  lazymatch goal with
    | hH1:_, hH2:_,hH3 : _ , hH4:_ , hH5:_ |- True =>
      let t := constr:((ltac:(reflexivity)): H1=hH1) in
      let t := constr:((ltac:(reflexivity)): H2=hH2) in
      let t := constr:((ltac:(reflexivity)): H3=hH3) in
      let t := constr:((ltac:(reflexivity)): H4=hH4) in
      let t := constr:((ltac:(reflexivity)): H5=hH5) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  auto.
Qed.

(* Legacy Notations tac ;; tac2. *)
Lemma test_tactical_semi_rev: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z u:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  (* move_up_types is there for backward compatibility. It moves Type-Sorted hyps up. *)
  intros ;!; move_up_types.
  lazymatch reverse goal with
    | Ha:_, Hb:_, Hz: _ , Hu : _ , Hy:_ , Hx:_ |- True =>
      let t := constr:((ltac:(reflexivity)): Hb=b) in
      let t := constr:((ltac:(reflexivity)): Ha=a) in
      let t := constr:((ltac:(reflexivity)): Hu=u) in
      let t := constr:((ltac:(reflexivity)): Hz=z) in
      let t := constr:((ltac:(reflexivity)): Hy=y) in
      let t := constr:((ltac:(reflexivity)): Hx=x) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  lazymatch goal with
    | hH1:_, hH2:_,hH3 : _ , hH4:_ , hH5:_ |- True =>
      let t := constr:((ltac:(reflexivity)): H1=hH1) in
      let t := constr:((ltac:(reflexivity)): H2=hH2) in
      let t := constr:((ltac:(reflexivity)): H3=hH3) in
      let t := constr:((ltac:(reflexivity)): H4=hH4) in
      let t := constr:((ltac:(reflexivity)): H5=hH5) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  auto.
Qed.


(* Legacy Notations !!!!tac. *)
Import LibHyps.LegacyNotations.
Lemma test_group_up_list_legacy: forall x y:nat,
    ((fun f => x = y) true)
    -> forall a b: bool, forall z:nat,
    0 <= 1 ->
    (0%Z <= 1%Z)%Z ->
    x <= y ->
    x = y ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
Proof.
  (* move_up_types is there for backward compatibility. It moves Type-Sorted hyps up. *)
  !!!!intros.
  lazymatch reverse goal with
    | Hb:_, Ha:_,Hz : _ , Hy:_  |- True =>
      let t := constr:((ltac:(reflexivity)): Hb=b) in
      let t := constr:((ltac:(reflexivity)): Ha=a) in
      let t := constr:((ltac:(reflexivity)): Hz=z) in
      let t := constr:((ltac:(reflexivity)): Hy=y) in
      (* let t := constr:((ltac:(reflexivity)): Hx=x) in *)
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  lazymatch goal with
    | hH1:_, hH2:_,hH3 : _ , hH4:_ , hH5:_ |- True =>
      let t := constr:((ltac:(reflexivity)): h_le_0_1_=hH1) in
      let t := constr:((ltac:(reflexivity)): h_le_0_1_0=hH2) in
      let t := constr:((ltac:(reflexivity)): h_le_y_y_=hH3) in
      let t := constr:((ltac:(reflexivity)): h_impl_lt_1_0_=hH4) in
      let t := constr:((ltac:(reflexivity)): h_lt_0_z_=hH5) in
      idtac
    | _ => fail "test failed (wrong order of hypothesis)!"
  end.
  auto.
Qed.



(* This is supposed to be copy-pasted in README.md *)
Lemma foo: forall x y z:nat,
    x = y -> forall  a b t : nat, a+1 = t+2 -> b + 5 = t - 7 ->  (forall u v, v+1 = 1 -> u+1 = 1 -> a+1 = z+2)  -> z = b + x-> True.
Proof.
  intros.
  (* ugly names *)
  Undo.
  (* Example of using the iterator on new hyps: this prints each new hyp name. *)
  (*intros; {fun h => idtac h}.
    Undo.*)
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
  (* BROKEN IN COQ 8.18 *)
  (* especialize h_all_eq_add_add_ at 2.
  { apply Nat.add_0_l. }
  (* now h_all_eq_add_add is specialized *)
  Undo 6. *)
  Undo 2.
  intros until 1.
  (** The taticals apply after any tactic. Notice how H:x=y is not new
    and hence not substituted, whereas z = b + x is. *)
  destruct x eqn:heq;intros /sng.
  - apply I.
  - apply I.
Qed.



(* Stressing the system with big goals *)
Import TacNewHyps.Notations.
Lemma foo':
  forall (_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          : (forall (_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                     :nat), True))
                  (a b:bool), True -> forall y z:nat, True.
  (* Time intros. (* .07s *) *)
  (* Time intros; { fun x => idtac x}. (* 1,6s *) *)
  Time intros /g. (* 3s *)
  (* Time intros ; { move_up_types }. (* ~7mn *) *)
  (* Time intros /n. (* 19s *) *)
exact I.
Qed.
