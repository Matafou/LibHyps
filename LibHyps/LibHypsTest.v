
Require Import Arith ZArith LibHyps.LibHyps LibHyps.LibSpecialize.

(* Typical use, subst with all hyps created by inversion, and move
Type-sorted hyps to the top of the goal:

inversion H ;; subst_or_move_up.

  See also LibHypsNaming.v for a generic tactic for auto naming new
  hypothesis. *)

(* Examples of use: *)

Lemma foo: forall x y:nat,
    x = y -> forall  a t : nat, a+1 = t+2 ->forall u v, u+1 = v -> a+1 = t+2 -> True.
Proof.
  intros.
  (* try to move all hyps with types in Type: *)
  onAllHyps move_up_types.
  Undo.
  (* subst or revert all hypothesis (older first) *)
  onAllHyps subst_or_revert.
  Undo.
  (* in the othe other order: *)
  onAllHypsRev subst_or_revert.
  Undo 2.
  intros until 1.
  (* Do subst on new hyps only, notice how x=y remains (as 0 = y). *)
  (destruct x eqn:heq;intros);; substHyp.
  match goal with
  | H: 0 = y |- _ => idtac
  end.
  Undo 2.
  (* same + move up new hyps of Sort Type *)
  (destruct x eqn:heq;intros) ;; (fun h => substHyp h || move_up_types h).
  match goal with
  | H: 0 = y |- _ => idtac
  end.
  Undo 2.
  (* First attempt to revert all new hyps: wrong order *)
  (destruct x eqn:heq;intros) ;; revertHyp.
  Undo.
  (* Works better if we go in reverse order: *)
  (destruct x eqn:heq;intros) ;!; revertHyp.
  Undo.
  (* revert every new hyp except if subst can remove the hyp *)
  (destruct x eqn:heq;intros) ;!; subst_or_revert.
  Undo.
  intros.
  apply I.
Qed.

(* Example of tactic notations to define shortcuts: =tac means "apply
   tac and try subst on all created hypothesis" *)
Local Tactic Notation "=" tactic3(Tac) := Tac ;!; substHyp.

Lemma bar: forall x y a t u v : nat,
    x = v -> a = t -> u = x -> u = y -> x = y.
Proof.
  =intros.
  Undo.
  intros.
  =destruct x eqn:heq.
  - subst;auto.
  - subst;auto.
Abort.


(* Example of tactic notations to define shortcuts: =tac means "apply
   tac and reverts all created hypothesis" *)
Local Tactic Notation "<=" tactic3(Tac) := Tac ;!; revertHyp.

Lemma bar: forall x y a t u v : nat,
    x = v -> a = t -> u = x -> u = y -> x = y.
Proof.
  intros.
  <=destruct x eqn:heq.
  - intros;subst;auto.
  - intros;subst;auto.
Qed.



(* Another exampe: =tac means "apply
   tac and try subst on all created hypothesis, revert when subst fails" *)
Local Tactic Notation "<-" tactic3(Tac) := Tac ;!; subst_or_revert.

Lemma bar': forall x y a t u v : nat,
    x < v -> a = t -> u > x -> u = y -> x < y.
Proof.
  <-intros.
  (* Some variable (ones on which subst worked) are not reverted *)
Admitted.

Definition test n := n = 1.
Variable Q: nat -> bool -> list nat -> Prop.

Lemma foo':
  (forall n b l, b = true -> test n -> Q n b l) ->
  Q 1 true (cons 1 nil).
Proof.
  intro hyp.
  especialize hyp at 2 as h.
  { reflexivity. }
  apply hyp.
  reflexivity.
Qed.




Ltac rename_hyp_2 h th :=
  match th with
  | true = false => fresh "trueEQfalse"
  end.

Ltac rename_hyp ::= rename_hyp_2.

(* Suppose I want to add later another naming rule: *)
Ltac rename_hyp_3 h th :=
  match th with
  | Nat.eqb ?x ?y = _ => fresh "Nateqb"
  | _ = Nat.eqb ?x ?y => fresh "Nateqb"
  | _ => rename_hyp_2 h th (* call the previously defined tactic *)
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
     (forall w w':nat , w = w' -> true=false) -> 
     (forall w w':nat , w = w' -> Nat.eqb 3 4=Nat.eqb 4 3) -> 
    List.length (cons 3 nil) = (fun x => 0)1 ->
    List.length (cons 3 nil) = 0 ->
    plus 0 y = y ->
    (true=false) ->
    (False -> (true=false)) ->
    forall z t:nat, IDProp ->
      (0 < 1 -> 0 < 0 -> true = false -> ~(true=false)) ->
      (~(true=false)) ->
      (forall w w',w < w' -> ~(true=false)) ->
      (0 < 1 -> ~(1<0)) ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
  (* auto naming at intro: *)
  !intros.
  Check x:nat.
  Check y : nat.
  Check h_le_0_1 : 0 <= 1.
  Check h_le_0_0 : (0 <= 1)%Z.
  Check h_le_x_y : x <= y.
  Check h_eq_x_y : x = y.
  Check h_eq_0_1 : 0 = 1.
  Check h_eq_0_0 : 0%Z = 1%Z.
  Check h_neq_x_y : x <> y.
  Check h_Nateqb : true = (3 =? 4).
  Check h_Nateqb0 : (3 =? 4) = true.
  Check h_eq_true_leb : true = (3 <=? 4).
  Check h_eq_1_0 : 1 = 0.
  Check h_neq_x_y0 : x <> y.
  Check h_not_lt_1_0 : ~ 1 < 0.
  Check h_forall_neq_true_false : forall w w' : nat, w = w' -> true <> false.
  Check h_forall_trueEQfalse : forall w w' : nat, w = w' -> true = false.
  Check h_forall_Nateqb : forall w w' : nat, w = w' -> (3 =? 4) = (4 =? 3).
  Check h_eq_length : length (3 :: nil) = (fun _ : nat => 0) 1.
  Check h_eq_length_0 : length (3 :: nil) = 0.
  Check h_eq_add_y : 0 + y = y.
  Check h_trueEQfalse : true = false.
  Check h_impl_trueEQfalse : False -> true = false.
  Check z: nat.
  Check t : nat.
  Check h_IDProp : IDProp.
  Check h_impl_neq_true_false : 0 < 1 -> 0 < 0 -> true = false -> true <> false.
  Check h_neq_true_false : true <> false.
  Check h_forall_neq_true_false0 : forall w w' : nat, w < w' -> true <> false.
  Check h_impl_not_lt_1_0 : 0 < 1 -> ~ 1 < 0.
  Check h_impl_lt_1_0 : 0 < 1 -> 1 < 0.
  exact I.
Qed.
