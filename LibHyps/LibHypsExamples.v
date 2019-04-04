Require Import LibHyps.LibHyps LibHyps.LibSpecialize.

(* Typical use, subst with all hyps created by inversion, and move
Type-sorted hyps to the top of the goal:

inversion H ;; subst_or_move_up.

  See also LibHypsNaming.v for a generic tactic for auto naming new
  hypothesis. *)

(* Examples of use: *)

Lemma foo: forall x y:nat,
    x = y -> forall  a t : nat, a+1 = t+2 ->forall u v, u+1 = v -> a+1 = t+2 -> False.
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
  onNewHypsOf (destruct x eqn:heq;intros) do substHyp.
  Undo.
  (* same + move up new hyps of Sort Type *)
  onNewHypsOf (destruct x eqn:heq;intros) do (fun h => substHyp h || move_up_types h).
  Undo.
  (* First attempt to revert all new hyps: wrong order *)
  onNewHypsOf (destruct x eqn:heq;intros) do revertHyp.
  Undo.
  (* Works better if we go in reverse order: *)
  onNewHypsOfRev (destruct x eqn:heq;intros) do revertHyp.
  Undo.
  (* revert everything except if subst can remove the hyp *)
  onNewHypsOfRev (destruct x eqn:heq;intros) do subst_or_revert.
Abort.

(* Example of tactic notations to define shortcuts: =tac means "apply
   tac and try subst on all created hypothesis" *)
Local Tactic Notation "=" tactic3(Tac) := onNewHypsOfRev (Tac) do substHyp.

Lemma bar: forall x y a t u v : nat,
    x = v -> a = t -> u = x -> u = y -> x = y.
Proof.
  =intros.
  Undo.
  intros.
  =destruct x eqn:heq.
Abort.


(* Example of tactic notations to define shortcuts: =tac means "apply
   tac and try subst on all created hypothesis" *)
Local Tactic Notation "<=" tactic3(Tac) := onNewHypsOfRev (Tac) do revertHyp.

Lemma bar: forall x y a t u v : nat,
    x = v -> a = t -> u = x -> u = y -> x = y.
Proof.
  intros.
  <=destruct x eqn:heq.
Abort.



(* Another exampe: =tac means "apply
   tac and try subst on all created hypothesis" *)
Local Tactic Notation "<-" tactic3(Tac) := onNewHypsOfRev (Tac) do subst_or_revert.

Lemma bar: forall x y a t u v : nat,
    x < v -> a = t -> u > x -> u = y -> x < y.
Proof.
  <-intros.
  (* Some variable (ones on which subst worked) are not reverted *)
Abort.


(* Better version *)
Local Tactic Notation "<<-" tactic3(Tac) := onNewHypsOfRev (onNewHypsOf (Tac) do substHyp ) do revertHyp.

Lemma bar: forall x y a t u v : nat,
    x < v -> a = t -> u > x -> u = y -> x < y.
Proof.
  <<-intros.
Abort.




Definition test n := n = 1.
Variable Q: nat -> bool -> list nat -> Prop.

Lemma foo:
  (forall n b l, b = true -> test n -> Q n b l) ->
  (true = true -> false = false ->  True) -> Q 1 true (cons 1 nil).
Proof.
  intros hyp hyp'.
  (* proveprem hyp at 2 as h. *)
  let ev := open_constr:((_:Prop)) in
  assert (id:ev).
  Focus 2.
  eassert (hhh:=fun b l (h:b=true) => hyp _ b l h id).



  Focus 2.
  (specialize hyp with (2:=id)).
  Show Proof.
  
   2:specialize hyp with (2:=id).
  { reflexivity. }
  Check hyp.
  proveprem hyp at 1.
  { reflexivity. }
  Check hyp_prem.
  apply hyp.
Qed.


