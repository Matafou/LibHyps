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
Abort.

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
Abort.


(* Example of tactic notations to define shortcuts: =tac means "apply
   tac and reverts all created hypothesis" *)
Local Tactic Notation "<=" tactic3(Tac) := Tac ;!; revertHyp.

Lemma bar: forall x y a t u v : nat,
    x = v -> a = t -> u = x -> u = y -> x = y.
Proof.
  intros.
  <=destruct x eqn:heq.
Abort.



(* Another exampe: =tac means "apply
   tac and try subst on all created hypothesis, revert when subst fails" *)
Local Tactic Notation "<-" tactic3(Tac) := Tac ;!; subst_or_revert.

Lemma bar: forall x y a t u v : nat,
    x < v -> a = t -> u > x -> u = y -> x < y.
Proof.
  <-intros.
  (* Some variable (ones on which subst worked) are not reverted *)
Abort.

Definition test n := n = 1.
Variable Q: nat -> bool -> list nat -> Prop.

Lemma foo:
  (forall n b l, b = true -> test n -> Q n b l) ->
  Q 1 true (cons 1 nil).
Proof.
  intro hyp.
  especialize hyp at 2 as h.
  { reflexivity. }
  apply hyp.
  reflexivity.
Qed.


