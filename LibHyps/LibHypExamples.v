Require Import LibHyps.LibHyps.

(* Typical use, subst with all hyps created by inversion, and move
Type-sorted hyps to the top of the goal:

inversion H ;; subst_or_move_up.

  See also LibHypsNaming.v for a generic tactic for auto naming new
  hypothesis. *)

(* Examples of use: *)

Lemma foo: forall x y a t : nat,
    x = y -> a+1 = t+2 ->forall u v, u+1 = v -> a+1 = t+2 -> False.
Proof.
  intros.
  onAllHyps move_up_types.
  Undo.
  onAllHyps subst_or_revert.
  Undo.
  onAllHypsRev subst_or_revert.
  Restart.
  intros until 1.
  onNewHypsOf (destruct x eqn:heq;intros) do (fun h => substHyp h).
  Undo.
  onNewHypsOf (destruct x eqn:heq;intros) do substHyp.
  Undo.
  onNewHypsOf (destruct x eqn:heq;intros) do revertHyp.
  Undo.
  onNewHypsOf (destruct x eqn:heq;intros) do (fun h => substHyp h || move_up_types h).
  Undo.
  onNewHypsOf (destruct x eqn:heq;intros) do subst_or_revert.
Abort.

(* Example of tactic notations to define shortcuts: *)
Local Tactic Notation "=" tactic3(Tac) := onNewHypsOf (Tac) do substHyp.

Lemma bar: forall x y a t u v : nat,
    x = y -> a = t -> u = v -> False.
Proof.
  intros.
   =destruct x eqn:heq.
Abort.

