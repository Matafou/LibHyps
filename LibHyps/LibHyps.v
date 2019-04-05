Require Export LibHyps.TacNewHyps.
Require Export LibHyps.LibHypsNaming.

(* Some usual tactics one may want to use with onNewHypsOf: *)
(* apply subst using H if possible. *)
Ltac substHyp H :=
  match type of H with
  | ?x = ?y => once (subst x + subst y)
  end.

(* revert, fails if impossible, should not fail if hyps are ordered in the right order *)
Ltac revertHyp H := revert H. (* revert is a tactic notation *)

(* revert if subst fails. Never fail, be careful to not use this tactic i n the
   left member of a "+" tactical: *)
Ltac subst_or_revert H := try first [substHyp H | revert H].

(* A tactic which moves up a hypothesis if it sort is Type or Set.
   These hypothesis are generally less interesting, having them far
   from the goal is harmless. Moreover with Set Printing Compact
   Context. Coq can group them in horizontal boxes. *)
Ltac move_up_types H := match type of H with
                        | ?T => match type of T with
                                | Set => move H at top
                                | Type => move H at top
                                | _ => idtac
                                end
                        end.

Ltac subst_or_move_up H := (substHyp H + move_up_types H).

(* two renaming tactical with different priorities wrt ";". !! binds
   stronger than ";", "!" bind weaker than ";". *)
Tactic Notation (at level 3) "!!" tactic3(Tac) := (Tac ;!; revert_if_norename ;; autorename).
Tactic Notation (at level 0) "!" tactic(Tac) := (Tac ;!; revert_if_norename ;; autorename).
(* !!! tac performs tac, then subst with new hypothesis when possible,
   then rename remaining new hyps. "!!!" binds string than ";" *)
Tactic Notation "!!!" tactic3(Tac) := (Tac ;; substHyp ;!; revert_if_norename ;; autorename).

(* Same as !!! + move hyp to the top of the goal if it is Type-sorted. *)
Tactic Notation (at level 4) "!!!!" tactic4(Tac) :=
  (Tac ;; substHyp ;!; revert_if_norename ;; autorename ;; move_up_types).
  (* (tac1 ;; (fun h => substHyp h||(move_up_types h;autorename h))). *)

(* subst or revert, revert is done from older to newer *)
Tactic Notation (at level 4) "??" tactic4(tac1) :=
  (tac1 ;; substHyp ;!; revertHyp).



(* subst or revert, revert is done from older to newer *)
Tactic Notation (at level 4) "?!" tactic4(tac1) :=
  ((tac1 ;; substHyp ;!; revert_if_norename) ;; autorename).

Ltac rename_all_hyps :=
  let renam H := autorename H in
  let hyps := all_hyps in
  map_hyps renam hyps.
