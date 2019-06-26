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

Require Export LibHyps.TacNewHyps.
Require Export LibHyps.LibHypsNaming.
Require Export LibHyps.LibSpecialize.

(* Tactical to rename all new hypothesis. A hypothesis is new if its
   name was not present in previous goal. *)
Ltac rename_new_hyps tac := tac_new_hyps tac autorename.

(* Default behaviour: generalize hypothesis that we failed to rename,
   so that no automatic names are introduced by mistake. Of course one
   can do "intros" to reintroduce them.

   Revert needs to be done in the other direction (so better do ";;
   autorename ;!; revertHyp"), and may fail if something depends on
   the reverted hyp. So we should revert everything depending on the
   unrenamed hyp. *)
Ltac revert_if_norename H :=
  let t := type of H in
  match type of t with
  | Prop => match goal with
            | _ =>  let x := fallback_rename_hyp_name t in idtac
            (* since we are only in prop it is almost never the case
               that something depends on H but if this happens we revert
               everything that does. *)
            | _ => try revert dependent H
            end
  | _ => idtac
  end.

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
