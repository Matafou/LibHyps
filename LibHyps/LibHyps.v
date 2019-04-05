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
Ltac subst_or_revert H := try (substHyp H + revert H).

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


(* A full example: *)

Ltac rename_hyp_2 h th :=
  match th with
  | true = false => fresh "trueEQfalse"
  end.

Ltac rename_hyp ::= rename_hyp_2.


Lemma foo:
  (true=false -> false = true -> false = false -> False) -> 
  (forall w w',w < w' -> ~(true=false)) ->
            False.
Proof.
  !intros.
Abort.

Lemma foo: forall x y,
    x <= y ->
    x = y ->
    true = Nat.eqb 3 4  ->
    1 = 0 ->
    ~x = y ->
    ~1 < 0 ->
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
      (0 < 1 -> 1<0) -> 0 < z.
  (* auto naming at intro: *)
  !intros.

  Undo.
  (* auto naming + subst when possible at intro: *)
  !!!intros.
  Undo.
  (* intros first, rename after: *)
  intros.
  rename_all_hyps.
  Undo 2.
  (* intros first, rename some hyp only: *)
  intros.
  autorename H0.
  Undo 2.
  (* put ;; between to tactics to apply the snd to all new hyps of all subgoals. *)
  intros;; (fun h => substHyp h||(move_up_types h;autorename h)).
  (* put ! before a (composed)tactic to rename all new hyps: *)
  !generalize (le_n 8);intros. 
  Undo 2.
  intros until 3.
  !destruct H eqn:?;intros.
  Undo.
  (* !! binds stronger than ";" *)
  !!destruct H eqn:?;intros.
  Undo.
  ?!(destruct H eqn:?;intros).
Abort.
*)