Require Import TacNewHyps.
Require Import LibHypsNaming.
Require Import LibDecomp.
(* Some tactics used in sparkCompcert. Mostly about autorenaming. *)

(* Same tactic as LibDecomp.decomp_logical but make sure the name of
   the hypothesis decomposed is not recycled during the process, so
   that all generated hypothesis are detected as such. *)
Ltac decompose_clear c :=
  let h := fresh "h_decomp" in
  pose proof c as h;
  decomp_logicals c; try clear h.

(* decompose + rename new hyps. *)
Tactic Notation "decomp" constr(c) := (!!decompose_clear c).

(* Iterating the tactic on all hypothesis. Moves up all Set/Type
   variables to the top. Really useful with [Set Compact Context]
   which is no yet commited in coq-trunk. *)
Ltac up_type := map_all_hyps_rev move_up_types.

(* rew foo with tac first rewrite everywhere with t' (right to left),
then applies tac and then rewrite eveywhere in the other direction.
this is useful when some tactic needs the goal (or a hypothesis to be
in a certain form but you don't want to keep this form in your goal. *)
Tactic Notation "rew" constr(t') "with"  tactic(tac) :=
  try (rewrite <- t' in * ); tac; (try rewrite t' in * ).

(* subst with all new hyps if ossible after applying tactic tac *)
(* Ltac subst_new_hyps tac := onNewHypsOf ltac:tac do substHyp. *)

(* !!! tac performs tac, then subst with new hypothesis when possible,
   then rename remaining new hyps. *)
Tactic Notation "!!!" tactic3(Tac) := !!(tac_new_hyps Tac substHyp).

(* Same + move hyp to the top of the goal if it is Type-sorted *)
Tactic Notation (at level 4) "!!!!" tactic4(tac1) :=
  (tac1 ;; (fun h => substHyp h||(move_up_types h;autorename h))).

(* subst or revert, revert is done from older to newer *)
Tactic Notation (at level 4) "??" tactic4(tac1) :=
  (tac1 ;; substHyp ;!; revertHyp).

(* in sparkCompcert !inversion always tries to subst. *)
Tactic Notation "!inversion" hyp(h) := !!! (inversion h).
Tactic Notation "!invclear" hyp(h) := !!! (inversion h;clear h).

(* Example of !!! and ?? *)
(*
Ltac rename_hyp_2 h th :=
  match th with
  | true = false => fresh "trueEQfalse"
  end.

Ltac rename_hyp ::= rename_hyp_2.

Lemma foo: forall x y,
    x <= y ->
    x = y ->
    ~x = y ->
    ~1 < 0 ->
    forall z t:nat,
    (0 < 1 -> ~(true=false)) ->
    (forall w w',w < w' -> ~(true=false)) ->
    (0 < 1 -> ~(1<0)) ->
    (0 < 1 -> 1<0) -> 0 < z.
  (* auto naming + subst when possible at intro: *)
  ??intros.
  Undo.
  !!!intros.
  Undo.
  !!!!intros.
Admitted.
*)
(* Examples of decomp *)
(*
Lemma foo : forall x, { aa:nat | (aa = x /\ x=aa) & (aa = aa /\ aa= x) } -> False.
Proof.
  intros x H.
  decomp H.
Abort.

Lemma foo : { aa:False & True  } -> False.
Proof.
  intros H.
  decomp H.
Abort.


Lemma foo : { aa:False & True & False  } -> False.
Proof.
  intros H.
  decomp H.
Abort.
*)

