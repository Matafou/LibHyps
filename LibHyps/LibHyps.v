(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

Require Export LibHyps.TacNewHyps.
Require Export LibHyps.LibHypsNaming.
Require Export LibHyps.Especialize.
Require Export LibHyps.AssertPremise.
Require Export LibHyps.LibHypsTactics.

(* Some usual tactics one may want to use on new hyps. *)

Ltac rename_or_revert H := autorename_strict H + generalize dependent H.
(* revert, fails if impossible, should not fail if hyps are ordered in the right order *)
Ltac revertHyp H := revert H. (* revert is a tactic notation, so we need to define this *)
(* revert if subst fails. Never fail, be careful not to use this tactic in the
   left member of a "+" tactical: *)
Ltac subst_or_revert H := try first [progress substHyp H | generalize dependent H].
(* try subst. Never fail, be careful to not use this tactic in the
   left member of a "+" tactical: *)
Ltac subst_or_idtac H := substHyp H.

(* TACTIC NOTATIONS *)
(* This exports the "tac ; { } ." syntax for then_eachnh. *)
Export TacNewHyps.Notations.

(* There are three variants of the autorename tatic, depending on what
   to do with hypothesis on which no name was found. *)
(* hypothesis for which autonaming failed ar left with there default name.  *)
Tactic Notation (at level 4) tactic4(Tac) "/" "n":= Tac ; { autorename }.
Tactic Notation (at level 4) "/" "n" := (onAllHyps autorename).
(* Fail if autonaming fails on some hyp *)
Tactic Notation(at level 4) tactic4(Tac) "/" "n!":= Tac ; { autorename_strict }.
Tactic Notation (at level 4) "/" "n!" := (onAllHyps autorename_strict).
(* Revert hyps for which autorenaming fails, but don't fail *)
Tactic Notation (at level 4) tactic4(Tac) "/" "n?" := Tac ; { rename_or_revert }.
Tactic Notation (at level 4) "/" "n?" := (onAllHyps rename_or_revert).

(* Revert new hypothesis *)
Tactic Notation (at level 4) tactic4(Tac) "/" "r" := Tac ; {< revertHyp }.
Tactic Notation (at level 4) "/" "r" := (onAllHypsRev revertHyp).

Tactic Notation (at level 4) tactic4(Tac) "/" "g" := Tac ; { move_up_types }.
Tactic Notation (at level 4) "/" "g" := (onAllHyps move_up_types).

Tactic Notation (at level 4) tactic4(Tac) "/" "s" := Tac ; { subst_or_idtac }.
Tactic Notation (at level 4) "/" "s" := (onAllHyps subst_or_idtac).

(* usual combinations *)
Tactic Notation (at level 4) tactic4(Tac) "//" := (Tac /s/n/g).
Tactic Notation (at level 4) tactic4(Tac) "/" "sng" := (Tac /s/n/g).
Tactic Notation (at level 4) tactic4(Tac) "/" "sgn" := (Tac /s/g/n).
Tactic Notation (at level 4) tactic4(Tac) "/" "sn" := (Tac /s/n).
Tactic Notation (at level 4) tactic4(Tac) "/" "sr" := (Tac /s/r).
Tactic Notation (at level 4) tactic4(Tac) "/" "sg" := (Tac /s/g).
Tactic Notation (at level 4) tactic4(Tac) "/" "ng" := (Tac /n/g).
Tactic Notation (at level 4) tactic4(Tac) "/" "gn" := (Tac /g/n).

(* Tactic Notation (at level 4) "/" "sng" := *)
  (* (onAllHyps subst_or_idtac); (onAllHyps autorename); group_up_list all_hyps. *)
Tactic Notation (at level 4) "/" "sn" := (onAllHyps subst_or_idtac); (onAllHyps autorename).
Tactic Notation (at level 4) "/" "sr" := (onAllHyps subst_or_idtac); (onAllHyps revertHyp).
Tactic Notation (at level 4) "/" "ng" := ((onAllHyps autorename) ; (onAllHyps move_up_types) ).

Module LegacyNotations.
  Import Notations.
  (* COMPATIBILITY WITH PREVIOUS VERSION OF LIBHYPS. *)
  Tactic Notation (at level 0) "!" tactic(Tac) := (Tac /n?).
  (* binds stronger than ";" *)
  Tactic Notation (at level 3) "!!" tactic3(Tac) := (Tac /n).
  (* like !!tac + tries to subst with each new hypothesis. *)
  Tactic Notation "!!!" tactic3(Tac) := Tac/s/n?.
  (* Like !!! + regroup new Type-sorted hyps at top. *)
  Tactic Notation (at level 4) "!!!!" tactic4(Tac) := Tac /s/n?/g.

  (* Other Experimental combinations *)

  (* subst or revert, revert is done from older to newer for consistency. *)
  Tactic Notation (at level 4) "??" tactic4(tac1) := tac1 /s/r.

  (* subst or rename or revert, revert is done from older to newer *)
  Tactic Notation (at level 4) "?!" tactic4(tac1) :=
    tac1 /s/n!.
End LegacyNotations.
