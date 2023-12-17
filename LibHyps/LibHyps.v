(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

Require Export LibHyps.TacNewHyps.
Require Export LibHyps.LibHypsNaming.
(* Require Export LibHyps.LibSpecialize. *)
Require Export LibHyps.LibHypsTactics.
(* We export ; { } etc. ";;" also. *)

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

(* WARNING group_up_list applies to the whole list of hyps directly. *)
(* Tactic Notation (at level 4) tactic4(Tac) "/" "g" := (then_allnh Tac group_up_list). *)
Tactic Notation (at level 4) tactic4(Tac) "/" "g" := Tac ; {! group_up_list }.
Tactic Notation (at level 4) "/" "g" := (group_up_list all_hyps).

(* Tactic Notation (at level 4) tactic4(Tac) "/" "s" := (then_eachnh Tac subst_or_idtac). *)
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

Tactic Notation (at level 4) "/" "sng" :=
  (onAllHyps subst_or_idtac); (onAllHyps autorename); group_up_list all_hyps.
Tactic Notation (at level 4) "/" "sn" := (onAllHyps subst_or_idtac); (onAllHyps autorename).
Tactic Notation (at level 4) "/" "sr" := (onAllHyps subst_or_idtac); (onAllHyps revertHyp).
Tactic Notation (at level 4) "/" "ng" := ((onAllHyps autorename) ; group_up_list all_hyps).

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

(*
Goal forall x1 x3:bool, forall a z e : nat,
      z+e = a
      -> forall SEP:(True -> True),
        a = z+z
        -> ((fun f => z = e) true)
        -> forall b1 b2 b3 b4: bool,
          True -> True.
Proof.
  (* Set Ltac Debug. *)
  (* then_nh_rev ltac:(intros) ltac:(subst_or_idtac).   *)
  intros ; {! group_up_list }.
  (* intros ? ? ? ? ? ? ? ? ? ?. *)
  (* group_up_list (DCons bool b1 DNil). *)
  Undo.
  intros ; { move_up_types }.
  intros /n!.
  intros /s/n!.
  Undo.
  intros /n.
  match goal with
  | h: bool => assert 
  end
  Undo.
  intros/n.
  Undo.
  intros ; { autorename }; {! group_up_list }.
  Undo.
  intros/ng.
  Undo.
  intros ; {subst_or_idtac} ; { autorename } ; {! group_up_list }.
  Undo.
  intros/sng.
  Fail progress intros ; { revertHyp }.

  subst_or_idtac (DCons (z0 + r = a) H DNil).
 

  let hyps := all_hyps in
  idtac hyps.
  subst_or_idtac hyps.

  intros  ;!;  ltac:(subst_or_idtac_l).

  then_nh_one_by_one ltac:(intros) ltac:(subst_or_idtac).  
; {< subst_or_idtac }. ; { group_up_list } ; { autorename_l }.
  subst_or_idtac h_eq_a_add_z0_t.
  intros ; { fun h => autorename_strict h }.
  intros ; { fun h => idtac h }.
  intros ; { ltac:(fun h => idtac h) }.
   intros ; [H: sng H].
*)   
(*
Goal forall x1 x3:bool, True -> forall a z e r t z e r t z e r t z e r t y: nat, False -> forall u i o p q s d f g:nat, forall x2:bool,  True -> True.
Proof.
  
  time then_nh ltac:(intros) ltac:(group_up_list).

  intros.
  Set Ltac Profiling.
  let lh := all_hyps in
  let cache := build_initial_cache lh in
  group_up_list_ H (DCons bool x3 DNil) lh.
  idtac cache.
  
 *)
