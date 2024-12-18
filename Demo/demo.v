(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

(* DEMO FILE FOR THE LIBHYPS LIBRARY FEATURES. *)

(* This acts as a documentation for LibHyps. *)

(* WARNING: You can play this file in any IDE but beware that it
contains "Undo" at many places and that your IDE may not support it.
In this case you can edit the script by commenting things instead of
playing the Undos. *)

(* You can install LibHyps with opam with:

opam install coq_libhyps *)

(*** Proof maintenance ***)
Unset Printing Compact Contexts.
Require Import Arith ZArith  List.
Require Import LibHyps.LibHyps.


Lemma foo: forall (x:nat) (b1:bool) (y:nat) (b2:bool),
    x = y
    -> orb b2 b1 = false
    -> forall  a b:nat, forall b3:bool, forall t : nat,
        a+1 = t+2
        -> b + 5 = t - 7
        -> forall z, forall b4:bool, forall z',
            orb b3 b4 = b2
            -> (forall u v, v+1 = 1 -> u+1 = 1 -> a = z+2)
            -> z = b + 5-> z' + 1 = b + x-> x < y + b.
Proof.
  (* tactical "; { }" to apply a tactic to each "new" hyp. *)
  intros ; { fun h => idtac h }.
  Undo.
  (* tactical "; {< }": same but newer hyps first. *)
  intros ; {< fun h => idtac h }.
  Undo.
  intros x b1.
  (* Only the *new* hyps are iterated *)
  intros ; { fun h => idtac h }.
  Undo 2.
  (* Simply based on new *names* *)
  intros x b1.
  (* this tactic renames x into aaa, which is a new name. *)
  rename x into aaa ; { fun h => idtac h }.
  Undo 2.
  (* Here x is reused by induction and thus not new. *)
  intros x.
  induction x ; {< (fun h => idtac h) }.
  Undo 2.
  (* tactical "onAllhyps": same thing but on all hyps. *)
  intros.
  onAllHyps (fun h => idtac h).

  (*** Use Cases  ***)

  (* Revert any new hyp. Must be older fist. *)
  intros.
  revert x H H6.
  induction x ; {< (fun h => generalize dependent h) }.
  Undo.
  (* Shortcut *)
  induction x /r.

  Restart.
  (* Try subst on each new hyp. *)
  intros ; { fun h => try match type of h with
                        (?x = ?y) => (subst x+subst y)
                      end }.
  Undo.
  (* predefined tactic. *)
  intros ;{ subst_or_idtac }.
  Undo.
  (* and a shortcut. *)
  intros /s.
  Undo.
  (* combination: try subst and revert remaining hyps. *)
  intros x b1.
  intros ; { subst_or_idtac } ; {< (fun h => generalize dependent h) }.
  Undo.
  intros /s/r.
  Undo 2.
  (* It really applies only on new hyps: *)
  intros until 1.
  intros /s/r.

Abort.


(*** Large Goals - Foraward reasoning and reordering and autorenaming of hypothesis. ***)

Lemma foo: forall (x:nat) (b1:bool) (y:nat) (b2:bool),
    x = y ->
    orb b2 b1 = false ->
    forall  a b:nat, forall b3:bool, forall t : nat,
      a+1 = t+2 ->
      b + 5 = t - 7 ->
      (forall n m p : nat,
          0 <= p ->
          Nat.divide n p ->
          Nat.divide m p ->
          (forall q : nat, Nat.divide n q -> Nat.divide m q
                    -> Nat.divide p q) ->
          Nat.lcm n m = p) ->
      (exists w:nat , ~(true=(andb false true)) /\ le w w /\ w = x) ->
      forall z, forall b4:bool, forall z',
        orb b3 b4 = b2 ->
        (forall u v, v+1 = 1 -> u+1 = 1 -> a = z+2) ->
        z = b + 5-> z' + 1 = b + x-> x < y + b.
Proof.
  intros.
  Set Printing Compact Contexts.
  (* BIG HYPS may clutter the goal. IDE solution. *)
  (* 1. ProofGeneral: just hide it by clicking on its button, or hit
        "f" while cursor on its name. Persistent and simply based on
        hyp name. *)

  (* 2. Big hyps ask for "non verbose forward reasoning". *)
  (* Since a few years coq allows "specialize" to re-quantifies
     non-unified premisses. *)
  specialize H3 with (1:= le_S _ _ (le_n 0)).

  (* Our tactic "especialize" starts a goal to instantiate a dependent
     premiss of a hyp, and then re-quantifies everything non
     instantiated. *)
  Undo.
  (* THIS IS BROKEN IN COQ 8.18 *)
  especialize H3 with p at 1.
  { apply le_S.
    apply le_n. }
  Undo 5.
  (* IDEs don't like Undo, replay the next ocommand twice will resync
     proofgeneral. *)
  (* It accepts several (up to 7) premisses numers. *)
  (* BROKEN IN 8.18 *)
  especialize H3 with n,m,p at 2,3.
  Undo.

  (* you can ask a goal for all premisses, in the spirit of the
     "exploit" tactic from CompCert. *)
  (* BROKEN IN 8.18 *)
  especialize H3 with  n,m,p at *.
  Undo.
  
  (* You can also specify that you want to instantiate the n first premisses. *)
  (* BROKEN IN 8.18 *)
  especialize H3 with n,m,p until 3.
  Show 4.
  Undo.

  (* VARIABLES MIXED WITH HYPOTHESIS. *)
  (* move_up_types X. moves X at top near something of the same type,
     but only if X is Type-sorted (not Prop). *)
  move_up_types b4. (* group z on top *)
  move_up_types H. (* does nothing because H:..:Prop *)
  Undo 2.
  Unset Printing Compact Contexts.
  (* Do that on all hyps: *)
  onAllHyps move_up_types.
  Set Printing Compact Contexts.
  Restart.
  (* Better do that on new hyps only. *)
  intros ; { move_up_types }.
  Undo.
  (* Faster version dealing with the whole list of new hyps at once: *)
  intros; {! group_up_list }.
  Undo.
  (* Shortcut for this faster version: *)
  intros /g.
  Undo.
  (* combined with subst: *)
  intros /s/g.
  (* And have this coq option on fo saving a bit more room: *)
  Set Printing Compact Contexts.

  (*** HYPOTHESIS NAMES. ***)
  Restart.
  intros.
  Undo.
  (* After a lot of non interesting thinking. *)
  intros x b1 y b2 h_x_eq_y h_or_b2_b1 a b b3 t
         h_a_t h_b_t hh hex z b4 z' h_b3_b4 h_all_uvaz
         heq_z heq_z'_b.
  (* But at each change in definitions or statements ==> Adapt the
     intros and "as". *)
  Restart.
  intros.
  (* tactic "autorename H" applies the naming heursitc to H. *)
  autorename H.
  (* Notice the trailing "_": avoids coq replacing digits. *)
  Undo.
  (* Again, one can apply it to all hyps: *)
  onAllHyps autorename.

  (* experimental: (setq coq-libhyps-intros t) *)
  Undo 2.
  Show.
  Restart.
  Show.
  (* Again, better combine it with "; { }". *)
  intros ; { autorename }.
  (* You can still shorten big hyps. but hiding most of the time is better. *)
  rename h_all_eq_lcm_p_ into hall.
  Undo 2.
  (* shortcut: *)
  intros /n.
  Restart. Show. Set Printing Compact Contexts.
  (* Combining with other cleaning operators: *)
  intros /s/n/g. (* /sng is also accepted *)
  (* Long names, this is configurable (next demo), but IDE provides
     easy ways to see them (highlight) and to input them:
     - middle-click on hyp's name.
     - completion (company-coq). *)

  (* tactic that generate names can be easily tamed. *)
  decompose [ex and or] h_ex_and_neq_and_/sng.
  (* No more obscure "as" to maintain *)
  inversion h_le_y_y_ /sng.
  Show 2.
  (* You can still use destructive pattern, but without inventing names: *)
  Undo.
  assert (y < a /\ b < t /\ z' < t) /n.
  {admit. }
  destruct h_and_lt_y_a_and_lt_lt_ as [ ? [? ?]] /n.

Abort.

(* customization of autorename *)

Local Open Scope autonaming_scope.
Import ListNotations.

(* Define the naming scheme as new tactic pattern matching on a type
th, and the depth n of the recursive naming analysis. Here we state
that a type starting with Nat.eqb should start with _Neqb, followed by
the name of both arguments. #n here means normal decrement of depth.
(S n) would increase depth by 1 (n-1) would decrease depth. *)
Ltac rename_hyp_2 n th :=
  match th with
  | Nat.eqb ?x ?y => name(`_Neqb` ++ x#n ++ y#n)
  end.

(* Then overwrite the customization hook of the naming tactic *)
Ltac rename_hyp ::= rename_hyp_2.

Goal forall x y:nat, True.
  intros.
  (* computing a few names *)
  (* Customize the starting depth *)

  let res := fallback_rename_hyp_name (Nat.eqb 1 2) in idtac res.
  let res := fallback_rename_hyp_name (Nat.eqb x 4) in idtac res.
  let res := fallback_rename_hyp_name (Nat.eqb 1 2 = false) in idtac res.
  Ltac rename_depth ::= constr:(2).
  let res := fallback_rename_hyp_name (Nat.eqb 1 2 = false) in idtac res.
  Ltac rename_depth ::= constr:(3).
Abort.

(** Suppose I want to add another naming rule: I need to cumulate the
    previous scheme with the new one. First define a new tactic that
    will replace the old one. it should call previous naming schemes
    in case of failure of the new scheme. It is thus important that
    rename_hyp_2 was defined by itself and directly as rename_hyp. *)
Ltac rename_hyp_3 n th :=
  match th with
  | ?x = false => name(x#n ++ `_isf`)
  | ?x = true => name( x#n ++ `_ist`)
  | _ => rename_hyp_2 n th (* previous naming scheme *)
  end.

(* Then update the customization hook *)
Ltac rename_hyp ::= rename_hyp_3.
(* Close the naming scope *)
Local Close Scope autonaming_scope.

Goal forall x y:nat, True.
  intros.
  let res := fallback_rename_hyp_name (Nat.eqb 1 2 = false) in
  idtac res.
Abort.



Lemma foo: forall (x:nat) (b1:bool) (y:nat) (b2:bool),
    x = y
    -> orb b2 b1 = false
    -> forall  a b:nat, forall b3:bool, forall t : nat,
        true = Nat.eqb (a+1) (t+2)
        -> b + 5 = t - 7
        -> forall z, forall b4:bool, forall z',
            orb b3 b4 = b2
            -> (forall u v, v+1 = 1 -> u+1 = 1 -> a = z+2)
            -> z = b + 5-> z' + 1 = b + x-> x < y + b.
Proof.
  (* Customize the starting depth *)
  Ltac rename_depth ::= constr:(3).

  intros/n/g.
  Undo.
  (* Have shorter names: *)
  Ltac rename_depth ::= constr:(2).
  intros/n/g.


Abort.

(*** Local Variables: ***)
(*** eval: (company-coq-mode 1) ***)
(*** End: ***)
