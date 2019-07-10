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

(** Demonstration file for LibHyps tactics and tacticals.  *)

Require Import Arith ZArith LibHyps.LibHyps List.


Lemma foo: forall x y z:nat,
    x = y -> forall  a b t : nat, a+1 = t+2 -> b + 5 = t - 7 ->  (forall u v, v+1 = 1 -> u+1 = 1 -> a+1 = z+2)  -> z = b + x-> True.
Proof.
  intros.
  (* ugly names *)
  Undo.
  intros ;; autorename. (* ;; here means "apply to all new hyps" *)
  (* better names *)
  Undo.
  (* short syntax: *)
  !intros.
  Undo.
  (* same thing but use subst if possible, and push non prop hyps to the top. *)
  intros;; substHyp;; autorename;;move_up_types.
  Undo.
  (* short syntax: *)  
  !!!intros.
  (* Let us instantiate the 2nd premis of h_all_eq_add_add without copying its type: *)
  especialize h_all_eq_add_add at 2.
  { apply Nat.add_0_l. }
  (* now h_all_eq_add_add is specialized *)

  Undo 6.
  intros until 1.
  (** Do subst on new hyps only, notice how x=y is not subst and
    remains as 0 = y. Contrary to z = b  + x which is substituted. *)
  (destruct x eqn:heq;intros);; substHyp.
  - apply I.
  - apply I.
Qed.

(** Example of tactic notations to define shortcuts for the examples
   above: here =tac does "apply tac and try subst on all new hypothesis" *)
Local Tactic Notation "=" tactic3(Tac) := Tac ;!; substHyp.

Lemma bar: forall x y a t u v : nat,
    x = v -> a = t -> u = x -> u = y -> x = y.
Proof.
  =intros.
  Undo.
  intros.
  =destruct x eqn:heq.
  - subst;auto.
  - subst;auto.
Qed.


(** Example of tactic notations to define shortcuts: <=tac means "apply
   tac and reverts all created hypothesis" *)
Local Tactic Notation "<=" tactic3(Tac) := Tac ;!; revertHyp.

Lemma bar2: forall x y a t u v : nat,
    x = v -> a = t -> u = x -> u = y -> x = y.
Proof.
  intros.
  <=destruct x eqn:heq.
  - intros;subst;auto.
  - intros;subst;auto.
Qed.



(** Another exampe: <-tac means "apply tac and try subst on all created
   hypothesis, revert when subst fails" *)
Local Tactic Notation "<-" tactic3(Tac) := Tac ;!; subst_or_revert.

Lemma bar': forall x y a t u v : nat,
    x < v -> a = t -> u > x -> u = y -> x < y.
Proof.
  <-intros.
  auto.
Qed.


(** 1 especialize allows to do forward reasoning without copy pasting statements.
   from a goal of the form 

H: forall ..., h1 -> h2 ... hn-1 -> hn -> hn+1 ... -> concl.
========================
G

especialize H at n.
gives two subgoals:

H: forall ..., h1 -> h2 ... hn-1 -> hn+1 ... -> concl.
========================
G

========================
hn

this creates as much evars as necessary for all parameters of H that
need to be instantiated.

Example: *)

Definition test n := n = 1.
Definition Q (x:nat) (b:bool) (l:list nat):= True.

Lemma foo':
  (forall n b l, b = true -> test n -> Q n b l) ->
  Q 1 true (cons 1 nil).
Proof.
  intro hyp.
  (* I want to prove the (test n) hypothesis of hyp, without knwing n
     yet, and specialize hyp with it immediately. *)

  especialize hyp at 2.
  { reflexivity. }
  Undo 4.

  (* Same thing with a given name for the new premis once proved *)
  especialize hyp at 2:foo.
  { reflexivity. }
  Undo 4.

  (* Build a new hypothesis instead of specializing hyp itself *)
  especialize hyp at 2 as h.
  { reflexivity. }
  specialize hyp with (2:=hyp_prem).
  Undo 5.

  (* same with a given name for the premiss *)
  especialize hyp at 2 : foo as h.
  { reflexivity. }
  specialize hyp with (2:=foo).
  Undo 5.

  apply I.
Qed.



(** 1 Auto naming hypothesis *)

(** Let us custmize the naming scheme:  *)

(* First open the some dedicated notations (namely `id` and x#n below). *)
Local Open Scope autonaming_scope.
Import ListNotations.

(* Define the naming scheme as new tactic *)
Ltac rename_hyp_2 n th :=
  match th with
  | Nat.eqb ?x ?y = _ => name(`_Neqb` ++ x#n ++ x#n)
  | _ = Nat.eqb ?x ?y => name(`_Neqb` ++ x#n ++ x#n)
  end.

(* Then overwrite the customization hook of the naming tactic *)
Ltac rename_hyp ::= rename_hyp_2.

(** Suppose I want to add another naming rule: I need to cumulate the
    previous scheme with the new one. First define a new tactic that
    will replace the old one. it should call previous naming schemes
    in case of failure of the new scheme *)
Ltac rename_hyp_3 n th :=
  match th with
  | true <> false => name(`_tNEQf`)
  | true = false => name(`_tEQf`)
  (* if all failed, call the previously defined naming tactic, which
     must not be rename_hyp since it will be overwritten: *)
  | _ => rename_hyp_2 n th
  end.

(* Then update the customization hook *)
Ltac rename_hyp ::= rename_hyp_3.
(* Close the naming scope *)
Local Close Scope autonaming_scope.

(** 2 Example of uses of the naming schemes. *)
Lemma dummy: forall x y,
    (forall nat : Type, (nat -> nat -> Prop) -> list nat -> Prop) ->
    (let a := 0 in a = 0) -> (* this is is not treated for renaming *)
    (exists x, (let a := x in a = 0) /\ (x >=0)) -> (* this too, once decomposed *)
    0 <= 1 ->
    0 = 1 ->
    (0%Z <= 1%Z)%Z ->
    (0%Z <= 6%Z)%Z ->
    x <= y ->
    x = y ->
    0 = 3 ->
    (1 = 8)%Z ->
    ~x = y ->
    true = Nat.eqb 3 4  ->
    Nat.eqb 3 4 = true  ->
    true = Nat.leb 3 4  ->
    1 = 0 ->
    ~x = y ->
    ~1 < 0 ->
     (forall w w':nat , w = w' -> ~true=false)=(forall w w':nat , w = w' -> ~true=false) ->
     (forall w w':nat , w = w' -> ~true=false) ->
     (forall w w':nat , w = w' -> true=false /\ True) ->
     (forall w w':nat , w = w' -> true=false) ->
     (forall w w':nat , w = w' -> False /\ True) ->
     (exists w:nat , ~(true=(andb false true)) /\ le w w /\ w = x) ->
     (exists w:nat , w = w -> ~(true=(andb false true)) /\ False) ->
     (exists w:nat , w = w -> True /\ False) ->
     (forall w w':nat , w = w' -> true=false) ->
     (forall w:nat , w = w -> true=false) ->
     (forall w:nat, (Nat.eqb w w)=false) ->
     (forall w w':nat , w = w' -> Nat.eqb 3 4=Nat.eqb 4 3) ->
    List.length (cons 3 nil) = (fun x => 0)1 ->
    List.length (cons 3 nil) = x ->
    plus 0 y = y ->
    plus (plus (plus x y) y) y = y ->
    (true=false) ->
    (true<>false) ->
    (False -> (true=false)) ->
    forall (a b: nat) (env : list nat),
      ~ List.In a nil ->
      cons a (cons 3 env) = cons 2 env ->
    forall z t:nat,
      IDProp ->
      a = b ->
      (0 < 1 -> 0 < 0 -> true = false -> ~(true=false)) ->
      (~(true=false)) ->
      (forall w w',w < w' -> ~(true=false)) ->
      plus (plus (plus x y) a) b = t ->
      plus (plus (plus x y) a) b < 0 ->
      (0 < 1 -> ~(1<0)) ->
      (0 < 1 -> 1<0) -> 0 < z -> True.
  (* auto naming at intro: *)
Proof.
  intros.
  onAllHyps autorename.
  Undo 2.
  (* Shorter: the ! tactical applies a tactic and then applies
     autorename on new hypothesis: *)
  !intros.
  Undo.
  (* combining ! and = defined previously (subst) *)
  =!intros.
  Undo.
  (** Reduce renaming depth to 2: *)
  Ltac rename_depth ::= constr:(2).
  (* names are shorter, more collisions *)
  !intros.
  Undo.
  Ltac rename_depth ::= constr:(3).
  !intros.
  (** move up all non prop hypothesis *)
  Undo.
  (* Let us have really big names. *)
  Ltac rename_depth ::= constr:(5).
  !intros.
  onAllHyps move_up_types.
  (* decompose and revert all new hyps *)
  decompose [ex and] h_ex_and_neq_true_andb_false_true_and_le_w_w_eq_w_x ;!; revertHyp.
  Undo.
  (* decompose and subst or revert all new hyps *)
  decompose [ex and] h_ex_and_neq_true_andb_false_true_and_le_w_w_eq_w_x ;!; subst_or_revert.
  Undo.
  (* decompose and rename all new hyps *)
  decompose [ex and] h_ex_and_neq_true_andb_false_true_and_le_w_w_eq_w_x ;!; autorename.
  Undo.
  (* in short: *)
  !decompose [ex and] h_ex_and_neq_true_andb_false_true_and_le_w_w_eq_w_x.
  Undo.
  (* decompose and subst or rename all new hyps *)
  decompose [ex and] h_ex_and_neq_true_andb_false_true_and_le_w_w_eq_w_x ;; substHyp ;!; revert_if_norename ;; autorename.
  Undo.
  (* decompose and subst or rename all new hyps, revert if nothing applies *)
  decompose [ex and] h_ex_and_ge_x_0n ;; substHyp ;!; revert_if_norename ;; autorename.
  Undo.
  (* in short: *)
  !!!decompose [ex and] h_ex_and_neq_true_andb_false_true_and_le_w_w_eq_w_x.
  Undo.
  (* introducing the hypothesis that was not autonamed: *)
  intro h.
  exact I.
Qed.




