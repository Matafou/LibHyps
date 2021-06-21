(* Copyright 2017,2019,2021 Pierre Courtieu *)
(* This file is part of LibHyps. It is distributed under GPLv3.

 You should have received a copy of the GNU General Public License
 along with LibHyps.  If not, see <https://www.gnu.org/licenses/>. *)

(* proveprem H at i as h. Create an assert for the ith dependent
premiss of hypothesis H and specialize H with the resulting proof. h
is the (optional) name of the asserted premiss. *)

Ltac freshable t :=
  let x := fresh t "_dummy_sufx" in
  idtac.

Ltac proveprem_as_prem H i idpremis idnewH :=
  (* prefer this to evar, which is not well "typed" by Ltac (does not
     know that it creates an evar (coq bug?). *)
  let ev := open_constr:((_:Prop)) in
  assert (idpremis:ev);
  [|specialize H with (i:=idpremis) as idnewH].

Tactic Notation "especialize" constr(H) "at" integer(i) "as" ident(idH) ":" ident(idprem) := proveprem_as_prem H i idprem idH.
Tactic Notation "especialize" constr(H) "as" ident(idH) "at" integer(i) ":" ident(idprem) := proveprem_as_prem H i idprem idH.

Ltac proveprem_asg_newH H i idpremis :=
  let idnewH := fresh H "_spec" in (* FIXME: if H is not freshable? *)
  proveprem_as_prem H i idpremis idnewH.

Tactic Notation "especialize" constr(H) "at" integer(i) "as" "?" ":" ident(idprem) := proveprem_asg_newH H i idprem.
Tactic Notation "especialize" constr(H) "as" "?" "at" integer(i) ":" ident(idprem) := proveprem_asg_newH H i idprem.


Ltac proveprem_as_premg H i idnewH :=
  let idpremis := fresh H "_prem" in
  proveprem_as_prem H i idpremis idnewH.

Tactic Notation "especialize" constr(H) "at" integer(i) "as" ident(idH) ":" "?" := proveprem_as_premg H i idH.
Tactic Notation "especialize" constr(H) "as" ident(idH) "at" integer(i) ":" "?" := proveprem_as_premg H i idH.

Ltac proveprem_asg_premg H i :=
  let idnewH := fresh H "_spec" in
  let idpremis := fresh H "_prem" in
  proveprem_as_prem H i idpremis idnewH.

Tactic Notation "especialize" constr(H) "at" integer(i) "as" "?" ":" "?" := proveprem_asg_premg H i.
Tactic Notation "especialize" constr(H) "as" "?" "at" integer(i) ":" "?" := proveprem_asg_premg H i.

Ltac proveprem_as H i idnewH :=
  let idpremis := fresh H "_prem" in
  proveprem_as_prem H i idpremis idnewH;[ | clear idpremis].

Tactic Notation "especialize" constr(H) "at" integer(i) "as" ident(idH) := proveprem_as H i idH.
Tactic Notation "especialize" constr(H) "as" ident(idH) "at" integer(i) := proveprem_as H i idH.

Ltac proveprem_asg H i :=
  let idnewH := fresh H "_spec" in
  let idpremis := fresh H "_prem" in
  proveprem_as_prem H i idpremis idnewH;[ | clear idpremis].

Tactic Notation "especialize" constr(H) "at" integer(i) "as" "?" := proveprem_asg H i.
Tactic Notation "especialize" constr(H) "as" "?" "at" integer(i) := proveprem_asg H i.



(* Version where specialize is not given a name (soeither H is a
   hypand it is modified, or the new hyp is generalized). *)

Ltac proveprem_prem H i idpremis :=
  let ev := open_constr:((_:Prop)) in
  assert (idpremis:ev);
  [|specialize H with (i:=idpremis)].

Tactic Notation "especialize" constr(H) "at" integer(i) ":" ident(idprem) := proveprem_prem H i idprem.

Ltac proveprem_premg H i :=
  let idpremis := fresh H "_prem" in
  proveprem_prem H i idpremis.

Tactic Notation "especialize" constr(H) "at" integer(i) ":" "?" := proveprem_premg H i.

(* same as proveprem_prem but discard the created hypothesis once used in specialization *)
Ltac proveprem H i :=
  let idpremis := fresh H "_prem" in
  proveprem_prem H i idpremis ; [ | clear idpremis].

Tactic Notation "especialize" constr(H) "at" integer(i) := proveprem H i.
Tactic Notation "especialize" constr(H) "at" integer(i) := proveprem H i.

(* Create a subgoal for each dependent premiss of H *)
Ltac proveprem_all H := (especialize H at 1; [| proveprem_all H]) + idtac.

Tactic Notation "especialize" constr(H) "at" "*" :=
  ((try (is_var(H); fail 1));
   ((try (freshable H;fail 1));
    (let h := fresh "H_spec" in
     specialize H as h; (* create the hyp *)
     proveprem_all h))
   + (let h := fresh "H_" H "_spec" in
      specialize H as h; (* create the hyp *)
      proveprem_all h))
  + proveprem_all H.

Tactic Notation "especialize" constr(H) "at" "*" "as" ident(idH) :=
    (let h := fresh idH in
     specialize H as h; (* create the hyp *)
     proveprem_all h).

(* Create a subgoal for each dependent premiss of H *)
Ltac proveprem_until H i :=
  match i with
    0 => idtac
  | (S ?i') => (especialize H at 1; [| proveprem_until H i'])
  end.

Tactic Notation "especialize" constr(H) "until" constr(i) :=
  (try (is_var(H); fail 1);
   ((let _ := freshable H in
     let h := fresh "H_" H "_spec" in
     specialize H as h; (* create the hyp *)
     proveprem_until h i)
    + (let h := fresh "H_spec" in
       specialize H as h; (* create the hyp *)
       proveprem_until h i)))
  + proveprem_until H i.

Tactic Notation "especialize" constr(H) "until" constr(i) "as" ident(idH) :=
   (let h := fresh idH in
    specialize H as h; (* create the hyp *)
    proveprem_until h i).

(* Same but discard the created hypothesis once used in specialization *)
Ltac proveprem_as_2 H idnewH i1 i2 :=
  let idprem1 := fresh H "_prem" in (* FIXME when H is not freshable, and in all others. *)
  let idprem2 := fresh H "_prem'" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  assert (idprem1:ev1);
  [ |
    assert (idprem2:ev2);
    [|specialize H with (i1:=idprem1) (i2:=idprem2) as idnewH ; clear idprem2 idprem1]].

Tactic Notation "especialize" constr(H) "as" ident(idH) "at"  integer(i1) "," integer(i2) := proveprem_as_2 H idH i1 i2.
Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2) "as" ident(idH) := proveprem_as_2 H idH i1 i2.

(* Same but discard the created hypothesis once used in specialization *)
Ltac proveprem_2 H i1 i2 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem'" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  assert (idprem1:ev1);
  [ |
    assert (idprem2:ev2);
    [|specialize H with (i1:=idprem1) (i2:=idprem2) ; clear idprem2 idprem1]].

Tactic Notation "especialize" constr(H) "at" integer(i1) "," integer(i2) := proveprem_2 H i1 i2.

Ltac proveprem_as_3 H idnewH i1 i2 i3 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  assert (idprem1:ev1);
  [ | assert (idprem2:ev2);
      [ | assert (idprem3:ev3);
          [ | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) as idnewH ; clear idprem3 idprem2 idprem1 ]]].

Tactic Notation "especialize" constr(H) "as" ident(idH) "at"  integer(i1) "," integer(i2)"," integer(i3) := proveprem_as_3 H idH i1 i2 i3.
Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) "as" ident(idH) := proveprem_as_3 H idH i1 i2 i3.

Ltac proveprem_3 H i1 i2 i3 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  assert (idprem1:ev1);
  [ | assert (idprem2:ev2);
      [ | assert (idprem3:ev3);
          [ | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) ; clear idprem3 idprem2 idprem1 ]]].

Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) := proveprem_3 H i1 i2 i3.

Ltac proveprem_as_4 H idnewH i1 i2 i3 i4 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let idprem4 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  let ev4 := open_constr:((_:Prop)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4);
        [ | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) as idnewH ;
            clear idprem4 idprem3 idprem2 idprem1 ]]]].

Tactic Notation "especialize" constr(H) "as" ident(idH) "at"  integer(i1) "," integer(i2) "," integer(i3) "," integer(i4) := proveprem_as_4 H idH i1 i2 i3 i4.
Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) "," integer(i4) "as" ident(idH) := proveprem_as_4 H idH i1 i2 i3 i4.

Ltac proveprem_4 H i1 i2 i3 i4 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let idprem4 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  let ev4 := open_constr:((_:Prop)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4);
        [ | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) ;
            clear idprem4 idprem3 idprem2 idprem1 ]]]].

Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) "," integer(i4) := proveprem_4 H i1 i2 i3 i4.


Ltac proveprem_as_5 H idnewH i1 i2 i3 i4 i5 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let idprem4 := fresh H "_prem" in
  let idprem5 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  let ev4 := open_constr:((_:Prop)) in
  let ev5 := open_constr:((_:Prop)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) as idnewH ;
            clear idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]].

Tactic Notation "especialize" constr(H) "as" ident(idH) "at"  integer(i1) "," integer(i2) "," integer(i3) "," integer(i4) "," integer(i5) := proveprem_as_5 H idH i1 i2 i3 i4 i5.
Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) "," integer(i4) "," integer(i5) "as" ident(idH) := proveprem_as_5 H idH i1 i2 i3 i4 i5.

Ltac proveprem_5 H i1 i2 i3 i4 i5 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let idprem4 := fresh H "_prem" in
  let idprem5 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  let ev4 := open_constr:((_:Prop)) in
  let ev5 := open_constr:((_:Prop)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5);
            clear idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]].

Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) "," integer(i4) "," integer(i5) := proveprem_5 H i1 i2 i3 i4 i5.

Ltac proveprem_as_6 H idnewH i1 i2 i3 i4 i5 i6 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let idprem4 := fresh H "_prem" in
  let idprem5 := fresh H "_prem" in
  let idprem6 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  let ev4 := open_constr:((_:Prop)) in
  let ev5 := open_constr:((_:Prop)) in
  let ev6 := open_constr:((_:Prop)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | assert (idprem6:ev6); [
            | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) (i6:=idprem6) as idnewH ;
              clear idprem6 idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]]].

Tactic Notation "especialize" constr(H) "as" ident(idH) "at"  integer(i1) "," integer(i2) "," integer(i3) "," integer(i4) "," integer(i5) "," integer(i6) := proveprem_as_6 H idH i1 i2 i3 i4 i5 i6.
Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) "," integer(i4) "," integer(i5) "," integer(i6) "as" ident(idH) := proveprem_as_6 H idH i1 i2 i3 i4 i5 i6.

Ltac proveprem_6 H i1 i2 i3 i4 i5 i6 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let idprem4 := fresh H "_prem" in
  let idprem5 := fresh H "_prem" in
  let idprem6 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  let ev4 := open_constr:((_:Prop)) in
  let ev5 := open_constr:((_:Prop)) in
  let ev6 := open_constr:((_:Prop)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | assert (idprem6:ev6); [
          | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) (i6:=idprem6);
            clear idprem6 idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]]].

Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) "," integer(i4) "," integer(i5) "," integer(i6) := proveprem_6 H i1 i2 i3 i4 i5 i6.

Ltac proveprem_as_7 H idnewH i1 i2 i3 i4 i5 i6 i7 :=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let idprem4 := fresh H "_prem" in
  let idprem5 := fresh H "_prem" in
  let idprem6 := fresh H "_prem" in
  let idprem7 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  let ev4 := open_constr:((_:Prop)) in
  let ev5 := open_constr:((_:Prop)) in
  let ev6 := open_constr:((_:Prop)) in
  let ev7 := open_constr:((_:Prop)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | assert (idprem6:ev6); [
            | assert (idprem7:ev7); [
              | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) (i6:=idprem6) (i7:=idprem7) as idnewH ;
                clear idprem7 idprem6 idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]]]].

Tactic Notation "especialize" constr(H) "as" ident(idH) "at"  integer(i1) "," integer(i2) "," integer(i3) "," integer(i4) "," integer(i5) "," integer(i6) "," integer(i7) := proveprem_as_7 H idH i1 i2 i3 i4 i5 i6 i7.
Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) "," integer(i4) "," integer(i5) "," integer(i6) "," integer(i7) "as" ident(idH) := proveprem_as_7 H idH i1 i2 i3 i4 i5 i6 i7.

Ltac proveprem_7 H i1 i2 i3 i4 i5 i6 i7:=
  let idprem1 := fresh H "_prem" in
  let idprem2 := fresh H "_prem" in
  let idprem3 := fresh H "_prem" in
  let idprem4 := fresh H "_prem" in
  let idprem5 := fresh H "_prem" in
  let idprem6 := fresh H "_prem" in
  let idprem7 := fresh H "_prem" in
  let ev1 := open_constr:((_:Prop)) in
  let ev2 := open_constr:((_:Prop)) in
  let ev3 := open_constr:((_:Prop)) in
  let ev4 := open_constr:((_:Prop)) in
  let ev5 := open_constr:((_:Prop)) in
  let ev6 := open_constr:((_:Prop)) in
  let ev7 := open_constr:((_:Prop)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | assert (idprem6:ev6); [
            | assert (idprem7:ev7); [
              | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) (i6:=idprem6) (i7:=idprem7);
                clear idprem7 idprem6 idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]]]].

Tactic Notation "especialize" constr(H) "at"  integer(i1) "," integer(i2)"," integer(i3) "," integer(i4) "," integer(i5) "," integer(i6) "," integer(i7) := proveprem_7 H i1 i2 i3 i4 i5 i6 i7.



(*
Definition eq_one (i:nat) := i = 1.

Lemma test_esepec_6_7: (eq_one 2 -> eq_one 3 ->eq_one 4 ->eq_one 5 ->eq_one 6 ->eq_one 7 ->eq_one 8 -> eq_one 9 -> eq_one 1 -> False) -> True.
Proof.
  intros H.
  especialize H at 3,1,4,5,2,7 as h; [ admit | admit | admit  | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> eq_one 1 ->False=> idtac "OK" end].
  Undo.
  especialize H as h at 3,1,4,5,2,7; [ admit | admit | admit  | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> eq_one 1 ->False=> idtac "OK" end].
  Undo.
  especialize H at 3,1,4,5,2,7; [ admit | admit | admit  | admit | admit | admit | match type of H with eq_one 7 -> eq_one 9 -> eq_one 1 ->False=> idtac "OK" end].
  Undo.
  especialize H at 3,1,4,5,2,7,9 as h; [ admit | admit | admit  | admit | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H as h at 3,1,4,5,2,7,9; [ admit | admit | admit  | admit | admit | admit | admit | match type of h with eq_one 7 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  especialize H at 3,1,4,5,2,7,9; [ admit | admit | admit  | admit | admit | admit | admit | match type of H with eq_one 7 -> eq_one 9 -> False => idtac "OK" end].
  Undo.
  exact I.
Qed.






(* TEST *)

Lemma foo: (eq_one 2 -> eq_one 1 -> False) -> False.
Proof.
  intros H.
  especialize (le_sind 0) at 1 as hh : h.
  { admit. }
  especialize min_l at 1 as ? : ?.
  { apply (le_n O). }
  
  especialize H at 1 as hh : h.
  { reflexivity. }
  match type of h with False => idtac "OK" | _ => fail end.
  assumption.
Qed.
*)



