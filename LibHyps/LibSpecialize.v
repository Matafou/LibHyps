(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

(* The especialize tactic allows to create subgoals from premises of a
   hypothesis.

From a hypothesis of the form:

H: forall a b c, A -> B -> C -> X

one can start a goal for either A and/or B and/or C, while making
evars for a and/pr b and/or c. Duplicating H or not.

especialize H with a at 2.

will start a goal GB of type B[a<-?a] and specialize H with ?a and GB.
Changing H into:

H: forall b c, A[a<-?a] -> C[a<-?a} -> X[a<-?a]

Note that B must be proved without without supposing A. This tactic
does not implement the exact logical rule (this is work in progress).
This limitation is however not a problem in practice: if B needs A
then the user almost always wants to prove A first.

The tactic supports sevral evars and/or several sibgoals at once:

especialize H with a,b at 1,2.
etc.

Special "at *" form (inspired by exploit from Compcert=::

especialize H with a,b,c at *.

will start goals for all premises (A, B and C in the example above).

Special "until" form e.g. :

especialize with a,c A until 2.

will start goals for all the 2 first premises  with evars ?a, and ?c. *)


(* proveprem H at i as h. Create an assert for the ith dependent
premiss of hypothesis H and specialize H with the resulting proof. h
is the (optional) name of the asserted premiss. *)

Ltac freshable t :=
  let x := fresh t "_dummy_sufx" in
  idtac.

Ltac fresh_unfail H :=
  match constr:(True) with
    | _ => fresh H "_"
    | _ => fresh "H_"
  end.

Ltac fail_if_not_hyp c :=
  tryif is_var(c) then idtac else fail "especialize: please provide a name for the new hyp (with 'as')".


Ltac proveprem_as_prem H i idpremis idnewH :=
  (* prefer this to evar, which is not well "typed" by Ltac (does not
     know that it creates an evar (coq bug?). *)
  let ev := open_constr:((_)) in
  assert (idpremis:ev);
  [|specialize H with (i:=idpremis) as idnewH].

Tactic Notation "especialize" constr(H) "at" int_or_var(i) "as" ident(idH) ":" ident(idprem) := proveprem_as_prem H i idprem idH.

Ltac proveprem_asg_newH H i idpremis :=
  let prefx := fresh_unfail H in
  let idnewH := fresh prefx "spec" in (* FIXME: if H is not freshable? *)
  proveprem_as_prem H i idpremis idnewH.

Tactic Notation "especialize" constr(H) "at" int_or_var(i) "as" "?" ":" ident(idprem) := proveprem_asg_newH H i idprem.

Ltac proveprem_as_premg H i idnewH :=
  let prefx := fresh_unfail H in
  let idpremis := fresh prefx "prem" in
  proveprem_as_prem H i idpremis idnewH.

Tactic Notation "especialize" constr(H) "at" int_or_var(i) "as" ident(idH) ":" "?" := proveprem_as_premg H i idH.


Ltac proveprem_asg_premg H i :=
  let prefx := fresh_unfail H in
  let idnewH := fresh prefx "spec" in
  let idpremis := fresh prefx "prem" in
  proveprem_as_prem H i idpremis idnewH.

Tactic Notation "especialize" constr(H) "at" int_or_var(i) "as" "?" ":" "?" := proveprem_asg_premg H i.

Ltac proveprem_as H i idnewH :=
  let prefx := fresh_unfail H in
  let idpremis := fresh prefx "prem" in
  proveprem_as_prem H i idpremis idnewH;[ | clear idpremis].

Tactic Notation "especialize" constr(H) "at" int_or_var(i) "as" ident(idH) := proveprem_as H i idH.


Ltac proveprem_asg H i :=
  let prefx := fresh_unfail H in
  let idnewH := fresh prefx "spec" in
  let idpremis := fresh prefx "prem" in
  proveprem_as_prem H i idpremis idnewH;[ | clear idpremis].

Tactic Notation "especialize" constr(H) "at" int_or_var(i) "as" "?" := proveprem_asg H i.


(* Version where specialize is not given a name (soeither H is a
   hypand it is modified, or the new hyp is generalized). *)

Ltac proveprem_prem H i idpremis :=
  let ev := open_constr:((_)) in
  assert (idpremis:ev);
  [|specialize H with (i:=idpremis)].

Tactic Notation "especialize" constr(H) "at" int_or_var(i) ":" ident(idprem) :=
  fail_if_not_hyp H;
  proveprem_prem H i idprem.

Ltac proveprem_premg H i :=
  let prefx := fresh_unfail H in
  let idpremis := fresh prefx "prem" in
  proveprem_prem H i idpremis.

Tactic Notation "especialize" constr(H) "at" int_or_var(i) ":" "?" := proveprem_premg H i.

(* same as proveprem_prem but discard the created hypothesis once used in specialization *)
Ltac proveprem H i :=
  let prefx := fresh_unfail H in
  let idpremis := fresh prefx "prem" in
  proveprem_prem H i idpremis ; [ | clear idpremis].

Tactic Notation "especialize" constr(H) "at" int_or_var(i) := fail_if_not_hyp H;proveprem H i.

(* Create a subgoal for each dependent premiss of H *)
Ltac proveprem_all H := (especialize H at 1; [| proveprem_all H]) + idtac.

(* TODO: make the "as" mandatory if G not a hyp. *)
Tactic Notation "especialize" constr(H) "at" "*" :=
  tryif is_var(H) then proveprem_all H
  else
    let prefx := fresh_unfail H in
    let h := fresh prefx "spec" in
    specialize H as h; (* create the hyp *)
    proveprem_all h.

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

(* TODO idem: make as mandatory *)
Tactic Notation "especialize" constr(H) "until" constr(i) :=
  tryif is_var(H) then proveprem_until H i
  else
    let prefx := fresh_unfail H in
    let h := fresh prefx "spec" in
    specialize H as h; (* create the hyp *)
    proveprem_until h i.

Tactic Notation "especialize" constr(H) "until" constr(i) "as" ident(idH) :=
   (let h := fresh idH in
    specialize H as h; (* create the hyp *)
    proveprem_until h i).

(* Same but discard the created hypothesis once used in specialization *)
Ltac proveprem_as_2 H idnewH i1 i2 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in (* FIXME when H is not freshable, and in all others. *)
  let idprem2 := fresh prefx "_prem'" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  assert (idprem1:ev1);
  [ |
    assert (idprem2:ev2);
    [|specialize H with (i1:=idprem1) (i2:=idprem2) as idnewH ; clear idprem2 idprem1]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2) "as" ident(idH) := proveprem_as_2 H idH i1 i2.

(* Same but discard the created hypothesis once used in specialization *)
Ltac proveprem_2 H i1 i2 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem'" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  assert (idprem1:ev1);
  [ |
    assert (idprem2:ev2);
    [|specialize H with (i1:=idprem1) (i2:=idprem2) ; clear idprem2 idprem1]].

Tactic Notation "especialize" constr(H) "at" int_or_var(i1) "," int_or_var(i2) := proveprem_2 H i1 i2.

Ltac proveprem_as_3 H idnewH i1 i2 i3 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  assert (idprem1:ev1);
  [ | assert (idprem2:ev2);
      [ | assert (idprem3:ev3);
          [ | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) as idnewH ; clear idprem3 idprem2 idprem1 ]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) "as" ident(idH) := proveprem_as_3 H idH i1 i2 i3.

Ltac proveprem_3 H i1 i2 i3 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  assert (idprem1:ev1);
  [ | assert (idprem2:ev2);
      [ | assert (idprem3:ev3);
          [ | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) ; clear idprem3 idprem2 idprem1 ]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) := proveprem_3 H i1 i2 i3.

Ltac proveprem_as_4 H idnewH i1 i2 i3 i4 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let idprem4 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  let ev4 := open_constr:((_)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4);
        [ | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) as idnewH ;
            clear idprem4 idprem3 idprem2 idprem1 ]]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) "," int_or_var(i4) "as" ident(idH) := proveprem_as_4 H idH i1 i2 i3 i4.

Ltac proveprem_4 H i1 i2 i3 i4 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let idprem4 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  let ev4 := open_constr:((_)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4);
        [ | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) ;
            clear idprem4 idprem3 idprem2 idprem1 ]]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) "," int_or_var(i4) := proveprem_4 H i1 i2 i3 i4.


Ltac proveprem_as_5 H idnewH i1 i2 i3 i4 i5 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let idprem4 := fresh prefx "_prem" in
  let idprem5 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  let ev4 := open_constr:((_)) in
  let ev5 := open_constr:((_)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) as idnewH ;
            clear idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" ident(idH) := proveprem_as_5 H idH i1 i2 i3 i4 i5.

Ltac proveprem_5 H i1 i2 i3 i4 i5 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let idprem4 := fresh prefx "_prem" in
  let idprem5 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  let ev4 := open_constr:((_)) in
  let ev5 := open_constr:((_)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5);
            clear idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) := proveprem_5 H i1 i2 i3 i4 i5.

Ltac proveprem_as_6 H idnewH i1 i2 i3 i4 i5 i6 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let idprem4 := fresh prefx "_prem" in
  let idprem5 := fresh prefx "_prem" in
  let idprem6 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  let ev4 := open_constr:((_)) in
  let ev5 := open_constr:((_)) in
  let ev6 := open_constr:((_)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | assert (idprem6:ev6); [
            | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) (i6:=idprem6) as idnewH ;
              clear idprem6 idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" ident(idH) := proveprem_as_6 H idH i1 i2 i3 i4 i5 i6.

Ltac proveprem_6 H i1 i2 i3 i4 i5 i6 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let idprem4 := fresh prefx "_prem" in
  let idprem5 := fresh prefx "_prem" in
  let idprem6 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  let ev4 := open_constr:((_)) in
  let ev5 := open_constr:((_)) in
  let ev6 := open_constr:((_)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | assert (idprem6:ev6); [
          | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) (i6:=idprem6);
            clear idprem6 idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) := proveprem_6 H i1 i2 i3 i4 i5 i6.

Ltac proveprem_as_7 H idnewH i1 i2 i3 i4 i5 i6 i7 :=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let idprem4 := fresh prefx "_prem" in
  let idprem5 := fresh prefx "_prem" in
  let idprem6 := fresh prefx "_prem" in
  let idprem7 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  let ev4 := open_constr:((_)) in
  let ev5 := open_constr:((_)) in
  let ev6 := open_constr:((_)) in
  let ev7 := open_constr:((_)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | assert (idprem6:ev6); [
            | assert (idprem7:ev7); [
              | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) (i6:=idprem6) (i7:=idprem7) as idnewH ;
                clear idprem7 idprem6 idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" ident(idH) := proveprem_as_7 H idH i1 i2 i3 i4 i5 i6 i7.

Ltac proveprem_7 H i1 i2 i3 i4 i5 i6 i7:=
  let prefx := fresh_unfail H in
  let idprem1 := fresh prefx "_prem" in
  let idprem2 := fresh prefx "_prem" in
  let idprem3 := fresh prefx "_prem" in
  let idprem4 := fresh prefx "_prem" in
  let idprem5 := fresh prefx "_prem" in
  let idprem6 := fresh prefx "_prem" in
  let idprem7 := fresh prefx "_prem" in
  let ev1 := open_constr:((_)) in
  let ev2 := open_constr:((_)) in
  let ev3 := open_constr:((_)) in
  let ev4 := open_constr:((_)) in
  let ev5 := open_constr:((_)) in
  let ev6 := open_constr:((_)) in
  let ev7 := open_constr:((_)) in
  assert (idprem1:ev1); [
  | assert (idprem2:ev2); [
    | assert (idprem3:ev3); [
      | assert (idprem4:ev4); [
        | assert (idprem5:ev5); [
          | assert (idprem6:ev6); [
            | assert (idprem7:ev7); [
              | specialize H with (i1:=idprem1) (i2:=idprem2) (i3:=idprem3) (i4:=idprem4) (i5:=idprem5) (i6:=idprem6) (i7:=idprem7);
                clear idprem7 idprem6 idprem5 idprem4 idprem3 idprem2 idprem1 ]]]]]]].

Tactic Notation "especialize" constr(H) "at"  int_or_var(i1) "," int_or_var(i2)"," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) := proveprem_7 H i1 i2 i3 i4 i5 i6 i7.


Tactic Notation "especialize" constr(H) "at" int_or_var(i) "as" "?" :=
  let nme := fresh in
  especialize H at i as nme.

Tactic Notation "especialize" constr(H) "at" int_or_var(i1) "," int_or_var(i2) "as" "?" :=
  let nme := fresh in
  especialize H at i1,i2 as nme.

Tactic Notation "especialize" constr(H) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "as" "?" :=
  let nme := fresh in
  especialize H at i1,i2,i3 as nme.

Tactic Notation "especialize" constr(H) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" "?" :=
  let nme := fresh in
  especialize H at i1,i2,i3,i4 as nme.

Tactic Notation "especialize" constr(H) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" "?" :=
  let nme := fresh in
  especialize H at i1,i2,i3,i4,i5 as nme.

Tactic Notation "especialize" constr(H) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" "?" :=
  let nme := fresh in
  especialize H at i1,i2,i3,i4,i5,i6 as nme.

Tactic Notation "especialize" constr(H) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" "?" :=
  let nme := fresh in
  especialize H at i1,i2,i3,i4,i5,i6,i7 as nme.




(* Adding a phase of evar creation for premises that should be solved
   by side effect of proving others. NOTE that there is no mechanism
   to ensure that these evar are actually solved when subgoals are
   proved. You may want to try "unshelve especialize ..." to have a
   look at created evars.

NOTE: All these tactic notations would be greatly simplified if there
were a way of iterating on a list_int_sep and/or on list_ident_sep and
on the list of "with bindindgs". Probablt Ltac2 would be much better
at this. *)

Ltac spec_evar H id_name :=
  let idt := fresh id_name "T" in
  let id := fresh id_name in
  evar (idt : Type);
  evar (id : idt);
  specialize H with (id_name := id); subst id; subst idt.


Tactic Notation "especialize" constr(H) "with" ident(id) "at" "*" :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H at * .
Tactic Notation "especialize" constr(oldH) "with" ident(id) "at" "*" "as" ident(H) :=
  specialize oldH as H;
  especialize H with id at *.
Tactic Notation "especialize" constr(H) "with" ident(id) "at" "*" "as" "?" :=
  let nme := fresh in
  especialize H with id at * as nme.

Tactic Notation "especialize" constr(H) "with" ident(id) "until" constr(i) :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H until i .
Tactic Notation "especialize" constr(oldH) "with" ident(id) "until" constr(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id until i.
Tactic Notation "especialize" constr(H) "with" ident(id) "until" constr(i) "as" "?" :=
  let nme := fresh in
  especialize H with id until i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i) :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H at i .
Tactic Notation "especialize" constr(oldH) "with" ident(id) "at" int_or_var(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id at i.
Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i) "as" "?" :=
  let nme := fresh in
  especialize H with id at i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i) ":" ident(hprem) :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H at i : hprem.
Tactic Notation "especialize" constr(oldH) "with" ident(id) "at" int_or_var(i) "as" ident(H) ":"  ident(hprem) :=
  specialize oldH as H;
  especialize H with id at i : hprem.
Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i) "as" "?" ":"  ident(hprem) :=
  let nme := fresh in
  especialize H with id at i as nme : hprem.

Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H at i1,i2 .
Tactic Notation "especialize" constr(oldH) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id at i1,i2.
Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "as" "?" :=
  let nme := fresh in
  especialize H with id at i1,i2 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H at i1,i2,i3.
Tactic Notation "especialize" constr(oldH) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id at i1,i2,i3.
Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "as" "?" :=
  let nme := fresh in
  especialize H with id at i1,i2,i3 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H at i1,i2,i3,i4 .
Tactic Notation "especialize" constr(oldH) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id at i1,i2,i3,i4.
Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" "?" :=
  let nme := fresh in
  especialize H with id at i1,i2,i3,i4 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(oldH) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" "?" :=
  let nme := fresh in
  especialize H with id at i1,i2,i3,i4,i5 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H at i1,i2,i3,i4,i5,i6.
Tactic Notation "especialize" constr(oldH) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id at i1,i2,i3,i4,i5,i6.
Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" "?" :=
  let nme := fresh in
  especialize H with id at i1,i2,i3,i4,i5,i6 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) :=
  fail_if_not_hyp H;
  spec_evar H id;
  especialize H at i1,i2,i3,i4,i5,i6,i7.
Tactic Notation "especialize" constr(oldH) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id at i1,i2,i3,i4,i5,i6,i7.
Tactic Notation "especialize" constr(H) "with" ident(id) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" "?" :=
  let nme := fresh in
  especialize H with id at i1,i2,i3,i4,i5,i6,i7 as nme.


Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" "*" :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 at *.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "at" "*" "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2 at *.
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" "*" "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2 at * as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "until" constr(i) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 until i .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "until" constr(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2 until i .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "until" constr(i) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2 until i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 at i .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "at" int_or_var(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2 at i .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2 at i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i) ":" ident(hprem) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 at i : hprem.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "at" int_or_var(i) "as" ident(H) ":" ident(hprem) :=
  specialize oldH as H;
  especialize H with id1,id2 at i : hprem.
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i) "as" "?" ":" ident(hprem) :=
  let nme := fresh in
  especialize H with id1,id2 at i as nme : hprem.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 at i1,i2 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2 at i1,i2 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2 at i1,i2 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 at i1,i2,i3 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2 at i1,i2,i3 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2 at i1,i2,i3 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 at i1,i2,i3,i4 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2 at i1,i2,i3,i4 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2 at i1,i2,i3,i4 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2 at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2 at i1,i2,i3,i4,i5 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 at i1,i2,i3,i4,i5,i6 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2 at i1,i2,i3,i4,i5,i6 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2 at i1,i2,i3,i4,i5,i6 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2 at i1,i2,i3,i4,i5,i6,i7 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2 at i1,i2,i3,i4,i5,i6,i7 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2 at i1,i2,i3,i4,i5,i6,i7 as nme.


Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" "*" :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 at *.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "at" "*" "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 at *.
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" "*" "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3 at * as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "until" constr(i) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 until i .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "until" constr(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 until i .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "until" constr(i) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3 until i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 at i .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 at i .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3 at i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i) ":" ident(hprem) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 at i : hprem.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i) "as" ident(H) ":" ident(hprem) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 at i : hprem.
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i) "as" "?" ":" ident(hprem) :=
  let nme := fresh in
  especialize H with id1,id2,id3 at i as nme : hprem.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 at i1,i2.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 at i1,i2 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3 at i1,i2 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 at i1,i2,i3 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 at i1,i2,i3 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3 at i1,i2,i3 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 at i1,i2,i3,i4 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 at i1,i2,i3,i4 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3 at i1,i2,i3,i4 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3 at i1,i2,i3,i4,i5 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 at i1,i2,i3,i4,i5,i6 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 at i1,i2,i3,i4,i5,i6 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3 at i1,i2,i3,i4,i5,i6 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3 at i1,i2,i3,i4,i5,i6,i7 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3 at i1,i2,i3,i4,i5,i6,i7 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3 at i1,i2,i3,i4,i5,i6,i7 as nme.




Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" "*" :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 at *.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" "*" "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 at *.
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" "*" "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 at * as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "until" constr(i) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 until i .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "until" constr(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 until i .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "until" constr(i) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 until i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 at i .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 at i .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 at i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i) ":" ident(hprem) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 at i : hprem.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i) "as" ident(H) ":" ident(hprem) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 at i : hprem.
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i) "as" "?" ":" ident(hprem) :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 at i as nme : hprem.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 at i1,i2 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 at i1,i2 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 at i1,i2 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 at i1,i2,i3 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 at i1,i2,i3 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 at i1,i2,i3 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 at i1,i2,i3,i4 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 at i1,i2,i3,i4 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 at i1,i2,i3,i4 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 at i1,i2,i3,i4,i5 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 at i1,i2,i3,i4,i5,i6 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 at i1,i2,i3,i4,i5,i6 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 at i1,i2,i3,i4,i5,i6 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4 at i1,i2,i3,i4,i5,i6,i7 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4 at i1,i2,i3,i4,i5,i6,i7 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4 at i1,i2,i3,i4,i5,i6,i7 as nme.




Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" "*" :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at *.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" "*" "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at *.
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" "*" "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at * as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "until" constr(i) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 until i.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "until" constr(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 until i .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "until" constr(i) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 until i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at i .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at i .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at i as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i) ":" ident(hprem) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at i : hprem.
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i) "as" ident(H) ":" ident(hprem) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at i : hprem.
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i) "as" "?" ":" ident(hprem) :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at i as nme : hprem.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at i1,i2 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at i1,i2 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at i1,i2 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at i1,i2 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at i1,i2 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at i1,i2 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at i1,i2,i3 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at i1,i2,i3,i4 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3,i4 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2)  "," int_or_var(i3) "," int_or_var(i4) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3,i4 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3,i4,i5 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3,i4,i5 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at i1,i2,i3,i4,i5,i6 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3,i4,i5,i6 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3,i4,i5,i6 as nme.

Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) :=
  fail_if_not_hyp H;
  spec_evar H id1;
  especialize H with id2,id3,id4,id5 at i1,i2,i3,i4,i5,i6,i7 .
Tactic Notation "especialize" constr(oldH) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" ident(H) :=
  specialize oldH as H;
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3,i4,i5,i6,i7 .
Tactic Notation "especialize" constr(H) "with" ident(id1) "," ident(id2) "," ident(id3) "," ident(id4) "," ident(id5) "at" int_or_var(i1) "," int_or_var(i2) "," int_or_var(i3) "," int_or_var(i4) "," int_or_var(i5) "," int_or_var(i6) "," int_or_var(i7) "as" "?" :=
  let nme := fresh in
  especialize H with id1,id2,id3,id4,id5 at i1,i2,i3,i4,i5,i6,i7 as nme.

