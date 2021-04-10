(* Copyright 2017-2019 Pierre Courtieu *)
(* This file is part of LibHyps.

    LibHyps is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    LibHyps is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with LibHyps.  If not, see <https://www.gnu.org/licenses/>.
*)

(* proveprem H at i as h. Create an assert for the ith dependent
premiss of hypothesis H and specialize H with the resulting proof. h
is the (optional) name of the asserted premiss. *)

Ltac proveprem_named_ H i idpremis idnewH :=
  (* prefer this to evar, which is not well "typed" by Ltac (does not
  know that it creates an evar (coq bug?). *)
  let ev := open_constr:((_:Prop)) in
  assert (idpremis:ev);
  [|specialize H with (i:=idpremis) as idnewH].

Ltac proveprem_ H i idpremis :=
  (* prefer this to evar, which is not well "typed" by Ltac (does not
  know that it creates an evar (coq bug?). *)
  let ev := open_constr:((_:Prop)) in
  assert (idpremis:ev);
  [|specialize H with (i:=idpremis)].

Tactic Notation "especialize" constr(H) "at" integer(i) ":" ident(idprem) "as" ident(idH)  :=
  proveprem_named_ H i idprem idH.

Tactic Notation "especialize" constr(H) "at" integer(i) "as" ident(idH)  :=
  let idprem := fresh H "_prem" in
  proveprem_named_ H i idprem idH.

Tactic Notation "especialize" constr(H) "at" integer(i) ":" ident(idprem) :=
  proveprem_ H i idprem.

Tactic Notation "especialize" constr(H) "at" integer(i) :=
  let idprem := fresh H "_prem" in
  proveprem_ H i idprem.

(* TEST *)
(*
Definition eq_one (i:nat) := i = 1.
(* eq_one is delta_reducible but I don't want it to be reduced. *)
Lemma foo: (eq_one 1 -> False) -> False.
Proof.
  intros H.
  especialize H at 1 as h.
  { reflexivity. }
  match type of h with False => idtac "OK" | _ => fail end.
  assumption.
Qed.
*)



