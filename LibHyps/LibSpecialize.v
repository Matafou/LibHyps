
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

Tactic Notation "especialize" hyp(H) "at" integer(i) ":" ident(idprem) "as" ident(idH)  :=
  proveprem_named_ H i idprem idH.

Tactic Notation "especialize" hyp(H) "at" integer(i) "as" ident(idH)  :=
  let idprem := fresh H "_prem" in
  proveprem_named_ H i idprem idH.

Tactic Notation "especialize" hyp(H) "at" integer(i) ":" ident(idprem) :=
  proveprem_ H i idprem.

Tactic Notation "especialize" hyp(H) "at" integer(i) :=
  let idprem := fresh H "_prem" in
  proveprem_ H i idprem.



