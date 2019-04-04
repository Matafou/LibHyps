
(* proveprem H at i as h. Create an assert for the ith dependent
premiss of hypothesis H and specialize H with the resulting proof. h
is the (optional) name of the asserted premiss. *)

Ltac proveprem_ H i id :=
  (* prefer this to evar, which is not well "typed" by Ltac (does not
  know that it creates an evar (coq bug?). *)
  let ev := open_constr:((_:Prop)) in
  assert (id:ev);
  [|specialize H with (i:=id)].

Tactic Notation "especialize" hyp(H) "at" integer(i) "as" ident(id)  :=
  proveprem_ H i id.

Tactic Notation "especialize" hyp(H) "at" integer(i) :=
  let id := fresh H "_prem" in
  proveprem_ H i id.

