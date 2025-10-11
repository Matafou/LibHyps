Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr Printf.

(* debug *)
(*
Require LibHyps.LibHypsTactics.
Module Prgoal_Notation.
  Ltac pr_goal :=
    match goal with
      |- ?g =>
        let allh := LibHyps.TacNewHyps.harvest_hyps LibHyps.TacNewHyps.revert_clearbody_all in
        (* let allh := all_hyps in *)
        idtac "GOAL: " allh " ⊢ " g
    end.
End Prgoal_Notation.
*)

Ltac2 tag_info s := (String.concat "" [ "<infomsg>"; s; "</infomsg>" ]).
Ltac2 tag_msg m := Message.concat
                     (Message.concat (Message.of_string "<infomsg>") m)
                     (Message.of_string "</infomsg>").
Ltac2 str_to_msg s := tag_msg (Message.of_string s).
Ltac2 int_to_msg i := tag_msg (Message.of_int i).
Ltac2 id_to_msg id := tag_msg (Message.of_ident id).
Ltac2 constr_to_msg c := tag_msg (Message.of_constr c).

Ltac2 msgs s := Message.print (str_to_msg s).
Ltac2 msgi i := Message.print (int_to_msg i).
Ltac2 msgc c := Message.print (constr_to_msg c).
Ltac2 msgid id := Message.print (id_to_msg id).


Ltac2 pr_binder () (b:binder) :=
  let nme:ident option := Binder.name b in
  let typ:constr := Binder.type b in
  fprintf "(%I:%t)" (Option.get nme) typ.


Ltac2 pr_goal() :=
  let l := Control.hyps() in
  printf "<infomsg> Goal:";
  List.iter (fun (nme,_,typ) => printf "%I : %t" nme typ) l;
  printf "⊢ %t" (Control.goal());
  printf "</infomsg>".

