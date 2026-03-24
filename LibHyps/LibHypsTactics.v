(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

Require Export LibHyps.TacNewHyps.
Require Export LibHyps.LibHypsNaming.
(* Require Export LibHyps.LibSpecialize. *)
Require Import Ltac2.Ltac2.
From Ltac2 Require Import Option Constr Printf.

(* START DEBUG *)
(*
Require Import LibHypsDebug.



 (* example:  *)
Lemma test_espec2: forall x:nat, x = 1 -> (forall a y z:nat, a = 1 -> y = 1 -> z+y+a = 2 -> z+1 = x -> False) -> x > 1.
Proof.
  intros x hx h_eqone.
  (* specevar h_eqone at y. *)
  (pr_goal()).
Abort.

(* END DEBUG *)
*)

(* TODO *)

Ltac2 rec find_above_which (foundone:bool) (t:constr)
  (lH:(ident * constr option * constr) list): ident option :=
  match lH with
  | (id,_,tid)::lH' =>
      if Constr.equal (Constr.type tid) constr:(Prop) then Some id
      else
        if Constr.equal tid t
        then
          match find_above_which true t lH' with
          | Some x => Some x
          | None => Some id
          end
        else if foundone then Some id
             else find_above_which false t lH'
  | [] => None
  end.

Ltac2 rec cut_at (h:ident) (lH:(ident * constr option * constr) list) :=
   match lH with
   | ((id,_,_) as elt)::lH' => if Ident.equal id h then [elt] else elt :: (cut_at h lH')
   | [] => Control.throw (Invalid_argument None) (* Should we fail here? h should always be in lH *)
   end.

Ltac2 move_up_types (h:ident) :=
  let t := Constr.type (Control.hyp h) in
  let tt := Constr.type t in
  if Constr.equal constr:(Prop) tt then ()
  else 
    let l := (Control.hyps()) in
    let l := cut_at h l in
    let aboveh := find_above_which false t l in
    match aboveh with
    | None => ()
    | Some aboveh =>
        if Ident.equal aboveh h then ()
        else Std.move h (Std.MoveAfter aboveh)
    end.

(* Ltac2 move_up (h:constr) := *)
(*   match Constr.Unsafe.kind h with *)
(*   | Constr.Unsafe.Var id => move_up_hyp id *)
(*   | _ => Control.throw (Invalid_argument None) *)
(*   end. *)

Ltac2 ltac1_move_up_types (h:Ltac1.t) :=
  let h: ident := Option.get (Ltac1.to_ident h) in
  move_up_types h.

Local Tactic Notation "Lmove_up_type" hyp(h) :=
  let tac := ltac2:(h |- ltac1_move_up_types h) in
  tac h.

Global Ltac move_up_types h := Lmove_up_type h.


Local Set Default Proof Mode "Classic".
(*
(* Tests *)
Require Import LibHyps.LibHyps.
Export TacNewHyps.Notations.
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
  intros ; {< move_up_types }.
  (* intros ? ? ? ? ? ? ? ? ? ?. *)
  (* group_up_list (DCons bool b1 DNil). *)
  Undo.
  intros ; { move_up_types }.
  Undo.
  intros ; { autorename }; {< move_up_types }.
  Undo.
  intros ; {subst_or_idtac} ; { autorename } ; {< move_up_types }.
  Undo.
  Fail progress intros ; { revertHyp }.
  intros.
  then_eachnh ltac:(intros) ltac:(subst_or_idtac).  
  Undo.
  intros ; { fun h => autorename_strict h }.
  intros ; { fun h => idtac h }.
  intros ; { ltac:(fun h => idtac h) }.
*)

(*

Goal forall x y:nat, x<y -> x+1 <y+1 -> forall z:nat, forall a b : bool, forall n m p : nat,  True.
Proof.
  intros.
  
  progress (move_up_types z).
  Fail progress (move_up_types z).
  Fail progress (move_up_types H).
  Fail progress (move_up_types H0).
  

  let l:(ident * constr option * constr) list := (Control.hyps()) in
  let idopt := find_above_which false constr:(nat) l in
  match idopt with
  | None => printf "None"
  | Some id => printf "res = %I" id
  end.

  Std.move ident:(z) (Std.MoveAfter ident:(H)).

  let l:(ident * constr option * constr) list := (Control.hyps()) in
  let (h,_,_) := find_lowest constr:(nat) l in
  printf "h = %I" h.
*)
