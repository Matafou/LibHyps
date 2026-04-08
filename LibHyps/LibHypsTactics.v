(* Copyright 2021 Pierre Courtieu
  This file is part of LibHyps. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it. *)

Require Import Ltac2.Ltac2.

(* HYPS GROUPING *)

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

Ltac2 ltac1_move_up_types (h:Ltac1.t) :=
  let h: ident := Option.get (Ltac1.to_ident h) in
  move_up_types h.

Local Tactic Notation "Lmove_up_type" hyp(h) :=
  let tac := ltac2:(h |- ltac1_move_up_types h) in
  tac h.

(* GLOBAL TACTICS *)

Global Ltac move_up_types h := Lmove_up_type h.

(* SUBST WITH ONLY ONE HYP *)

(* This is similar to subst x, but ensures that H and only H is used.
   Even if there is another hyp with the same variable *)
Global Ltac substHyp H :=
  match type of H with
  (* | Depl => fail 1 (* fail immediately, we are applying on a list of hyps. *) *)
  | ?x = ?y =>
    (* subst would maybe subst using another hyp, so use replace to be sure *)
    once ((is_var(x); replace x with y in *; [try clear x ; try clear H] )
          + (is_var(y); replace y with x in * ; [try clear y; try clear H]))
  | _ => idtac
  end.

(* DECOMPOSE LOGICAL CONNECTORS *)

Global Ltac decomp_logicals h :=
  idtac;match type of h with
  | @ex _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_logicals h1
  | @sig _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_logicals h1
  | @sig2 _ (fun x => _) (fun _ => _) => let x' := fresh x in
                                         let h1 := fresh in
                                         let h2 := fresh in
                                         destruct h as [x' h1 h2];
                                         decomp_logicals h1;
                                         decomp_logicals h2
  | @sigT _ (fun x => _) => let x' := fresh x in let h1 := fresh in destruct h as [x' h1]; decomp_logicals h1
  | @sigT2 _ (fun x => _) (fun _ => _) => let x' := fresh x in
                                          let h1 := fresh in
                                          let h2 := fresh in
                                          destruct h as [x' h1 h2]; decomp_logicals h1; decomp_logicals h2
  | and _ _ => let h1 := fresh in let h2 := fresh in destruct h as [h1 h2]; decomp_logicals h1; decomp_logicals h2
  | iff _ _ => let h1 := fresh in let h2 := fresh in destruct h as [h1 h2]; decomp_logicals h1; decomp_logicals h2
  | or _ _ => let h' := fresh in destruct h as [h' | h']; [decomp_logicals h' | decomp_logicals h' ]
  | _ => idtac
  end.


