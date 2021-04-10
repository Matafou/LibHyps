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

(**************************************************************************
* A user-customizable auto-naming scheme for hypothesis in Coq            *
* Author: Pierre Courtieu                                                 *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)
Require Import Arith ZArith List LibHyps.TacNewHyps.
Import ListNotations.
Local Open Scope list.

(** This file defines a tactic "autorename h" (and "autorename_strict
    h") that automatically rename hypothesis h followinh a systematic,
    but customizable heuristic.

    Comments welcome. *)

(* Comment this and the Z-dependent lines below if you don't want
   ZArith to be loaded *)
Require Import ZArith.

(** ** The custom renaming tactic

  The tactic "rename_hyp" should be redefined along a coq development,
  it should return a fresh name build from a type th and a depth. It
  should fail if no name is found, so that the fallback scheme is
  called.

  Typical use, in increasing order of complexity, approximatively
  equivalent to the decreasing order of interest.

<<
Ltac rename_hyp1 n th :=
  match th with
  | List.In ?e ?l => name ( `_lst_in` ++ e#n ++ l#O)
  | InA _ ?e ?l => name( `_inA` ++ e#n ++ l#0)
  | @StronglySorted _ ?ord ?l => name ( `_strgSorted` ++ l#(S (S n)))
  | @Forall _ ?P ?x => name (`_lst_forall` ++ P#n ++ x#n)
  | @Forall2 _ _ ?P ?x ?y => name (`_lst_forall2` ++ P#n ++ x#n ++ y#n)
  | NoDupA _ ?l => name (`_NoDupA` ++ l#n)
  | NoDup _ ?l => name (`_NoDup` ++ l#n)
  end.
>>
(* Overwrite the definition of rename_hyp using the ::= operator. :*)

<<
Ltac rename_hyp ::= my_rename_hyp.
>> *)


(** * Implementation principle:

   The name of the hypothesis will be a sequence of chunks. A chunk is
   a word generally starting with "_".

   Internally (not seen by the user) this sequence is represented by a
   list of small terms. One term of the form (∀ <chunk>:Prop, DUMMY
   <chunk>) per chunk. For instance the sequence "h_eq_foo" is
   represented by the following coq term:

   [(∀ h,DUMMY h) ; (∀ _eq,DUMMY _eq) ; (∀ _foo, DUMMY _foo)]

   where DUMMY is an opaque (identity) function but we don't care. *)


(** We define DUMMY as an opaque symbol. *)
Definition DUMMY: Prop -> Prop.
  exact (fun x:Prop => x).
Qed.

(* ********** CUSTOMIZATION ********** *)

(** If this is true, then all hyps names will have a trailing "_". In
    case of names ending with a digit (like in "le_1_2" or "le_x1_x2")
    this additional suffix avoids Coq's fresh name generation to
    *replace* the digit. Although this is esthetically bad, it makes
    things more predictable. You may set this to true for backward
    compatility. *)
Ltac add_suffix := constr:(true).

(* This sets the way numerical constants are displayed, default value
   is set below to numerical_names_nosufx, which will give the same
   name to (O<1)%nat and (O<1)%Z and (O<1)%N, i.e. h_lt_0_1_.

   but you can use this in your development to change it
   h_lt_0n_1n_/h_lt_0z_1z_/h_lt_0N_1N_:
   Ltac numerical_names ::= numerical_names_sufx *)
Ltac numerical_names := fail.

(** This determines the depth of the recursive analysis of a type to
    compute the corresponding hypothesis name. generally 2 or 3 is
    enough. More gives too log names, less may give identical names
    too often. *)
Ltac rename_depth := constr:(3).

(** Default prefix for hypothesis names. *)
Ltac default_prefix :=constr:(forall h, DUMMY h).

(** A few special default chunks, for special cases in the naming heuristic. *)
Ltac impl_prefix := constr:(forall _impl, DUMMY _impl).
Ltac forall_prefix := constr:(forall _all, DUMMY _all).
Ltac exists_prefix := constr:(forall _ex, DUMMY _ex).

(** This is the customizable naming tactic that the user should
    REDEFINE along his development. See above for an example of such
    redefinition. It should always fail when no name suggestion is
    found, to give a chance to the default naming scheme to apply. *)

 Ltac rename_hyp stop th := fail.

(* ************************************** *)

(** Builds an id from a sequence of chunks. fresh is not supposed to
    add suffixes anywhere because all the ids we use start with "_".
    As long as no constant or hyp name start with "_" it is ok. *)
Ltac build_name l :=
  let l := eval lazy beta delta [List.app] iota in l in
  match l with
  | nil => fail
  | (forall id1:Prop, DUMMY id1)::nil =>
    match add_suffix with
    | true => fresh id1 "_"
    | false => fresh id1
    end
  | (forall id1:Prop, DUMMY id1)::?l' =>
    let recres := build_name l' in
    (* id1 starts with "_", so fresh do not add any suffix *)
    let res := fresh id1 recres in
    res
  end.

(** Check if t is an eligible argument for fresh function. For instance
   if t is (forall foo, ...), it is not eligible. *)
Ltac freshable t :=
  let x := fresh t "_dummy_sufx" in
  idtac.

(** Generate fresh name for numerical constants.

   Warning: problem here: hyps names may end with a digit: Coq may
   *replace* the digit in case of name clash. If you are bitten by
   this, you should switch to "Ltac add_suffix ::= constr:(true)." so
   that every hyp name ends with "_", so that coq never mangle with
   the digits *)
Ltac numerical_names_nosufx t :=
  match t with
  | 0%Z => fresh "_0"
  | 1%Z => fresh "_1"
  | 2%Z => fresh "_2"
  | 3%Z => fresh "_3"
  | 4%Z => fresh "_4"
  | 5%Z => fresh "_5"
  | 6%Z => fresh "_6"
  | 7%Z => fresh "_7"
  | 8%Z => fresh "_8"
  | 9%Z => fresh "_9"
  | 10%Z => fresh "_10"
  (* | Z0 => fresh "_0" *)
  | O%nat => fresh "_0"
  | 1%nat => fresh "_1"
  | 2%nat => fresh "_2"
  | 3%nat => fresh "_3"
  | 4%nat => fresh "_4"
  | 5%nat => fresh "_5"
  | 6%nat => fresh "_6"
  | 7%nat => fresh "_7"
  | 8%nat => fresh "_8"
  | 9%nat => fresh "_9"
  | 10%nat => fresh "_10"
  | O%N => fresh "_0"
  | 1%N => fresh "_1"
  | 2%N => fresh "_2"
  | 3%N => fresh "_3"
  | 4%N => fresh "_4"
  | 5%N => fresh "_5"
  | 6%N => fresh "_6"
  | 7%N => fresh "_7"
  | 8%N => fresh "_8"
  | 9%N => fresh "_9"
  | 10%N => fresh "_10"
  end.

Ltac numerical_names_sufx t :=
  match t with
  | 0%Z => fresh "_0z"
  | 1%Z => fresh "_1z"
  | 2%Z => fresh "_2z"
  | 3%Z => fresh "_3z"
  | 4%Z => fresh "_4z"
  | 5%Z => fresh "_5z"
  | 6%Z => fresh "_6z"
  | 7%Z => fresh "_7z"
  | 8%Z => fresh "_8z"
  | 9%Z => fresh "_9z"
  | 10%Z => fresh "_10z"
  (* | Z0 => fresh "_0" *)
  | O%nat => fresh "_0n"
  | 1%nat => fresh "_1n"
  | 2%nat => fresh "_2n"
  | 3%nat => fresh "_3n"
  | 4%nat => fresh "_4n"
  | 5%nat => fresh "_5n"
  | 6%nat => fresh "_6n"
  | 7%nat => fresh "_7n"
  | 8%nat => fresh "_8n"
  | 9%nat => fresh "_9n"
  | 10%nat => fresh "_10n"
  | O%N => fresh "_0N"
  | 1%N => fresh "_1N"
  | 2%N => fresh "_2N"
  | 3%N => fresh "_3N"
  | 4%N => fresh "_4N"
  | 5%N => fresh "_5N"
  | 6%N => fresh "_6N"
  | 7%N => fresh "_7N"
  | 8%N => fresh "_8N"
  | 9%N => fresh "_9N"
  | 10%N => fresh "_10N"
  end.

(* Default value, see above for another possible one.
Ltac numerical_names ::= numerical_names_sufx *)
Ltac numerical_names ::= numerical_names_nosufx.
  

(** Build a chunk from a simple term: either a number or a freshable
   term. *)
Ltac box_name t :=
  let id_ :=
      match t with
      | _ => numerical_names t
      | _ =>
        let _ := freshable t in
        fresh "_" t
      end
  in constr:(forall id_:Prop, DUMMY id_).


(** This will later contain a few default fallback naming strategy. *)
Ltac rename_hyp_default stop th :=
  fail.

Ltac decr n :=
  match n with
  | S ?n' => n'
  | 0 => 0
  end.

(* This computes the way we decrement our depth counter when we go
   inside of t. For now we forget the idea of traversing Prop sorted
   terms indefinitely. It gives too long names. *)
Ltac nextlevel n t :=
  let tt := type of t in
  match tt with
 (* | Prop => n *)
  | _ => decr n
  end.


(* Determines the number of "head" implicit arguments, i.e. implicit
   arguments that are before any explicit one. This shall be ignored
   when naming an application. This is done in very ugly way. Any
   better solution welcome. *)
Ltac count_impl th :=
  lazymatch th with
  | (?z ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ _ _ _ _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z _ _ _ _ e f g h i j k) in constr:(7%nat)
    | _ => let foo := constr:(z _ _ _ d e f g h i j k) in constr:(8%nat)
    | _ => let foo := constr:(z _ _ c d e f g h i j k) in constr:(9%nat)
    | _ => let foo := constr:(z _ b c d e f g h i j k) in constr:(10%nat)
    | _ => let foo := constr:(z a b c d e f g h i j k) in constr:(10%nat)
    end
  | (?z ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ _ _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ _ _ _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z _ _ _ e f g h i j k) in constr:(7%nat)
    | _ => let foo := constr:(z _ _ d e f g h i j k) in constr:(8%nat)
    | _ => let foo := constr:(z _ c d e f g h i j k) in constr:(9%nat)
    | _ => let foo := constr:(z b c d e f g h i j k) in constr:(10%nat)
    end
  | (?z ?c ?d ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ _ _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z _ _ e f g h i j k) in constr:(7%nat)
    | _ => let foo := constr:(z _ d e f g h i j k) in constr:(8%nat)
    | _ => let foo := constr:(z c d e f g h i j k) in constr:(9%nat)
    end
  | (?z ?d ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z _ e f g h i j k) in constr:(7%nat)
    | _ => let foo := constr:(z d e f g h i j k) in constr:(8%nat)
    end
  | (?z ?e ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z _ f g h i j k) in constr:(6%nat)
    | _ => let foo := constr:(z e f g h i j k) in constr:(7%nat)
    end
  | (?z ?f ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z _ g h i j k) in constr:(5%nat)
    | _ => let foo := constr:(z f g h i j k) in constr:(6%nat)
    end
  | (?z ?g ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z _ h i j k) in constr:(4%nat)
    | _ => let foo := constr:(z g h i j k) in constr:(5%nat)
    end
  | (?z ?h ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z _ i j k) in constr:(3%nat)
    | _ => let foo := constr:(z h i j k) in constr:(4%nat)
    end
  | (?z ?i ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ _ k) in constr:(1%nat)
    | _ => let foo := constr:(z _ j k) in constr:(2%nat)
    | _ => let foo := constr:(z i j k) in constr:(3%nat)
    end
  | (?z ?j ?k) =>
    match th with
    | _ => let foo := constr:(z _ k) in constr:(1%nat)
    | _ => let foo := constr:(z j k) in constr:(2%nat)
    end
  | (?z ?j) => constr:(1%nat)
  | _ => constr:(0%nat)
  end.


(** Default naming of an application: we name the function if possible
   or fail, then we name all parameters that can be named either
   recursively or simply. Parameters at positions below nonimpl are
   considered implicit and not considered. *)
Ltac rename_app nonimpl stop acc th :=
  match th with
  | ?f => let f'' := box_name f in
          constr:(f''::acc)
  | (?f ?x) =>
    match nonimpl with
    | (S ?nonimpl') =>
      let newstop := nextlevel stop x in
      let namex := match true with
                   | _ => fallback_rename_hyp newstop x
                   | _ => constr:(@nil Prop)
                   end in
      let newacc := constr:(namex ++ acc) in
      rename_app nonimpl' stop newacc f
    | 0%nat => (* don't consider this (implicit) argument *)
      rename_app nonimpl stop acc f
    end
  | _ => constr:(@nil Prop)
  end

(* Go under binder and rebuild a term with a good name inside,
   catchable by a match context. *)
with build_dummy_quantified stop th :=
      lazymatch th with
      | forall __z:?A , ?B =>
        constr:(
          fun __z:A =>
            ltac:(
              let th' := constr:((fun __z => B) __z) in
              let th' := eval lazy beta in th' in
                  let res := build_dummy_quantified stop th' in
                  exact res))
      | ex ?f =>
        match f with
        | (fun __z:?A => ?B) =>
          constr:(
            fun __z:A =>
              ltac:(
                let th' := constr:((fun __z => B) __z) in
                let th' := eval lazy beta in th' in
                    let res := build_dummy_quantified stop th' in
                    exact res))
        end
      | _ => fallback_rename_hyp stop th
      end

(** ** Calls the (user-defined) rename_hyp + and fallbacks to some
    default namings if needed. [h] is the hypothesis (ident) to
    rename, [th] is its type. *)

with fallback_rename_hyp_quantif stop th :=
   let prefx :=
       match th with
       | ?A -> ?B => impl_prefix
       | forall _ , _ => forall_prefix
       | ex (fun _ => _) => exists_prefix
       | _ => fail
       end in
   let newstop := decr stop in
   (* sufx_buried contains a list of dummies *)
   let sufx_buried := build_dummy_quantified newstop th in
   (* FIXME: a bit fragile *)
   let sufx_buried' := eval lazy beta delta [List.app] iota in sufx_buried in
       let sufx :=
           match sufx_buried' with
           | context [ (@cons Prop ?x ?y)] => constr:(x::y)
           end
       in
       constr:(prefx::sufx)

with fallback_rename_hyp_specials stop th :=
     let newstop := decr stop in
     match th with
     (* First see if user has something that applies *)
     | _ => rename_hyp newstop th
     (* if it fails try default specials *)
     | _ => rename_hyp_default newstop th
     end

with fallback_rename_hyp stop th :=
     match stop with
     (*| 0 => constr:(cons ltac:(box_name th) nil)*)
     | 0 => constr:(@nil Prop)
     | S ?n =>
       match th with
       | _ => fallback_rename_hyp_specials stop th
       | _ => fallback_rename_hyp_quantif stop th
       | _ =>
         (*let newstop := nextlevel stop th in*)
         let numnonimpl := count_impl th in
         rename_app numnonimpl stop (@nil Prop) th
       end
     end.

(** * Notation to define specific naming strategy *)
Declare Scope autonaming_scope.
(** Notation to build a singleton chunk list *)

(* from coq-8.13 we should use name instead of ident. But let us wait
   a few versions before this change. *)
Notation "'`' idx '`'" := (@cons Prop (forall idx:Prop, DUMMY idx) (@nil Prop))
                           (at level 1,idx ident,only parsing): autonaming_scope.


(** Notation to call naming on a term X, with a given depth n. *)
Notation " X '#' n " := ltac:(
                          let c := fallback_rename_hyp n X in exact c)
                            (at level 1,X constr, only parsing): autonaming_scope.

(** It is nicer to write name t than constr:t, see below. *)
Ltac name c := (constr:(c)).


(** * Default fallback renaming strategy

  (Re)defining it now that we have everything we need. *)

Local Open Scope autonaming_scope.
Ltac rename_hyp_default n th ::=
  let res :=
      match th with
      (* | (@eq _ ?x ?y) => name (`_eq` ++ x#n ++ y#n) *)
      (* | Z.le ?A ?B => name (`_Zle` ++ A#n ++ B#n) *)
      | ?x <> ?y => name ( `_neq` ++ x#(decr n) ++ y#(decr n))
      | @cons _ ?x (cons ?y ?l) =>
        match n with
        | S ?n' => name (`_cons` ++ x#n ++ y#n ++ l#n')
        | 0 => name (`_cons` ++ x#n)
        end
      | @cons _ ?x ?l =>
        match n with
        | S ?n' => name (`_cons` ++ x#n ++ l#n')
        | 0 => name (`_cons` ++ x#n)
        end
      | (@Some _ ?x) => name (x#n)
      | (@None _) => name (`_None`)
      | _ => fail
      end in
  res.

(* Call this in your own renaming scheme if you want the "hneg" prefix
   on negated properties *)
Ltac rename_hyp_neg n th :=
  match th with
  | ~ (_ = _) => fail 1(* h_neq already dealt by fallback *)
  | ~ ?th' => name (`neq` ++ th'#(S n))
  | _ => fail
  end.

Local Close Scope autonaming_scope.

(* Entry point of the renaming code. *)
Ltac fallback_rename_hyp_name th :=
  let depth := rename_depth in
  let h := constr:(ltac:(let x := default_prefix in exact x)) in
  let l := fallback_rename_hyp depth th in
  match l with
    nil => fail 1
  | _ => let nme := build_name (h::l) in
         fresh nme
  end.

(* Formating Error message *)
Inductive LHMsg t (h:t) := LHMsgC: LHMsg t h.

Notation "h : t" := (LHMsgC t h) (at level 1,only printing, format
"'[ ' h ':' '/' '[' t ']' ']'").

(* Tactic renaming hypothesis H. Ignore Type-sorted hyps, fails if no
renaming can be computed. Example of failing type: H:((fun x => True) true). *)
Ltac autorename_strict H :=
  match type of H with
  | ?th =>
    match type of th with
    | Prop =>
      let dummy_name := fresh "dummy" in
      rename H into dummy_name; (* this renaming makes the renaming
                                   more or less idempotent by freeing
                                   the current name of H, it is
                                   backtracked if the rename_hyp below
                                   fails. *)
      let newname := fallback_rename_hyp_name th in
      rename dummy_name into newname
    | Prop =>
      let c := constr:(LHMsgC th H) in
      fail 1 "no renaming pattern for " c (* "no renaming pattern for " H *)
    | _ => idtac (* not in Prop or "no renaming pattern for " H *)
    end
  end.

(* Tactic renaming hypothesis H. *)
Ltac autorename H := try autorename_strict H.

(*
Print Visibility.
Open Scope autonaming_scope.
Ltac rename_hyp1 n th :=
  match th with
    (* | (?min <= ?x) /\ (?x < ?max) => name (x#n ++ `_bounded_` ++ min#n ++ `_` ++ max#n) *)
  | ((?min <= ?x) /\ (?x <= ?max))%nat => name (x#n ++ `_bounded` ++ min#n ++ max#n)
  | (?x = ?z + ?z)%nat => name (x#n ++ `_bounded` ++ z#n ++ z#n)
  end.
Close Scope autonaming_scope.

Ltac rename_hyp n th ::=
  match th with
  | _ => rename_hyp1 n th
  end.

Goal forall x1 x3:bool, forall a z e : nat,
      z+e = a
      -> forall SEP:(True -> True),
        a = z+z
        -> z+z <= a <= e + e
        -> ((fun f => z = e) true)
        -> forall b1 b2 b3 b4: bool,
          True -> True.
Proof.
  (* Set Ltac Debug. *)
  (* then_nh_rev ltac:(intros) ltac:(subst_or_idtac).   *)
  intros.
  autorename H1.
  Fail autorename_strict H2.

*)
