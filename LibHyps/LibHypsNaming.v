(**************************************************************************
* A user-customizable auto-naming scheme for hypothesis in Coq            *
* Author: Pierre Courtieu                                                 *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)
Require Import Arith ZArith List LibHyps.TacNewHyps.
Import ListNotations.
Local Open Scope list.

(** This file is a set of tactical (mainly "!! t" where t is a tactic)
    and tactics (!intros, !destruct etc), that automatically rename
    new hypothesis after applying a tactic. The names chosen for
    hypothesis is programmable using Ltac. See examples in comment
    below.

    Comments welcome. *)

(* Comment this and the Z-dependent lines below if you don't want
   ZArith to be loaded *)
Require Import ZArith.

(** ** The custom renaming tactic
  This tactic should be redefined along a coq development, it should
  return a fresh name build from an hypothesis h and its type th. It
  should fail if no name is found, so that the fallback scheme is
  called.

  Typical use, in increasing order of complexity, approximatively
  equivalent to the decreasing order of interest.

<<
Ltac my_rename_hyp h th :=
  match th with
    | (ind1 _ _ _ _) => fresh "ind1"
    | (ind2 _ _) => fresh "ind2"
    | f1 _ _ = true => fresh "f_eq_true"
    | f1 _ _ = false => fresh "f_eq_false"
    | f1 _ _ = _ => fresh "f_eq"
    | ind3 ?h ?x => fresh "ind3_" h
    | ind3 _ ?x => fresh "ind3" (* if fresh h failed above *)

    (* Sometime we want to look for the name of another hypothesis to
       name h. For example here we want to rename hypothesis h into
       "type_of_foo" if there is some H of type [type_of foo = Some
       h]. *)
    | type => (* See if we find something of which h is the type: *)
              match reverse goal with
              | H: type_of ?x = Some h => fresh "type_of_" x
              end

    | _ => previously_defined_renaming_tac1 th (* cumulative with previously defined renaming tactics *)
    | _ => previously_defined_renaming_tac2 th
  end.

(* Overwrite the definition of rename_hyp using the ::= operator. :*)

Ltac rename_hyp ::= my_rename_hyp.>> *)


(** * Implementation principle:

   The name of the hypothesis will be a sequence of chunks. A chunk is
   a word generally starting with "_".

   Internally this sequence is represented by a list of small terms.
   One term of the form (∀ <chunk>, DUMMY <chunk>) per chunk. For
   instance the sequence "h_eq_foo" is represented by the coq term:

   [ (∀ h:Prop,DUMMY h) (∀ _eq:Prop,DUMMY _eq); (∀ _foo:Prop, DUMMY
   _foo) ]

   where DUMMY is an opaque function (in fact it is the identiy
   function but we don"t care). *)


(** We define DUMMY as an really opaque symbol. *)
Definition DUMMY: Prop -> Prop.
  exact (fun x:Prop => x).
Defined.

(** Builds a chunk from an id (should be given by fresh). *)
Ltac box_name_raw id := constr:(forall id:Prop, DUMMY id).

(** Builds an id from a sequence of chunks. *)
Ltac build_name acc l :=
  let l := eval lazy beta delta [List.app] iota in l in
  match l with
  | nil => acc
  | (forall id1:Prop, DUMMY id1)::?l' =>
    let newacc := fresh acc id1 in
    let res := build_name newacc l' in
    res
  end.

(** A few default chunks *)
Ltac impl_prefix := constr:(forall _impl, DUMMY _impl).
Ltac forall_prefix := constr:(forall _all, DUMMY _all).
Ltac exists_prefix := constr:(forall _ex, DUMMY _ex).
Ltac default_prefix :=constr:(forall h, DUMMY h).

(** * Definition of a naming strategy.

   To compute the name of a hypothesis we look inside its type and
   build a list of chunks. We analyse recursively the type until we
   reach a fixed depth, defined below. This depth determines the
   number of layers we traverse to build the chunk list. *)

Ltac rename_depth := constr:(3).



(** Check if t is an eligible argument for fresh function. For instance
   if t is (forall foo, ...), it is not eligible. *)
Ltac freshable t :=
  let x := fresh t "_dummy_sufx" in
  idtac.

(** Generate fresh name for numerical constants. The Z and N suffixes
   are there to avoid messing with numerical suffixes added by "fresh"
   itself. *)
Ltac numerical_names t :=
  match t with
  | 0%Z => fresh "_0Z"
  | 1%Z => fresh "_1Z"
  | 2%Z => fresh "_2Z"
  | 3%Z => fresh "_3Z"
  | 4%Z => fresh "_4Z"
  | 5%Z => fresh "_5Z"
  | 6%Z => fresh "_6Z"
  | 7%Z => fresh "_7Z"
  | 8%Z => fresh "_8Z"
  | 9%Z => fresh "_9Z"
  | 10%Z => fresh "_10"
  (* | Z0 => fresh "_0" *)
  | O%nat => fresh "_0N"
  | 1%nat => fresh "_1N"
  | 2%nat => fresh "_2N"
  | 3%nat => fresh "_3N"
  | 4%nat => fresh "_4N"
  | 5%nat => fresh "_5N"
  | 6%nat => fresh "_6N"
  | 7%nat => fresh "_7N"
  | 8%nat => fresh "_8N"
  | 9%nat => fresh "_9N"
  | 10%nat => fresh "_10N"
  end.

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


(** This is the customizable naming tactic, by default it fails, giving
   control to default naming tactics. *)
Ltac rename_hyp stop th := fail.

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

(* go under binder and rebuild a term with a good name inside,
   catchable by a match context. *)
with build_dummy_quantified stop th :=
      lazymatch th with
      | forall z:?A , ?B =>
        constr:(
          fun z:A =>
            ltac:(
              let th' := constr:((fun z => B) z) in
              let th' := eval lazy beta in th' in
                  let res := build_dummy_quantified stop th' in
                  exact res))
      | ex ?f =>
        match f with
        | (fun z:?A => ?B) =>
          constr:(
            fun z:A =>
              ltac:(
                let th' := constr:((fun z => B) z) in
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

(** Notation to build a singleton chunk list *)
Notation "'`' id '`'" := (@cons Prop (forall id, DUMMY id) nil) (at level 1,id ident,only parsing): autonaming_scope.

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
      | ?x <> ?y => name (`_neq` ++ x#n ++ y#n)
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
      | _ => fail
      end in
  res.
Local Close Scope autonaming_scope.

(* ENtry point of the renaming code. *)
Ltac fallback_rename_hyp_name th :=
  let depth := rename_depth in
  let l := fallback_rename_hyp depth th in
  let prfx := default_prefix in
  match prfx with
  | context [forall z:Prop, DUMMY z] =>
    build_name z l
  end.

(* Tactic renaming hypothesis H. *)
Ltac autorename H :=
  match type of H with
  | ?th =>
    match type of th with
    | Prop => 
      let dummy_name := fresh "dummy" in
      rename H into dummy_name; (* this renaming makes the renaming more or less
                                   idempotent, it is backtracked if the
                                   rename_hyp below fails. *)
      let newname := fallback_rename_hyp_name th in
      rename dummy_name into newname
    end
  | _ => idtac (* not in Prop or "no renaming pattern for " H *)
  end.

(* Tactical to rename all new hypothesis. A hypothesis is new if its
   name was not present in previous goal. *)
Ltac rename_new_hyps tac := tac_new_hyps tac autorename.

(* The default behaviour is to generalize hypothesis that we failed to
   rename, so that no automatic names are introduced by mistake. Of
   course one can do "intros" to reintroduce them.

   Revert needs to be done in the other direction (so better do ";;
   autorename ;!; revertHyp"), and may fail if something depends on
   the reverted hyp. So we should revert everything depending on the
   unrenamed hyp. *)
Ltac revert_if_norename H :=
  let t := type of H in
  match type of t with
  | Prop => match goal with
            | _ =>  let x := fallback_rename_hyp_name t in idtac
            (* since we are only in prop it is almost never the case
               that something depends on H but if this happens we revert
               everything that does. *)
            | _ => try revert dependent H
            end
  | _ => idtac
  end.


(* EXAMPLE *)
(*
Local Open Scope autonaming_scope.
Ltac rename_hyp_trueeqfalse n th :=
  let res := 
      match th with
      | (@eq _ true false) => name (`_TRUEEQFALSE`)
      end in
  res.

Ltac rename_hyp ::= rename_hyp_trueeqfalse.
Local Close Scope autonaming_scope.

Lemma dummy: forall x y,
    (forall nat : Type, (nat -> nat -> Prop) -> list nat -> Prop) ->
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
     (exists w:nat , w = w -> ~(true=(andb false true)) /\ False) ->
     (exists w:nat , w = w -> True /\ False) ->
     (forall w w':nat , w = w' -> true=false) -> 
     (forall w:nat , w = w -> true=false) -> 
     (forall w:nat, (Nat.eqb w w)=false) -> 
     (forall w w':nat , w = w' -> Nat.eqb 3 4=Nat.eqb 4 3) -> 
    List.length (cons 3 nil) = (fun x => 0)1 ->
    List.length (cons 3 nil) = x ->
    List.nth_error (cons 3 nil) x = Some 3 -> 
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
  Debug Off.
  (* Ltac rename_depth ::= constr:(4). *)


  Ltac rename_depth ::= constr:(3).
  onAllHyps autorename.
  Debug On.
  autorename H14.
  autorename H1.
  
  Debug Off.
  let fr := fresh h_le_0_1 in
  idtac fr.

  let th := type of H1 in
  let newname := fallback_rename_hyp_name th in
  idtac newname.
(*  let th := type of H2 in
  match th with
  | (@eq _ ?a ?b) => let res := constr:( {* x *}) in idtac res
  end.*)



  onAllHyps autorename.
  let th10 := type of H2 in
  let newname := fallback_rename_hyp_name th10 in
  idtac newname.
  let x := fallback_rename_hyp false th10 in
  idtac x.
*)
(* ***************************************************** *)



