(**************************************************************************
* A user-customizable auto-naming scheme for hypothesis in Coq            *
* Author: Pierre Courtieu                                                 *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)
Require Import LibHyps.TacNewHyps.
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
(* Dummy constant *)
Definition h_:=Type.
Definition heq_:=Type.
Definition noname:=Type.
Definition DUMMY := fun x:Prop => x.


(* All hyps are prefixed by "h_" except equalities and non-equalities which
   are prefixed by "heq_" "hneq" respectively. *)
Inductive HypPrefixes :=
  | HypNone
  | HypH_
  | HypH
  | HypEq
  | HypNeq
  | HypNeg
  | HypImpl
  | HypForall.

(* This is doing nothign for now, no satisfying behaviour found yet.*)
(* One should rename this if needed *)
Ltac prefixable_eq_neq h th :=
  match th with
  | eq _ _ => HypEq (* Too complicated *)
  | ~ (eq _ _) => HypNeq
  | ~ _ => HypNeq
  (* | _ => HypH_ not satisfying for now because to much collision with ids*)
  | ?A -> ?B => HypImpl
  | forall z:?A , ?B => HypForall
  | _ => HypNone
  end.

Ltac prefixable h th := prefixable_eq_neq h th.

(* Add prefix except if not a Prop or if prefixable says otherwise. *)
Ltac add_prefix h th nme :=
  match type of th with
  | Prop =>
    match prefixable h th with
    | HypH_ => fresh "h_" nme
    | HypH => fresh "h" nme
    | HypImpl => fresh "h" nme
    | HypForall => fresh "h" nme
    | HypEq => fresh "h" nme
    | HypNeq => fresh "h" nme
    | HypNeg => fresh "h" nme
    | HypNone => nme
    end
  | _ => nme
  end.

Ltac rename_hyp h ht := fail.

Ltac rename_happ id th :=
  match th with
  | ?f => fresh id f
  | ?f ?x => fresh id f "_" x
  | ?f ?x => fresh id f
  | ?f ?x ?y => fresh id f "_" x "_" y
  | ?f ?x ?y => fresh id f "_" x
  | ?f _ _ => fresh id f
  | ?f ?x ?y ?z => fresh id f "_" x "_" y "_" z
  | ?f ?x ?y ?z => fresh id f "_" x "_" y
  | ?f ?x ?y ?z => fresh id f "_" x
  | ?f _ _ _ => fresh id f
  | ?f _ ?x ?y ?z => fresh id f "_" x "_" y "_" z
  | ?f _ ?x ?y ?z => fresh id f "_" x "_" y
  | ?f _ ?x ?y ?z => fresh id f "_" x
  | ?f _ _  _  _  => fresh id f
  | ?f _ _ ?x ?y ?z => fresh id f "_" x "_" y "_" z
  | ?f _ _ ?x ?y ?z => fresh id f "_" x "_" y
  | ?f _ _ ?x ?y ?z => fresh id f "_" x
  | ?f _ _ _  _  _  => fresh id f
  | ?f _ _ _ ?x ?y ?z => fresh id f "_" x "_" y "_" z
  | ?f _ _ _ ?x ?y ?z => fresh id f "_" x "_" y
  | ?f _ _ _ ?x ?y ?z => fresh id f "_" x
  | ?f _ _ _ _  _  _  => fresh id f
  | ?f _ _ _ _ ?x ?y ?z => fresh id f "_" x "_" y "_" z
  | ?f _ _ _ _ ?x ?y ?z => fresh id f "_" x "_" y
  | ?f _ _ _ _ ?x ?y ?z => fresh id f "_" x
  | ?f _ _ _ _ _  _  _  => fresh id f
  end.

Ltac freshable t :=
  let x := fresh t in
  idtac.

Ltac freshable_head t :=
  match t with
  | _ => let x := freshable t in t
  | ?f _ => let x := freshable f in f
  | ?f _ _ => let x := freshable f in f
  | ?f _ _ _ => let x := freshable f in f
  | ?f _ _  _  _  => let x := freshable f in f
  | ?f _ _ _  _  _  => let x := freshable f in f
  | ?f _ _ _ _  _  _  => let x := freshable f in f
  | ?f _ _ _ _ _  _  _  => let x := freshable f in f
  | ?f _ _ _ _ _  _  _ _  => let x := freshable f in f
  | ?f _ _ _ _ _  _  _ _ _  => let x := freshable f in f
  | ?f _ _ _ _ _  _  _ _ _ _  => let x := freshable f in f
  | ?f _ _ _ _ _  _  _ _ _ _ _  => let x := freshable f in f
  | ?f _ _ _ _ _  _  _ _ _ _ _ _  => let x := freshable f in f
  | ?f _ _ _ _ _  _  _ _ _ _ _ _ _  => let x := freshable f in f
  end.

Ltac rename_happ_only_prop id th :=
  match type of th with
  | Prop => rename_happ id th
  end.

Ltac rename_heq h th :=
  match th with
  | ?t = ?u =>
    let a := freshable_head t in
    let b := freshable_head u in
    fresh "eq_" a "_" b
  | ?t = ?u =>
    let a := freshable_head t in
    fresh "eq_" a
  | ?t = ?u =>
    let b := freshable_head u in
    fresh "eq_" b
  | _ = _ => fresh "eq"
  end.


Ltac build_dummy_quantified h th :=
  lazymatch th with
  | forall z:?A , ?B =>        
    constr:(
      forall z:A,
        let h' := (h z) in
        ltac:(
          let th' := type of h' in
          let res := build_dummy_quantified h' th' in
          exact res))
  | _ => 
    (* let nme := fallback_rename_hyp h th in *)
    let nme := fallback_rename_hyp h th in
    let frshnme := fresh nme in
    let _ := idtac "foo" in
    let _ := idtac th in
    constr:(forall frshnme:Prop, DUMMY frshnme)
  end

(** ** Calls the (user-defined) rename_hyp + and fallbacks to some default namings if needed.
    [h] is the hypothesis (ident) to rename, [th] is its type. *)
with fallback_rename_hyp h th :=
  match th with
    | _ => rename_hyp h th
    | _ => rename_heq h th
    | ~ ?th' =>
      let sufx := fallback_rename_hyp h th' in
      fresh "neg_" sufx
    | ~ ?th' => fresh "neg"
    (* Order is important here: *)
    | ?A -> ?B =>
      let dummyH := build_dummy_quantified h th in
      let _ := idtac "foo" in
      let _ := idtac dummyH in
      match dummyH with
      | context [forall z:Prop, DUMMY z] =>
        let _ := idtac "foo" in
        let _ := idtac z in
        fresh z
      end
    | forall _ , _ =>
      let dummyH := build_dummy_quantified h th in
      let _ := idtac "foo" in
      let _ := idtac dummyH in
      match dummyH with
      | context [forall z:Prop, DUMMY z] =>
         let _ := idtac "foo" in
         let _ := idtac z in
         fresh z
      end
(*    | ?A -> ?B =>
      let nme := fallback_rename_hyp h B in
      fresh "impl_" nme
    | forall z , _ => fresh "forall_" z*)
    | _ => rename_happ_only_prop h_ th
  end.
(*
Lemma foo:
  (true=false -> false = true -> false = false -> False) -> 
  (forall w w',w < w' -> ~(true=false)) ->
            False.
Proof.
  Set Printing All.
  intros.
  Debug Off.

  
  let t:= type of H in
  let x := fallback_rename_hyp H t in
  idtac x.
*)

Ltac fallback_rename_hyp_prefx h th :=
  let res := fallback_rename_hyp h th in
  add_prefix h th res.

(* Add this if you want hyps of typr ~ P to be renamed like if of type
   P but prefixed by "neg_" *)
Ltac rename_hyp_neg h th :=
  match th with
  | ~ (_ = _) => fail 1(* h_neq already dealt by fallback *)
  | ~ ?th' =>
    let sufx := fallback_rename_hyp h th' in
    fresh "neg_" sufx
  | ~ ?th' => fresh "neg"
  | _ => fail
  end.

Ltac autorename H :=
  match type of H with
  | ?th =>
    let dummy_name := fresh "dummy" in
    rename H into dummy_name; (* this renaming makes the renaming more or less
                                 idempotent, it is backtracked if the
                                 rename_hyp below fails. *)
    let newname := fallback_rename_hyp_prefx dummy_name th in
    rename dummy_name into newname
  | _ => idtac (* "no renaming pattern for " H *)
  end.
  
Ltac rename_new_hyps tac := tac_new_hyps tac autorename.

(* Need a way to rename or revert but revert needs to be done in the
   other direction (so better do ";; autorename ;!; revertHyp"), and
   may fail if something depends on the reverted hyp. So we should
   revert everything depending on the unrenamed hyp. *)
Ltac revert_if_norename H :=
  let t := type of H in
  match type of t with
  | Prop => match goal with
            | _ =>  let x := fallback_rename_hyp_prefx H t in idtac
            (* since we are only in prop it is almost never the case
               that something depends on H but if this happens we revert
               everything that does. *)
            | _ => try revert dependent H
            end
  | _ => idtac
  end.



