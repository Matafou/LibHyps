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

(* Ltac rename_hyp k h ht := match true with true => fail | _ => let frsh := fresh "hh" in k frsh end. *)
Ltac rename_hyp k h ht := fail.

Ltac rename_happ k id th :=
  let frsh:= 
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
      end in
  k frsh.

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

Ltac rename_happ_only_prop k id th :=
  match type of th with
  | Prop => rename_happ k id th
  end.

Ltac rename_heq k h th :=
  let frsh := 
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
      end in
  k frsh.

(** ** Calls the (user-defined) rename_hyp + and fallbacks to some default namings if needed.
    [h] is the hypothesis (ident) to rename, [th] is its type. *)
Ltac fallback_rename_hyp k h th :=
  match th with
    | _ => rename_hyp k h th
    | _ => rename_heq k h th
    | ~ ?th' =>
      let newk sufx :=
          let frsh := fresh "neg_" sufx in
          k frsh
      in
      fallback_rename_hyp newk h th'
    (* Order is important here: *)
    | ?A -> ?B =>
      let newk sufx :=
          let frsh := fresh "impl_" sufx in
          k frsh
      in
      ltac:(fallback_rename_hyp newk h uconstr:(B))
    | forall z:?A , ?B =>
      let newk sufx :=
          let frsh := fresh "forall_" sufx in
          k frsh
      in
          ltac:(fallback_rename_hyp newk h uconstr:(B))
(*
    | ?A -> ?B =>
      let newk sufx :=
          let frsh := fresh "impl_" sufx in
          k frsh
      in
      constr:(
        fun z:A =>
          let h' := (h z) in
          ltac:(
            let th' := type of h' in
            fallback_rename_hyp newk h' constr:(th'))
      )
    | forall z:?A , ?B =>
      let newk sufx :=
          let frsh := fresh "forall_" sufx in
          k frsh
      in
      constr:(
        fun z:A =>
          let h' := (h z) in
          ltac:(
            let th' := type of h' in
            fallback_rename_hyp newk h' constr:(th'))
      )

*)    | _ => rename_happ_only_prop k h_ th
  end.

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

Ltac fallback_rename_hyp_prefx k h th :=
  let newk sufx :=
      let frsh := add_prefix h th sufx in
      k frsh
  in
  fallback_rename_hyp newk h th.

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
    let dummyterm := fallback_rename_hyp_prefx dummy_name th in
    idtac "renamed"
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


(* TEST *)
Ltac rename_all_hyps :=
  let renam H := autorename H in
  let hyps := all_hyps in
  map_hyps renam hyps.

Lemma foo: forall b, b = true -> (forall w w',w < w' -> ~(true=false)) ->
            False.
Proof.
  intros.
(*  Debug On.*)
  (* fallback_rename_hyp ltac:(fun nme => let nme' := fresh "h_" nme in rename H into nme') H (b = true). *)
(* fallback_rename_hyp *)
  (* ltac:(fun nme => let nme' := fresh "h_" nme in rename H into nme') H (b = true). *)
  Debug Off.
  let typ := type of H0 in
  fallback_rename_hyp
    ltac:(fun nme => let nme' := fresh "h_" nme in rename H0 into nme')
           H0
         typ.


  autorename H.

  rename_all_hyps.



