(**************************************************************************
* A user-customizable auto-naming scheme for hypothesis in Coq            *
* Author: Pierre Courtieu                                                 *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)
Require Import Arith ZArith LibHyps.TacNewHyps.
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


(* In principle hypothesis are named as "h" followed by "_" separated
parts built by looking at there type. we only look at the immediate
subterms execept is some cases. In this case the generated name would
be too long if we add a part at each recursive level. So when we
detect something that will be recursive (for instance a forall) we add
a single prefix. *)
Inductive HypPrefixes :=
  | HypDefault
  | HypImpl
  | HypForall.

Ltac detect_prefix h th :=
  match th with
  | ?A -> ?B => HypImpl
  | forall z:?A , ?B => HypForall
  | _ => HypDefault
  end.


(* Add prefix except if not a Prop or if prefixable says otherwise.
   Only for forall and impl currently.  *)
Ltac initial_prefix h th :=
  match detect_prefix h th with
  | HypImpl => fresh "h_impl"
  | HypForall => fresh "h_forall"
  | _ => fresh "h"
  end.

Ltac rename_hyp h th := match th with
                        | _ => fail
                        end.

(* for hypothesis on numerical constants *)
Ltac numerical_names prefx t :=
  match t with
  | Z0 => fresh prefx "_0"
  | 0%Z => fresh prefx "_0"
  | (Zpos xH)%Z => fresh prefx "_1"
  | 2%Z => fresh prefx "_2"
  | 3%Z => fresh prefx "_3"
  | 4%Z => fresh prefx "_4"
  | 5%Z => fresh prefx "_5"
  | 6%Z => fresh prefx "_6"
  | 7%Z => fresh prefx "_7"
  | 8%Z => fresh prefx "_8"
  | 9%Z => fresh prefx "_9"
  | 10%Z => fresh prefx "_10"
  | O%nat => fresh prefx "_0"
  | 1%nat => fresh prefx "_1"
  | 2%nat => fresh prefx "_2"
  | 3%nat => fresh prefx "_3"
  | 4%nat => fresh prefx "_4"
  | 5%nat => fresh prefx "_5"
  | 6%nat => fresh prefx "_6"
  | 7%nat => fresh prefx "_7"
  | 8%nat => fresh prefx "_8"
  | 9%nat => fresh prefx "_9"
  | 10%nat => fresh prefx "_10"
  end.

(* fresh with a prefx and that never fails, return
   the prefix itself if the fresh fails *)
Ltac fresh_ prfx x :=
  match x with
  | _ => numerical_names prfx x
  | _ => fresh prfx "_" x
  | _ => prfx
  end.

Ltac fresh_2 prfx x y :=
  let id := fresh_ prfx x in
  fresh_ id y.

Ltac fresh_3 prfx x y z :=
  let id := fresh_ prfx x in
  fresh_2 id y z.

Ltac fresh_4 prfx x y z t :=
  let id := fresh_ prfx x in
  fresh_3 id y z t.

Ltac rename_happ prefx th :=
  match th with
  | _ => numerical_names prefx th
  | ?f _ _ _ _ ?x ?y ?z => fresh_4 prefx f x y z
  | ?f _ _ _ ?x ?y ?z => fresh_4 prefx f x y z
  | ?f _ _ ?x ?y ?z => fresh_4 prefx f x y z
  | ?f _ ?x ?y ?z => fresh_4 prefx f x y z
  | ?f ?x ?y ?z => fresh_4 prefx f x y z
  | ?f ?x ?y => fresh_3 prefx f x y
  | ?f ?x => fresh_2 prefx f x
  | ?f => fresh_ prefx f
  end.

Ltac rename_hhead prefx th :=
  match th with
  | _ => numerical_names prefx th
  | ?f _ _ _ _ _ _ _ => fresh_ prefx f
  | ?f _ _ _ _ _ _ => fresh_ prefx f
  | ?f _ _ _ _ _ => fresh_ prefx f
  | ?f _ _ _ _ => fresh_ prefx f
  | ?f _ _ _ => fresh_ prefx f
  | ?f _ _ => fresh_ prefx f
  | ?f _ => fresh_ prefx f
  | ?f => fresh_ prefx f
  end.

Ltac rename_happ_only_prop prefx th :=
  match type of th with
  | Prop => rename_happ prefx th
  end.


Ltac rename_default prefx h th :=
  match th with
  | ?t = ?u =>
    let hl := rename_hhead eq t in
    let hlr := rename_hhead hl u in
    fresh prefx "_" hlr
  | ~ ?t = ?u =>
    let hl := rename_hhead eq t in
    let hlr := rename_hhead hl u in
    fresh prefx "_n" hlr
  | ~ ?t =>
    let newprefx := fresh prefx "_not" in
    fallback_rename_hyp newprefx h t
  end

(* go under binder and rebuild a term with a good name inside,
   catchable by a match context. *)
with build_dummy_quantified prfx h th :=
  match th with
  | forall z:?A , ?B =>
    constr:(
      forall z:A,
        let h' := (h z) in
        ltac:(
          let th' := type of h' in
          let res := build_dummy_quantified prfx h' th' in
          exact res))
  | _ =>
    let nme := fallback_rename_hyp prfx h th in
    let frshnme := fresh nme in
    (* Build something catchable with mathc context *)
    constr:(forall frshnme:Prop, DUMMY frshnme)
  end

(** ** Calls the (user-defined) rename_hyp + and fallbacks to some default namings if needed.
    [h] is the hypothesis (ident) to rename, [th] is its type. *)
with fallback_rename_hyp prfx h th :=
  match th with
    | _ =>
      (* The renaming tactic we expose to the user does not deal with
         prefix, so we add it afterwards. *)
      let sufx := rename_hyp h th in
      fresh prfx "_" sufx
    | _ => rename_default prfx h th
    | forall _ , _ =>
      let dummyH := build_dummy_quantified prfx h th in
      match dummyH with
      | context [forall z:Prop, DUMMY z] =>
         fresh z
      end
    | _ => rename_happ_only_prop prfx th
  end.


Ltac fallback_rename_hyp_prefx h th :=
    (* initial prefix, we must put something already so that the future
     calls to fresh do not collide with existing constants. *)
    let initial_prfx := initial_prefix h th in
    let res := fallback_rename_hyp initial_prfx h th in
    res.


Ltac autorename H :=
  match type of H with
  | ?th =>
    match type of th with
    | Prop => 
      let dummy_name := fresh "dummy" in
      rename H into dummy_name; (* this renaming makes the renaming more or less
                                   idempotent, it is backtracked if the
                                   rename_hyp below fails. *)
      let newname := fallback_rename_hyp_prefx dummy_name th in
      rename dummy_name into newname
    end
  | _ => idtac (* not in Prop or "no renaming pattern for " H *)
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



