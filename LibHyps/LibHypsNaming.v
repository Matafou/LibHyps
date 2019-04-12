(**************************************************************************
* A user-customizable auto-naming scheme for hypothesis in Coq            *
* Author: Pierre Courtieu                                                 *
* Distributed under the terms of the LGPL-v3 license                      *
***************************************************************************)
Require Import Arith ZArith List LibHyps.TacNewHyps.
Import ListNotations.
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
(* Definition h_:=Type. *)
Definition heq_:=Type.
Definition noname:=Type.
Definition DUMMY := fun x:Prop => x.

Local Open Scope list.


Ltac freshable t :=
  let x := fresh t "_dummy_sufx" in
  idtac.

(* for hypothesis on numerical constants *)
Ltac numerical_names t :=
  match t with
  | 0%Z => fresh "_0"
  | (Zpos xH) => fresh "_1"
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
  end.

Ltac box_name_raw id := constr:(forall id:Prop, DUMMY id).
Ltac box_name id :=  
  let id_ :=
      match id with
      | _ => numerical_names id
      | _ =>
        let _ := freshable id in
        fresh "_" id
      end
  in constr:(forall id_:Prop, DUMMY id_).

Ltac build_name acc l :=
  let l := eval lazy beta delta [List.app] iota in l in
  match l with
  | nil => acc
  | (forall id1:Prop, DUMMY id1)::?l' =>
    let newacc := fresh acc id1 in
    let res := build_name newacc l' in
    res
  end.


Ltac impl_prefix := constr:(forall _impl, DUMMY _impl).
Ltac forall_prefix := constr:(forall _forall, DUMMY _forall).
Ltac exists_prefix := constr:(forall _exist, DUMMY _exist).
Ltac default_prefix :=constr:(forall h, DUMMY h).
Ltac eq_prefix :=constr:(forall eq, DUMMY eq).
Ltac neq_prefix :=constr:(forall neq, DUMMY neq).

Ltac detect_prefix th :=
  match th with
  | ?A -> ?B => impl_prefix
  | forall z:?A , ?B => forall_prefix
  | exists z:?A , ?B => exists_prefix
  | _ => default_prefix
  end.

(* This is the customizable naming tactic, by default it fails, giving
   control to default naming tactics. *)
Ltac rename_hyp th := fail.


Ltac rename_hyp_default stop th :=
  fail.

Ltac decr n :=
  match n with
  | S ?n' => n'
  | 0 => 0
  end.

Ltac nextlevel n t :=
  let tt := type of t in
  match tt with
  | Prop => n
  | _ => decr n
  end.


(* Default naming of an application: we name the function if possible
   or fail, then we add all parameters that can be named either
   recursively or simply.
   TODO: remove implicits? Don't know how to do that. *)
Ltac rename_app stop acc th :=
  match th with
  | ?f => let f'' := box_name f in
          constr:(f''::acc)
  | (?f ?x) =>
    let newstop := nextlevel stop x in
    let namex := match true with
                 | _ => fallback_rename_hyp newstop x
                 | _ => constr:(@nil Prop)
                 end in
    let newacc := constr:(namex ++ acc) in
    rename_app stop newacc f
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
  | _ =>
    let newstop := decr stop in
    fallback_rename_hyp newstop th
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
    let sufx :=
        match sufx_buried with
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
        | 0 => constr:(cons ltac:(box_name th) nil)
        | 0 => constr:(@nil Prop)
        | S ?n =>
          match th with
          | _ => fallback_rename_hyp_specials stop th
          | _ => fallback_rename_hyp_quantif stop th
          | _ =>
            let newstop := nextlevel stop th in
            rename_app newstop (@nil Prop) th
          end
        end.


(* create a simple part of a name from id, returns a list of constr *)
Notation "'`' id '`'" := (@cons Prop (forall id, DUMMY id) nil) (at level 1,id ident,only parsing): autonaming_scope.

(* create a complex part of name from term X, returns a list of constr *)
Notation " X '#' n " := ltac:(
                          let c := fallback_rename_hyp n X in exact c)
                            (at level 1,X constr, only parsing): autonaming_scope.

(* create a less complex part of name from term X, returns a list of constr *)
Notation "'$' X " := ltac:(
                       let c := fallback_rename_hyp 1 X in exact c)
                            (at level 1,X constr, only parsing): autonaming_scope.

Ltac name c := (constr:(c)).

Local Open Scope autonaming_scope.

(* Redefining rename_hyp_default now that we have these usefull notations. *)
Ltac rename_hyp_default n th ::=
  let res := 
      match th with
      | (@eq _ ?x ?y) => name (`_EQ` ++ x#n ++ y#n)
      | ?x <> ?y => name (`_neq` ++ x#n ++ y#n)
      | @cons _ ?x ?l => name (`_cons` ++ x#(S n) ++ l#0%nat)
      | _ => fail
      end in
  res.

(* Default naming scheme, which can be extended by redefining
   rename_hyp with a customized tactic, which can also call
   rename_hyp_default. *)
Ltac rename_hyp ::= rename_hyp_default.

Local Close Scope autonaming_scope.

Ltac fallback_rename_hyp_name th :=
  let l := fallback_rename_hyp 2 th in
  let prfx := default_prefix in
  match prfx with
  | context [forall z:Prop, DUMMY z] =>
    build_name z l
  end.

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
  
Ltac rename_new_hyps tac := tac_new_hyps tac autorename.

(* Need a way to rename or revert but revert needs to be done in the
   other direction (so better do ";; autorename ;!; revertHyp"), and
   may fail if something depends on the reverted hyp. So we should
   revert everything depending on the unrenamed hyp. *)
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

Local Open Scope autonaming_scope.
Ltac rename_hyp_trueeqfalse th :=
  let res := 
      match th with
      (*| (@eq _ (@true) (@false)) => name (`_TRUEEQFALSE`)*)
      (* | (@eq _ ?x ?y) => name (`_eq` ++ $x ++ $y) *)
      (* | ?x <> ?y => name (`_neq` ++ $x ++ $y) *)
      (* | _ => rename_hyp_default th *)
        | _ => fail
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
  let th := constr:(1%Z) in
  
  match th with
  | ?f =>
    let f' := numerical_names f in
    let f'' := box_name_raw f' in
    let c := constr:(f'') in
    idtac c
  end.

  onAllHyps autorename.
  
  Debug Off.

(*
  let th := type of H2 in
  let res :=
      match th with
      | (@eq _ ?x ?y) => let a := constr:(+{_eq}) in a
      end in
  let h_ := fresh "h" in
  (* let nme := build_name h_ res in *)
  idtac res*)


  let th := type of H2 in
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



